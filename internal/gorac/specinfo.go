// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"fmt"
	"github.com/viperproject/gorac/pkg/specparser"
	"go/ast"
	"go/token"
	"go/types"
	"regexp"
)

type InvariantPos int

const (
	Before = iota
	Inside
	After
	NotApplicable
)

// SpecInfo provides an interface for all specification informations. All specification info objects need to provide
// the following functionality:
type SpecInfo interface {
	// A function to return the original specification string as defined by the user in the specification comment
	Original() *string
	// A function to return the position the specification has in the original file
	Pos() token.Pos
	// A function to return the ast node that the specification comment is associated to
	AssociatedNode() *ast.Node
	// A function to return the runtime assertion check for the specification

	String() string
}

// SpecInfo provides an interface for all specification informations. All specification info objects need to provide
// the following functionality:
type RACInfo interface {
	SpecInfo
	// A function to compute the desugared internal representation of the specification
	ComputeDesugaredNode(d *Desugarer)
	// A function to return the internal AST / desugared AST for the specification
	DesugaredNode() Node
	// A function to return the runtime assertion check for the specification
	RAC(rg *RACGenerator, invariantPos InvariantPos) ast.Node
}

// The structs below implement the concrete specification information objects

type AssertInfo struct {
	original       string
	condition      specparser.Node
	pos            token.Pos
	associatedNode ast.Node
	parentFunction *ast.FuncDecl
	desugaredNode  Node

	insertBefore bool
	// Since there is no different for checking assumption or assertions, an AssertInfo object can represent both
	// and only distinguish the two whenever output to the user is provided
	isAssume bool
}

func (a *AssertInfo) Original() *string {
	return &a.original
}

func (a *AssertInfo) Condition() *specparser.Node {
	return &a.condition
}

func (a *AssertInfo) Pos() token.Pos {
	return a.pos
}

func (a *AssertInfo) AssociatedNode() *ast.Node {
	return &a.associatedNode
}

func (a *AssertInfo) DesugaredNode() Node {
	return a.desugaredNode
}

func (a *AssertInfo) ComputeDesugaredNode(d *Desugarer) {
	a.desugaredNode = d.desugar(a.condition, a.associatedNode.Pos(), a.pos)
}

func (a *AssertInfo) ParentFunction() *ast.FuncDecl {
	return a.parentFunction
}

func (a *AssertInfo) RAC(rg *RACGenerator, invariantPos InvariantPos) ast.Node {
	var panicString string
	if a.isAssume {
		panicString = fmt.Sprintf("\"Assumption '%v' violated.\"", a.condition)
	} else {
		panicString = fmt.Sprintf("\"Assertion '%v' violated.\"", a.condition)
	}
	assertion := a.desugaredNode.toRAC().(ast.Expr)
	// Before adding the runtime assertion check to the ast it is type checked
	typeCheckExpr(assertion, a, a.pos, rg.fset, rg.pkg, rg.tokenFile)
	// An assumption is checked as a single if statement that is enabled on the negated condition of the assertion
	rac := ifStmt(nil, nil, unaryExpr(assertion, token.NOT), blockStmt(_panic(basicLit(panicString, token.STRING))))
	return catchPanicWrapper(rac, fmt.Sprintf("Line %d, Specification '%v':", rg.tokenFile.Line(a.pos), a))
}

func (a *AssertInfo) String() string {
	if a.isAssume {
		return "assume " + a.condition.String()
	} else {
		return "assert " + a.condition.String()
	}
}

func (a *AssertInfo) InsertBefore() bool {
	return a.insertBefore
}

func (a *AssertInfo) IsAssume() bool {
	return a.isAssume
}

type PreCondInfo struct {
	original       string
	condition      specparser.Node
	pos            token.Pos
	associatedNode ast.Node
	desugaredNode  Node
}

func (pre *PreCondInfo) Original() *string {
	return &pre.original
}

func (pre *PreCondInfo) Condition() *specparser.Node {
	return &pre.condition
}

func (pre *PreCondInfo) Pos() token.Pos {
	return pre.pos
}

func (pre *PreCondInfo) AssociatedNode() *ast.Node {
	return &pre.associatedNode
}

func (pre *PreCondInfo) DesugaredNode() Node {
	return pre.desugaredNode
}

func (pre *PreCondInfo) ComputeDesugaredNode(d *Desugarer) {
	pre.desugaredNode = d.desugar(pre.condition, pre.associatedNode.(*ast.FuncDecl).Body.Pos(), pre.pos)
}

func (pre *PreCondInfo) RAC(rg *RACGenerator, invariantPos InvariantPos) ast.Node {
	preCond := pre.desugaredNode.toRAC().(ast.Expr)
	typeCheckExpr(preCond, pre, pre.associatedNode.(*ast.FuncDecl).Body.Lbrace, rg.fset, rg.pkg, rg.tokenFile)
	// A precondition is checked as a single if statement that is enabled on the negated condition of the precondition
	// and placed in the beginning of the associated function declaration
	panicString := fmt.Sprintf("\"Precondition '%v' violated.\"", pre.condition)
	rac := ifStmt(nil, nil, unaryExpr(preCond, token.NOT), blockStmt(_panic(basicLit(panicString, token.STRING))))
	return catchPanicWrapper(rac, fmt.Sprintf("Line %d, Specification '%v':", rg.tokenFile.Line(pre.pos), pre))
}

func (pre *PreCondInfo) String() string {
	return "requires " + pre.condition.String()
}

type PostCondInfo struct {
	original       string
	condition      specparser.Node
	pos            token.Pos
	associatedNode ast.Node
	desugaredNode  Node
}

func (post *PostCondInfo) Original() *string {
	return &post.original
}

func (post *PostCondInfo) Condition() *specparser.Node {
	return &post.condition
}

func (post *PostCondInfo) Pos() token.Pos {
	return post.pos
}

func (post *PostCondInfo) AssociatedNode() *ast.Node {
	return &post.associatedNode
}

func (post *PostCondInfo) DesugaredNode() Node {
	return post.desugaredNode
}

func (post *PostCondInfo) ComputeDesugaredNode(d *Desugarer) {
	post.desugaredNode = d.desugar(post.condition, post.associatedNode.(*ast.FuncDecl).Body.Pos(), post.pos)
}

func (post *PostCondInfo) RAC(rg *RACGenerator, invariantPos InvariantPos) ast.Node {
	postCond := post.desugaredNode.toRAC().(ast.Expr)
	typeCheckExpr(postCond, post, post.associatedNode.(*ast.FuncDecl).Body.Rbrace, rg.fset, rg.pkg, rg.tokenFile)
	// A postcondition is checked as a single if statement that is enabled on the negated condition of the postcondition
	// and checked in the end of the associated function declaration, thus, encapsulated by a defer statement
	panicString := fmt.Sprintf("\"Postcondition '%v' violated.\"", post.condition)
	rac := ifStmt(nil, nil, unaryExpr(postCond, token.NOT), blockStmt(_panic(basicLit(panicString, token.STRING))))
	wrapped := catchPanicWrapper(rac, fmt.Sprintf("Line %d, Specification '%v':", rg.tokenFile.Line(post.pos), post))
	return deferStmt(*blockStmt(wrapped))
}

func (post *PostCondInfo) String() string {
	return "ensures " + post.condition.String()
}

type InvariantInfo struct {
	original       string
	condition      specparser.Node
	pos            token.Pos
	associatedNode ast.Node
	parentFunction *ast.FuncDecl
	desugaredNode  Node
}

func (i *InvariantInfo) Original() *string {
	return &i.original
}

func (i *InvariantInfo) Condition() *specparser.Node {
	return &i.condition
}

func (i *InvariantInfo) Pos() token.Pos {
	return i.pos
}

func (i *InvariantInfo) AssociatedNode() *ast.Node {
	return &i.associatedNode
}

func (i *InvariantInfo) DesugaredNode() Node {
	return i.desugaredNode
}

func (i *InvariantInfo) ComputeDesugaredNode(d *Desugarer) {
	switch i.associatedNode.(type) {
	case *ast.ForStmt:
		i.desugaredNode = d.desugar(i.condition, i.associatedNode.(*ast.ForStmt).Body.Pos(), i.pos)
	case *ast.RangeStmt:
		i.desugaredNode = d.desugar(i.condition, i.associatedNode.(*ast.RangeStmt).Body.Pos(), i.pos)
	default:
		panic(fmt.Sprintf("Invariant '%v' at line %d needs to be associated to a loop.",
			i, d.tokenFile.Line(i.pos)))
	}
}

func (i *InvariantInfo) ParentFunction() *ast.FuncDecl {
	return i.parentFunction
}

func (i *InvariantInfo) RAC(rg *RACGenerator, invariantPos InvariantPos) ast.Node {
	var pos token.Pos
	switch i.associatedNode.(type) {
	case *ast.ForStmt:
		pos = i.associatedNode.(*ast.ForStmt).Body.Pos()
	case *ast.RangeStmt:
		pos = i.associatedNode.(*ast.RangeStmt).Body.Pos()
	}
	inv := i.desugaredNode.toRAC().(ast.Expr)
	typeCheckExpr(inv, i, pos, rg.fset, rg.pkg, rg.tokenFile)
	// An invariant is checked as a single if statement that is enabled on the negated condition of the invariant and
	// placed in the beginning of the associated for loop's (or range statement's) body and directly after the loop (or
	// statement). Depending on the position of the check, a different panic-message is shown.
	var panicString string
	switch invariantPos {
	case Before:
		panicString = fmt.Sprintf("\"Invariant '%v' violated before loop execution.\"", i.condition)
	case Inside:
		panicString = fmt.Sprintf("\"Invariant '%v' violated during loop execution.\"", i.condition)
	case After:
		panicString = fmt.Sprintf("\"Invariant '%v' violated after loop execution.\"", i.condition)
	default:
		panic(fmt.Sprintf("Loop invariant '%v' at line %v cannot be converted into runtime check since invalid position was provided.",
			i, rg.tokenFile.Line(i.pos)))
	}
	rac := ifStmt(nil, nil, unaryExpr(inv, token.NOT), blockStmt(_panic(basicLit(panicString, token.STRING))))
	return catchPanicWrapper(rac, fmt.Sprintf("Line %d, Specification '%v':", rg.tokenFile.Line(pos), i))
}

func (i *InvariantInfo) String() string {
	return "invariant " + i.condition.String()
}

type PredicateInfo struct {
	original       string
	pos            token.Pos
	associatedNode ast.Node

	originalName        string
	internalName        string
	originalParameters  [][]specparser.Node // can be empty if no parameters given
	originalAssertion   specparser.Node
	desugaredParameters []Identifier
	desugaredAssertion  Node
	generateRAC         bool
}

func (p *PredicateInfo) Original() *string {
	return &p.original
}

func (p *PredicateInfo) Pos() token.Pos {
	return p.pos
}

func (p *PredicateInfo) AssociatedNode() *ast.Node {
	return &p.associatedNode
}

func (p *PredicateInfo) String() string {
	return fmt.Sprintf("predicate %v(%s) { %v }",
		p.originalName, specparser.StringNodeTuples(p.originalParameters, " "), p.originalAssertion)
}

func (p *PredicateInfo) InternalName() string {
	return p.internalName
}

func (p *PredicateInfo) OriginalName() string {
	return p.originalName
}

func (p *PredicateInfo) DesugaredParameters() []Identifier {
	return p.desugaredParameters
}

func (p *PredicateInfo) OriginalAssertion() specparser.Node {
	return p.originalAssertion
}

func (p *PredicateInfo) OriginalParameters() [][]specparser.Node {
	return p.originalParameters
}

func (p *PredicateInfo) GenerateRAC() bool {
	return p.generateRAC
}

func (p *PredicateInfo) DesugaredNode() Node {
	return p.desugaredAssertion
}

func (p *PredicateInfo) ComputeDesugaredNode(d *Desugarer) {
	if !p.generateRAC {
		p.generateRAC = true
		for _, parameterTuple := range p.originalParameters {
			if identifier, ok := parameterTuple[0].(specparser.Identifier); ok {
				// If the parameter's type is a dereference, it needs to be desugared without the "star" because this
				// does not symbolize a dereference but a pointer type instead.
				var type_ types.Type
				if dereference, ok := parameterTuple[1].(specparser.Dereference); ok {
					desugaredType := d.desugar(dereference.Operand(), p.associatedNode.Pos(), p.pos)
					type_ = types.NewPointer(desugaredType.Type())
				} else {
					type_ = d.desugar(parameterTuple[1], p.associatedNode.Pos(), p.pos).Type()
				}
				variable := Identifier{
					value: identifier.Value(),
					type_: type_,
				}
				p.desugaredParameters = append(p.desugaredParameters, variable)
			} else {
				// Shouldn't happen since specparser would have already thrown an error
				panic(fmt.Sprintf("Parameter declaration of predicate %v at line %d must be tuple of identifier and type, found declaration (%v, %v)",
					p, d.tokenFile.Line(p.pos), parameterTuple[0], parameterTuple[1]))
			}
		}
		// Add all predicate parameter variables to the map of predicate variables of the desugarer in order to assure that
		// lookups of identifiers while desugaring the assertion are found.
		for _, parameter := range p.desugaredParameters {
			d.predicateVarsMap[parameter.value] = parameter
		}
		p.desugaredAssertion = d.desugar(p.originalAssertion, p.associatedNode.Pos(), p.pos)
	}
}

func (p *PredicateInfo) RAC(rg *RACGenerator, invariantPos InvariantPos) ast.Node {
	results := fieldList([]*ast.Field{field(ident("bool"))})
	var parameters []*ast.Field
	for _, parameter := range p.desugaredParameters {
		paramField := field(ident(getTypeIdentifier(parameter.type_)), ident(parameter.value))
		parameters = append(parameters, paramField)
	}
	funcType := funcType(fieldList(parameters), results)
	assertion := p.desugaredAssertion.toRAC().(ast.Expr)
	typeCheckExpr(assertion, p, p.pos, rg.fset, rg.pkg, rg.tokenFile, p.desugaredParameters...)
	body := returnStmt([]ast.Expr{assertion})
	funcDecl := funcDecl(ident(p.internalName), *blockStmt(body), funcType)
	return funcDecl
}

// typeCheckExpr checks a given ast.Expr object that denotes a specification condition expression
func typeCheckExpr(expr ast.Expr, specInfo SpecInfo, pos token.Pos, fset *token.FileSet, pkg *types.Package,
	f *token.File, predicateParameters ...Identifier) {
	info := types.Info{
		Uses:  make(map[*ast.Ident]types.Object),
		Types: make(map[ast.Expr]types.TypeAndValue),
	}
	err := types.CheckExpr(fset, pkg, pos, expr, &info)
	exceptionRegex := regexp.MustCompile("undeclared name:\\s(.*OLD[1-9]*|.*Predicate[1-9]*)")
	if err != nil && !exceptionRegex.MatchString(err.Error()) && !isPredicateParameter(err.Error(), predicateParameters) {
		panic(fmt.Sprintf("Specification '%s' at line %v throws typing error: %s",
			specInfo.String(), f.Line(specInfo.Pos()), err.Error()))
	}
	assertionType := info.Types[expr].Type
	if assertionType != nil && assertionType != types.Typ[types.Bool] && assertionType != types.Typ[types.UntypedBool] {
		panic(fmt.Sprintf("Specification condition '%v' at line %v is not boolean.",
			specInfo, f.Line(specInfo.Pos())))
	}
}

// isPredicateParameter checks whether a given error reports an undeclared name, and if so, whether this name is simply
// a predicate parameter and thus undeclared because the predicate body will be wrapped around the assertion only
// after the assertion is tested.
func isPredicateParameter(errorString string, predicateParameters []Identifier) bool {
	undeclaredRegex := regexp.MustCompile("undeclared name:\\s")
	if undeclaredRegex.MatchString(errorString) {
		undeclaredVar := undeclaredRegex.Split(errorString, -1)[1]
		for _, parameter := range predicateParameters {
			if parameter.value == undeclaredVar {
				return true
			}
		}
	}
	return false
}

type PurityInfo struct {
	original       string
	pos            token.Pos
	associatedNode ast.Node
}

func (p *PurityInfo) Original() *string {
	return &p.original
}

func (p *PurityInfo) Pos() token.Pos {
	return p.pos
}

func (p *PurityInfo) AssociatedNode() *ast.Node {
	return &p.associatedNode
}

func (p *PurityInfo) String() string {
	return "pure"
}

type LabelInfo struct {
	original       string
	name           string
	pos            token.Pos
	associatedNode ast.Node

	insertBefore bool
}

func (l *LabelInfo) Original() *string {
	return &l.original
}

func (l *LabelInfo) Name() *string {
	return &l.name
}

func (l *LabelInfo) Pos() token.Pos {
	return l.pos
}

func (l *LabelInfo) AssociatedNode() *ast.Node {
	return &l.associatedNode
}

func (l *LabelInfo) InsertBefore() bool {
	return l.insertBefore
}

func (l *LabelInfo) String() string {
	return fmt.Sprintf("label %s", l.name)
}
