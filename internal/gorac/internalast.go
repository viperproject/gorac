// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"math/rand"
	"regexp"
	"strings"
)

// stringToken maps strings that represent tokens used by the parser to the corresponding token object.
var stringToken = map[string]token.Token{
	"&&": token.LAND,
	"||": token.LOR,
	"*":  token.MUL,
	"/":  token.QUO,
	"%":  token.REM,
	"+":  token.ADD,
	"-":  token.SUB,
	"==": token.EQL,
	"!=": token.NEQ,
	"<=": token.LEQ,
	">=": token.GEQ,
	"<":  token.LSS,
	">":  token.GTR,
	"!":  token.NOT,
	"&":  token.AND,
}

// Node represents an interface for all internal ast nodes. An internal ast node has to implement a function to return
// the node's type, a function to return a string representation of the node and a function to generate a runtime
// assertion check for the internal ast node.
type Node interface {
	Type() types.Type
	String() string
	extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old
	extractFunctionNames() []string
	extractQuantifiers() []Quantifier
	extractIdentifiers() []*Identifier
	toRAC() ast.Node // Runtime assertion checks are asts represented by their root node
}

// The structs below implement the different concrete types of internal ast nodes.

type Unary struct {
	type_    types.Type
	operator string
	operand  Node
}

func (u Unary) Type() types.Type {
	return u.type_
}

func (u Unary) String() string {
	return fmt.Sprintf("%s%v", u.operator, u.operand)
}

func (u Unary) Operator() string {
	return u.operator
}

func (u Unary) Operand() Node {
	return u.operand
}

func (u Unary) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	return u.operand.extractOldExpressions(labelMap, specInfo, tokenFile)
}

func (u Unary) extractFunctionNames() []string {
	return u.operand.extractFunctionNames()
}

func (u Unary) extractQuantifiers() []Quantifier {
	return u.operand.extractQuantifiers()
}

func (u Unary) extractIdentifiers() []*Identifier {
	return u.operand.extractIdentifiers()
}

func (u Unary) toRAC() ast.Node {
	operand := u.operand.toRAC().(ast.Expr)
	return unaryExpr(operand, stringToken[u.Operator()])
}

type Dereference struct {
	type_   types.Type
	operand Node
}

func (d Dereference) Type() types.Type {
	return d.type_
}

func (d Dereference) String() string {
	return fmt.Sprintf("(*%v)", d.operand)
}

func (d Dereference) Operand() Node {
	return d.operand
}

func (d Dereference) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	return d.operand.extractOldExpressions(labelMap, specInfo, tokenFile)
}

func (d Dereference) extractFunctionNames() []string {
	return d.operand.extractFunctionNames()
}

func (d Dereference) extractQuantifiers() []Quantifier {
	return d.operand.extractQuantifiers()
}

func (d Dereference) extractIdentifiers() []*Identifier {
	return d.operand.extractIdentifiers()
}

func (d Dereference) toRAC() ast.Node {
	operand := d.operand.toRAC().(ast.Expr)
	return starExpr(operand)
}

type Binary struct {
	type_    types.Type
	operator string
	left     Node
	right    Node
}

func (b Binary) Type() types.Type {
	return b.type_
}

func (b Binary) String() string {
	left := b.left
	if b.operator == "==>" {
		switch b.left.(type) {
		case Unary:
			left = b.left.(Unary).operand
		case *Unary:
			left = b.left.(*Unary).operand
		}
	}
	return fmt.Sprintf("(%v %s %v)", left, b.operator, b.right)
}

func (b Binary) Operator() string {
	return b.operator
}

func (b Binary) Left() Node {
	return b.left
}

func (b Binary) Right() Node {
	return b.right
}

func (b Binary) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := b.left.extractOldExpressions(labelMap, specInfo, tokenFile)
	return append(oldExpressions, b.right.extractOldExpressions(labelMap, specInfo, tokenFile)...)
}

func (b Binary) extractFunctionNames() []string {
	names := b.left.extractFunctionNames()
	return append(names, b.right.extractFunctionNames()...)
}

func (b Binary) extractQuantifiers() []Quantifier {
	quantifiers := b.left.extractQuantifiers()
	return append(quantifiers, b.right.extractQuantifiers()...)
}

func (b Binary) extractIdentifiers() []*Identifier {
	identifiers := b.left.extractIdentifiers()
	return append(identifiers, b.right.extractIdentifiers()...)
}

func (b Binary) toRAC() ast.Node {
	operator := b.operator
	if b.operator == "==>" {
		operator = "||"
	}
	left := b.left.toRAC().(ast.Expr)
	right := b.right.toRAC().(ast.Expr)
	return binaryExpr(left, right, stringToken[operator])
}

type Ternary struct {
	condition, positiveBranch, negativeBranch Node
	type_                                     types.Type
}

func (t Ternary) String() string {
	return fmt.Sprintf("(%v ? %v : %v)", t.condition, t.positiveBranch, t.negativeBranch)
}

func (t Ternary) Condition() Node {
	return t.condition
}

func (t Ternary) PositiveBranch() Node {
	return t.positiveBranch
}

func (t Ternary) NegativeBranch() Node {
	return t.negativeBranch
}

func (t Ternary) Type() types.Type {
	return t.type_
}

func (t Ternary) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := t.condition.extractOldExpressions(labelMap, specInfo, tokenFile)
	oldExpressions = append(oldExpressions, t.positiveBranch.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	oldExpressions = append(oldExpressions, t.negativeBranch.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	return oldExpressions
}

func (t Ternary) extractFunctionNames() []string {
	names := t.condition.extractFunctionNames()
	names = append(names, t.positiveBranch.extractFunctionNames()...)
	names = append(names, t.negativeBranch.extractFunctionNames()...)
	return names
}

func (t Ternary) extractQuantifiers() []Quantifier {
	quantifiers := t.condition.extractQuantifiers()
	quantifiers = append(quantifiers, t.positiveBranch.extractQuantifiers()...)
	quantifiers = append(quantifiers, t.negativeBranch.extractQuantifiers()...)
	return quantifiers
}

func (t Ternary) extractIdentifiers() []*Identifier {
	identifiers := t.condition.extractIdentifiers()
	identifiers = append(identifiers, t.positiveBranch.extractIdentifiers()...)
	identifiers = append(identifiers, t.negativeBranch.extractIdentifiers()...)
	return identifiers
}

func (t Ternary) toRAC() ast.Node {
	results := fieldList([]*ast.Field{field(ident("bool"))})
	funcType := funcType(fieldList([]*ast.Field{}), results)
	ifBody := blockStmt(returnStmt([]ast.Expr{t.positiveBranch.toRAC().(ast.Expr)}))
	elseBody := blockStmt(returnStmt([]ast.Expr{t.negativeBranch.toRAC().(ast.Expr)}))
	if_ := ifStmt(nil, elseBody, t.condition.toRAC().(ast.Expr), ifBody)
	funcLiteral := funcLit(*blockStmt(if_), funcType)
	return callExpr(funcLiteral)
}

type Identifier struct {
	type_ types.Type
	value string
}

func (i Identifier) Type() types.Type {
	return i.type_
}

func (i Identifier) String() string {
	return i.value
}

func (i Identifier) Value() string {
	return i.value
}

func (i Identifier) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	return []Old{}
}

func (i Identifier) extractFunctionNames() []string {
	if _, ok := i.type_.(*types.Signature); ok {
		return []string{i.value}
	} else if i.value == "len" || i.value == "cap" {
		return []string{i.value}
	} else {
		return []string{}
	}
}

func (i Identifier) extractQuantifiers() []Quantifier {
	return []Quantifier{}
}

func (i Identifier) extractIdentifiers() []*Identifier {
	return []*Identifier{&i}
}

func (i Identifier) toRAC() ast.Node {
	return ident(i.Value())
}

type Integer struct {
	type_ types.Type
	value string
}

func (i Integer) Type() types.Type {
	return i.type_
}

func (i Integer) String() string {
	return i.value
}

func (i Integer) Value() string {
	return i.value
}

func (i Integer) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	return []Old{}
}

func (i Integer) extractFunctionNames() []string {
	return []string{}
}

func (i Integer) extractQuantifiers() []Quantifier {
	return []Quantifier{}
}

func (i Integer) extractIdentifiers() []*Identifier {
	return []*Identifier{}
}

func (i Integer) toRAC() ast.Node {
	return basicLit(i.Value(), token.INT)
}

type SquareBracket struct {
	type_     types.Type
	structure Node
	index     Node
}

func (s SquareBracket) Type() types.Type {
	return s.type_
}

func (s SquareBracket) String() string {
	return fmt.Sprintf("%v[%v]", s.structure, s.index)
}

func (s SquareBracket) Structure() Node {
	return s.structure
}

func (s SquareBracket) Index() Node {
	return s.index
}

func (s SquareBracket) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := s.structure.extractOldExpressions(labelMap, specInfo, tokenFile)
	return append(oldExpressions, s.index.extractOldExpressions(labelMap, specInfo, tokenFile)...)
}

func (s SquareBracket) extractFunctionNames() []string {
	names := s.structure.extractFunctionNames()
	return append(names, s.index.extractFunctionNames()...)
}

func (s SquareBracket) extractQuantifiers() []Quantifier {
	quantifiers := s.structure.extractQuantifiers()
	return append(quantifiers, s.index.extractQuantifiers()...)
}

func (s SquareBracket) extractIdentifiers() []*Identifier {
	identifiers := s.structure.extractIdentifiers()
	return append(identifiers, s.index.extractIdentifiers()...)
}

func (s SquareBracket) toRAC() ast.Node {
	structure := s.structure.toRAC().(ast.Expr)
	index := s.index.toRAC().(ast.Expr)
	return indexExpr(structure, index)
}

type DotNotation struct {
	type_     types.Type
	structure Node
	field     Node
}

func (d DotNotation) Type() types.Type {
	return d.type_
}

func (d DotNotation) String() string {
	return fmt.Sprintf("%v.%v", d.structure, d.field)
}

func (d DotNotation) Structure() Node {
	return d.structure
}

func (d DotNotation) Field() Node {
	return d.field
}

func (d DotNotation) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	return d.structure.extractOldExpressions(labelMap, specInfo, tokenFile)
}

func (d DotNotation) extractFunctionNames() []string {
	names := d.structure.extractFunctionNames()
	return append(names, d.field.extractFunctionNames()...)
}

func (d DotNotation) extractQuantifiers() []Quantifier {
	return d.structure.extractQuantifiers()
}

func (d DotNotation) extractIdentifiers() []*Identifier {
	return d.structure.extractIdentifiers()
}

func (d DotNotation) toRAC() ast.Node {
	structure := d.structure.toRAC().(ast.Expr)
	field := d.field.toRAC().(*ast.Ident)
	return selectorExpr(structure, field)
}

type ArrayLiteral struct {
	type_     types.Type
	arrayType ArrayType
	values    [][]Node // (key, value) tuples, where key can also be nil if not named
}

func (a ArrayLiteral) Type() types.Type {
	return a.type_
}

// stringNodeTuples creates a string for the output of a list of node tuples, e.g. the values of array or struct
// literals.
func stringNodeTuples(values [][]Node, separator string) string {
	var nodeStrings []string
	for _, value := range values {
		if value[0] == nil {
			// Key for value is provided
			nodeStrings = append(nodeStrings, value[1].String())
		} else {
			nodeStrings = append(nodeStrings, value[0].String()+separator+value[1].String())
		}
	}
	return strings.Join(nodeStrings, ",")
}

func (a ArrayLiteral) String() string {
	return fmt.Sprintf("%v{%v}", a.type_, stringNodeTuples(a.values, ":"))
}

func (a ArrayLiteral) ArrayType() ArrayType {
	return a.arrayType
}

func (a ArrayLiteral) Values() [][]Node {
	return a.values
}

func (a ArrayLiteral) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := a.arrayType.extractOldExpressions(labelMap, specInfo, tokenFile)
	for _, value := range a.values {
		if value[0] != nil {
			oldExpressions = append(oldExpressions, value[0].extractOldExpressions(labelMap, specInfo, tokenFile)...)
		}
		oldExpressions = append(oldExpressions, value[1].extractOldExpressions(labelMap, specInfo, tokenFile)...)
	}
	return oldExpressions
}

func (a ArrayLiteral) extractFunctionNames() []string {
	names := a.arrayType.extractFunctionNames()
	for _, value := range a.values {
		if value[0] != nil {
			names = append(names, value[0].extractFunctionNames()...)
		}
		names = append(names, value[1].extractFunctionNames()...)
	}
	return names
}

func (a ArrayLiteral) extractQuantifiers() []Quantifier {
	quantifiers := a.arrayType.extractQuantifiers()
	for _, value := range a.values {
		if value[0] != nil {
			quantifiers = append(quantifiers, value[0].extractQuantifiers()...)
		}
		quantifiers = append(quantifiers, value[1].extractQuantifiers()...)
	}
	return quantifiers
}

func (a ArrayLiteral) extractIdentifiers() []*Identifier {
	identifiers := a.arrayType.extractIdentifiers()
	for _, value := range a.values {
		if value[0] != nil {
			identifiers = append(identifiers, value[0].extractIdentifiers()...)
		}
		identifiers = append(identifiers, value[1].extractIdentifiers()...)
	}
	return identifiers
}

// convertCompositeLiteralValues converted values of composite literals (array and struct literals) to key value
// expressions used in the runtime assertion checks.
func convertCompositeLiteralValues(values [][]Node) []ast.Expr {
	var valueNodes []ast.Expr
	for _, node := range values {
		key := node[0]
		value := node[1].toRAC().(ast.Expr)
		if key != nil {
			valueNodes = append(valueNodes, keyValueExpr(key.toRAC().(ast.Expr), value))
		} else {
			valueNodes = append(valueNodes, value)
		}
	}
	return valueNodes
}

func (a ArrayLiteral) toRAC() ast.Node {
	type_ := a.arrayType.toRAC().(ast.Expr)
	valueNodes := convertCompositeLiteralValues(a.Values())
	return compositeLit(type_, valueNodes)
}

type ArrayType struct {
	type_     types.Type
	arrayType Node
	length    Node
}

func (a ArrayType) Type() types.Type {
	return a.type_
}

func (a ArrayType) String() string {
	if a.length != nil {
		return fmt.Sprintf("[%v]%v", a.length, a.arrayType)
	} else {
		return fmt.Sprintf("[]%v", a.arrayType)
	}
}

func (a ArrayType) ArrayType() Node {
	return a.arrayType
}

func (a ArrayType) Length() Node {
	return a.length
}

func (a ArrayType) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := a.arrayType.extractOldExpressions(labelMap, specInfo, tokenFile)
	return append(oldExpressions, a.length.extractOldExpressions(labelMap, specInfo, tokenFile)...)
}

func (a ArrayType) extractFunctionNames() []string {
	names := a.arrayType.extractFunctionNames()
	return append(names, a.length.extractFunctionNames()...)
}

func (a ArrayType) extractQuantifiers() []Quantifier {
	quantifiers := a.arrayType.extractQuantifiers()
	return append(quantifiers, a.length.extractQuantifiers()...)
}

func (a ArrayType) extractIdentifiers() []*Identifier {
	identifiers := a.arrayType.extractIdentifiers()
	return append(identifiers, a.length.extractIdentifiers()...)
}

func (a ArrayType) toRAC() ast.Node {
	type_ := a.arrayType.toRAC().(ast.Expr)
	if a.Length() != nil {
		length := a.length.toRAC().(ast.Expr)
		return arrayType(length, type_)
	} else {
		return arrayType(nil, type_)
	}
}

type StructLiteral struct {
	type_      types.Type
	identifier Node
	values     [][]Node // (key, value) tuples, where key can also be nil if not named
}

func (s StructLiteral) Type() types.Type {
	return s.type_
}

func (s StructLiteral) String() string {
	return fmt.Sprintf("%v{%v}", s.identifier, stringNodeTuples(s.values, ":"))
}

func (s StructLiteral) Identifier() Node {
	return s.identifier
}

func (s StructLiteral) Values() [][]Node {
	return s.values
}

func (s StructLiteral) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := s.identifier.extractOldExpressions(labelMap, specInfo, tokenFile)
	for _, value := range s.values {
		if value[0] != nil {
			oldExpressions = append(oldExpressions, value[0].extractOldExpressions(labelMap, specInfo, tokenFile)...)
		}
		oldExpressions = append(oldExpressions, value[1].extractOldExpressions(labelMap, specInfo, tokenFile)...)
	}
	return oldExpressions
}

func (s StructLiteral) extractFunctionNames() []string {
	names := s.identifier.extractFunctionNames()
	for _, value := range s.values {
		if value[0] != nil {
			names = append(names, value[0].extractFunctionNames()...)
		}
		names = append(names, value[1].extractFunctionNames()...)
	}
	return names
}

func (s StructLiteral) extractQuantifiers() []Quantifier {
	quantifiers := s.identifier.extractQuantifiers()
	for _, value := range s.values {
		if value[0] != nil {
			quantifiers = append(quantifiers, value[0].extractQuantifiers()...)
		}
		quantifiers = append(quantifiers, value[1].extractQuantifiers()...)
	}
	return quantifiers
}

func (s StructLiteral) extractIdentifiers() []*Identifier {
	identifiers := s.identifier.extractIdentifiers()
	for _, value := range s.values {
		if value[0] != nil {
			identifiers = append(identifiers, value[0].extractIdentifiers()...)
		}
		identifiers = append(identifiers, value[1].extractIdentifiers()...)
	}
	return identifiers
}

func (s StructLiteral) toRAC() ast.Node {
	identifier := s.identifier.toRAC().(ast.Expr)
	valueNodes := convertCompositeLiteralValues(s.Values())
	return compositeLit(identifier, valueNodes)
}

type Old struct {
	type_      types.Type
	label      string // can be empty if old expression is unlabelled
	expression Node
	identifier Identifier // synthetic identifier that replaces the old condition in the runtime assertion checks
}

func (o Old) Type() types.Type {
	return o.type_
}

func (o Old) String() string {
	if o.label != "" {
		return fmt.Sprintf("old[%s](%v)", o.label, o.expression)
	} else {
		return fmt.Sprintf("old(%v)", o.expression)
	}
}

func (o Old) Expression() Node {
	return o.expression
}

func (o Old) Label() string {
	return o.label
}

func (o Old) Identifier() Identifier {
	return o.identifier
}

// extractOldExpressions return the old expression and all of the nested old expressions it contains. Additionally, it checks
// whether the restriction holds that for nested old expressions any inner label must occur in the program flow before
// any outer labels. 
func (o Old) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldPlace := getPlacement(o, labelMap, specInfo, tokenFile)
	nestedOlds := o.expression.extractOldExpressions(labelMap, specInfo, tokenFile)
	if len(nestedOlds) > 0 {
		for _, nested := range nestedOlds {
			nestedPlace := getPlacement(nested, labelMap, specInfo, tokenFile)
			if nestedPlace > oldPlace {
				panic(fmt.Sprintf("Nested inner old expression %v must be evaluated before outer old expression %v at line %v.",
					nested, o, tokenFile.Line(specInfo.Pos())))
			}
		}
	}
	return append([]Old{o}, nestedOlds...)
}

func (o Old) extractFunctionNames() []string {
	return o.expression.extractFunctionNames()
}

func (o Old) extractQuantifiers() []Quantifier {
	return o.expression.extractQuantifiers()
}

func (o Old) extractIdentifiers() []*Identifier {
	return o.expression.extractIdentifiers()
}

// getPlacement looks up the place where a given old expression should be inserted and returns the corresponding line
// number. In case of a labelled old expression that refers to a label which does not exist, the function panics.
func getPlacement(old Old, labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) int {
	place := 0
	if old.label != "" {
		placement, ok := (*labelMap)[old.label]
		if !ok {
			panic(fmt.Sprintf("Old expression %v from specification %v at line %v refers to undeclared label %s.",
				old, specInfo, tokenFile.Line(specInfo.Pos()), old.label))
		}
		place = tokenFile.Line(placement.node.Pos())
	}
	return place
}

func (o Old) toRAC() ast.Node {
	return o.identifier.toRAC()
}

type Access struct {
	type_   types.Type
	operand Node
}

func (a Access) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	return a.operand.extractOldExpressions(labelMap, specInfo, tokenFile)
}

func (a Access) extractFunctionNames() []string {
	return a.operand.extractFunctionNames()
}

func (a Access) extractQuantifiers() []Quantifier {
	return a.operand.extractQuantifiers()
}

func (a Access) extractIdentifiers() []*Identifier {
	return a.operand.extractIdentifiers()
}

func (a Access) Type() types.Type {
	return a.type_
}

func (a Access) String() string {
	return fmt.Sprintf("acc(%v)", a.operand)
}

func (a Access) Operand() Node {
	return a.operand
}

func (a Access) toRAC() ast.Node {
	// If successfully desugared, we know the operand is either an identifier referring to a pointer, a reference taken
	// from anything but composite literals or a dot notation with the underlying structure being a dereference.
	switch a.operand.(type) {
	case *Identifier, *Unary:
		// Identifiers always refer to pointer that can be checked against nil. For unary which are references taking
		// the address of something is always not nil. Thus, we could replace this access permission by true. However,
		// a replacement would omit a later type check of the stated reference expression. Therefore, we also simply
		// check the reference against nil.
		return binaryExpr(a.operand.toRAC().(ast.Expr), ident("nil"), token.NEQ)
	default: // *Dereference
		return binaryExpr(a.operand.(*Dereference).operand.toRAC().(ast.Expr), ident("nil"), token.NEQ)
	}
}

type FunctionCall struct {
	type_      types.Type
	function   Node
	parameters []Node
}

func (c FunctionCall) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := c.function.extractOldExpressions(labelMap, specInfo, tokenFile)
	for _, p := range c.parameters {
		oldExpressions = append(oldExpressions, p.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	}
	return oldExpressions
}

func (c FunctionCall) extractFunctionNames() []string {
	names := c.function.extractFunctionNames()
	for _, p := range c.parameters {
		names = append(names, p.extractFunctionNames()...)
	}
	return names
}

func (c FunctionCall) extractQuantifiers() []Quantifier {
	quantifiers := c.function.extractQuantifiers()
	for _, p := range c.parameters {
		quantifiers = append(quantifiers, p.extractQuantifiers()...)
	}
	return quantifiers
}

func (c FunctionCall) extractIdentifiers() []*Identifier {
	identifiers := c.function.extractIdentifiers()
	for _, p := range c.parameters {
		identifiers = append(identifiers, p.extractIdentifiers()...)
	}
	return identifiers
}

func (c FunctionCall) Type() types.Type {
	return c.type_
}

// stringParameters creates a string for the output of an array of parameter nodes.
func stringParameters(nodes []Node) string {
	var nodeStrings []string
	for _, value := range nodes {
		nodeStrings = append(nodeStrings, value.String())
	}
	return strings.Join(nodeStrings, ", ")
}

func (c FunctionCall) String() string {
	return fmt.Sprintf("%v(%v)", c.function, stringParameters(c.parameters))
}

func (c FunctionCall) Function() Node {
	return c.function
}

func (c FunctionCall) Parameters() []Node {
	return c.parameters
}

func (c FunctionCall) toRAC() ast.Node {
	var parametersRAC []ast.Expr
	for _, p := range c.parameters {
		parametersRAC = append(parametersRAC, p.toRAC().(ast.Expr))
	}
	return callExpr(c.function.toRAC().(ast.Expr), parametersRAC...)
}

type PredicateCall struct {
	type_      types.Type
	parameters []Node
	predicate  *PredicateInfo
}

func (c PredicateCall) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	// Check whether the predicate does not hold any old expressions.
	predicateAssertionString := c.predicate.desugaredAssertion.String()
	oldRegex := regexp.MustCompile("old(\\[[a-zA-Z0-9]*])?\\((.*)\\)")
	if oldRegex.MatchString(predicateAssertionString) {
		panic(fmt.Sprintf("Predicate '%v' at line %d is not allowed to contain old expressions.",
			c.predicate, tokenFile.Line(specInfo.Pos())))
	}
	// Collect all old expressions used in parameters.
	var oldExpressions []Old
	for _, p := range c.parameters {
		oldExpressions = append(oldExpressions, p.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	}
	return oldExpressions
}

func (c PredicateCall) extractFunctionNames() []string {
	var names []string
	for _, p := range c.parameters {
		names = append(names, p.extractFunctionNames()...)
	}
	return names
}

func (c PredicateCall) extractQuantifiers() []Quantifier {
	var quantifiers []Quantifier
	for _, p := range c.parameters {
		quantifiers = append(quantifiers, p.extractQuantifiers()...)
	}
	return quantifiers
}

func (c PredicateCall) extractIdentifiers() []*Identifier {
	var identifiers []*Identifier
	for _, p := range c.parameters {
		identifiers = append(identifiers, p.extractIdentifiers()...)
	}
	return identifiers
}

func (c PredicateCall) Type() types.Type {
	return c.type_
}

func (c PredicateCall) String() string {
	return fmt.Sprintf("%v(%v)", c.predicate.internalName, stringParameters(c.parameters))
}

func (c PredicateCall) Parameters() []Node {
	return c.parameters
}

func (c PredicateCall) Predicate() *PredicateInfo {
	return c.predicate
}

func (c PredicateCall) toRAC() ast.Node {
	var parametersRAC []ast.Expr
	for _, p := range c.parameters {
		parametersRAC = append(parametersRAC, p.toRAC().(ast.Expr))
	}
	return callExpr(ident(c.predicate.internalName), parametersRAC...)
}

type Quantifier interface {
	QuantifiedVars() []Identifier
	Domain() *Domain
	Condition() Node
}

type UnivQuantifier struct {
	quantifiedVars []Identifier
	domain         *Domain // can be empty if only boolean variables are used
	condition      Node
}

// stringQuantifiedIdentifiers creates a string for the output of a list of quantified variables of universal or
// existential quantifiers.
func stringQuantifiedIdentifiers(identifiers []Identifier) string {
	var nodeStrings []string
	for _, i := range identifiers {
		nodeStrings = append(nodeStrings, i.value+" "+i.type_.String())
	}
	return strings.Join(nodeStrings, ",")
}

func (u UnivQuantifier) String() string {
	if u.domain != nil {
		return fmt.Sprintf("(forall %s :: %v ==> %v)",
			stringQuantifiedIdentifiers(u.quantifiedVars), u.domain, u.condition)
	} else {
		return fmt.Sprintf("(forall %s :: %v)",
			stringQuantifiedIdentifiers(u.quantifiedVars), u.condition)
	}
}

func (u UnivQuantifier) Domain() *Domain {
	return u.domain
}

func (u UnivQuantifier) Condition() Node {
	return u.condition
}

func (u UnivQuantifier) QuantifiedVars() []Identifier {
	return u.quantifiedVars
}

func (u UnivQuantifier) Type() types.Type {
	return types.Typ[types.Bool]
}

func (u UnivQuantifier) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := u.condition.extractOldExpressions(labelMap, specInfo, tokenFile)
	for _, quantifiedVar := range u.quantifiedVars {
		oldExpressions = append(oldExpressions, quantifiedVar.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	}
	if u.domain != nil {
		oldExpressions = append(oldExpressions, u.domain.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	}
	return oldExpressions
}

func (u UnivQuantifier) extractFunctionNames() []string {
	names := u.condition.extractFunctionNames()
	for _, quantifiedVar := range u.quantifiedVars {
		names = append(names, quantifiedVar.extractFunctionNames()...)
	}
	if u.domain != nil {
		names = append(names, u.domain.extractFunctionNames()...)
	}
	return names
}

func (u UnivQuantifier) extractQuantifiers() []Quantifier {
	quantifiers := []Quantifier{u}
	quantifiers = append(quantifiers, u.condition.extractQuantifiers()...)
	for _, quantifiedVar := range u.quantifiedVars {
		quantifiers = append(quantifiers, quantifiedVar.extractQuantifiers()...)
	}
	if u.domain != nil {
		quantifiers = append(quantifiers, u.domain.extractQuantifiers()...)
	}
	return quantifiers
}

func (u UnivQuantifier) extractIdentifiers() []*Identifier {
	identifiers := u.condition.extractIdentifiers()
	for _, quantifiedVar := range u.quantifiedVars {
		identifiers = append(identifiers, quantifiedVar.extractIdentifiers()...)
	}
	if u.domain != nil {
		identifiers = append(identifiers, u.domain.extractIdentifiers()...)
	}
	return identifiers
}

func (u UnivQuantifier) toRAC() ast.Node {
	results := fieldList([]*ast.Field{field(ident("bool"))})
	funcType := funcType(fieldList([]*ast.Field{}), results)
	var domainStmt ast.Stmt
	domainStmt = &ast.EmptyStmt{}
	ifBody := blockStmt(returnStmt([]ast.Expr{ident("false")}))
	if_ := ifStmt(nil, nil, unaryExpr(u.condition.toRAC().(ast.Expr), token.NOT), ifBody)
	domainStmt = addBooleanDomains(if_, u.quantifiedVars, u.domain)
	if u.domain != nil {
		quantifiedVarsMap := make(map[string]*Identifier)
		for _, quantifiedVar := range u.quantifiedVars {
			quantifiedVarsMap[quantifiedVar.value] = &quantifiedVar
		}
		domainStmt = domainToRAC(u, u.domain, &quantifiedVarsMap, domainStmt)
	}
	funcLiteral := funcLit(*blockStmt(domainStmt, returnStmt([]ast.Expr{ident("true")})), funcType)
	callExpr := callExpr(funcLiteral)
	return callExpr
}

type ExistQuantifier struct {
	quantifiedVars []Identifier
	domain         *Domain // can be empty if only boolean variables are used
	condition      Node
}

func (e ExistQuantifier) String() string {
	if e.domain != nil {
		return fmt.Sprintf("(exists %s :: %v && %v)",
			stringQuantifiedIdentifiers(e.quantifiedVars), e.domain, e.condition)
	} else {
		return fmt.Sprintf("(exists %s :: %v)",
			stringQuantifiedIdentifiers(e.quantifiedVars), e.condition)
	}
}

func (e ExistQuantifier) Domain() *Domain {
	return e.domain
}

func (e ExistQuantifier) Condition() Node {
	return e.condition
}

func (e ExistQuantifier) QuantifiedVars() []Identifier {
	return e.quantifiedVars
}

func (e ExistQuantifier) Type() types.Type {
	return types.Typ[types.Bool]
}

func (e ExistQuantifier) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := e.condition.extractOldExpressions(labelMap, specInfo, tokenFile)
	for _, quantifiedVar := range e.quantifiedVars {
		oldExpressions = append(oldExpressions, quantifiedVar.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	}
	if e.domain != nil {
		oldExpressions = append(oldExpressions, e.domain.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	}
	return oldExpressions
}

func (e ExistQuantifier) extractFunctionNames() []string {
	names := e.condition.extractFunctionNames()
	for _, quantifiedVar := range e.quantifiedVars {
		names = append(names, quantifiedVar.extractFunctionNames()...)
	}
	if e.domain != nil {
		names = append(names, e.domain.extractFunctionNames()...)
	}
	return names
}

func (e ExistQuantifier) extractQuantifiers() []Quantifier {
	quantifiers := []Quantifier{e}
	quantifiers = append(quantifiers, e.condition.extractQuantifiers()...)
	for _, quantifiedVar := range e.quantifiedVars {
		quantifiers = append(quantifiers, quantifiedVar.extractQuantifiers()...)
	}
	if e.domain != nil {
		quantifiers = append(quantifiers, e.domain.extractQuantifiers()...)
	}
	return quantifiers
}

func (e ExistQuantifier) extractIdentifiers() []*Identifier {
	identifiers := e.condition.extractIdentifiers()
	for _, quantifiedVar := range e.quantifiedVars {
		identifiers = append(identifiers, quantifiedVar.extractIdentifiers()...)
	}
	if e.domain != nil {
		identifiers = append(identifiers, e.domain.extractIdentifiers()...)
	}
	return identifiers
}

func (e ExistQuantifier) toRAC() ast.Node {
	results := fieldList([]*ast.Field{field(ident("bool"))})
	funcType := funcType(fieldList([]*ast.Field{}), results)
	var domainStmt ast.Stmt
	domainStmt = &ast.EmptyStmt{}
	ifBody := blockStmt(returnStmt([]ast.Expr{ident("true")}))
	if_ := ifStmt(nil, nil, e.condition.toRAC().(ast.Expr), ifBody)
	domainStmt = addBooleanDomains(if_, e.quantifiedVars, e.domain)
	if e.domain != nil {
		quantifiedVarsMap := make(map[string]*Identifier)
		for _, quantifiedVar := range e.quantifiedVars {
			quantifiedVarsMap[quantifiedVar.value] = &quantifiedVar
		}
		domainStmt = domainToRAC(e, e.domain, &quantifiedVarsMap, domainStmt)
	}
	funcLiteral := funcLit(*blockStmt(domainStmt, returnStmt([]ast.Expr{ident("false")})), funcType)
	callExpr := callExpr(funcLiteral)
	return callExpr
}

type Domain struct {
	isLeaf      bool
	literal     DomainLiteral
	left, right *Domain // can be nil if leaf domain node
	operator    string  // either && or || or empty if leaf domain node
}

func (d Domain) String() string {
	if !d.isLeaf {
		return fmt.Sprintf("(%s %s %s)", d.left.String(), d.operator, d.right.String())
	} else {
		return d.literal.String()
	}
}

func (d Domain) IsLeaf() bool {
	return d.isLeaf
}

func (d Domain) DomainLiteral() DomainLiteral {
	return d.literal
}

func (d Domain) Left() *Domain {
	return d.left
}

func (d Domain) Right() *Domain {
	return d.right
}

func (d Domain) Operator() string {
	return d.operator
}

func (d Domain) Type() types.Type {
	return types.Typ[types.Bool]
}

func (d Domain) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	if !d.isLeaf {
		oldExpressions := d.left.extractOldExpressions(labelMap, specInfo, tokenFile)
		return append(oldExpressions, d.right.extractOldExpressions(labelMap, specInfo, tokenFile)...)
	} else {
		return d.literal.extractOldExpressions(labelMap, specInfo, tokenFile)
	}
}

func (d Domain) extractFunctionNames() []string {
	if !d.isLeaf {
		names := d.left.extractFunctionNames()
		return append(names, d.right.extractFunctionNames()...)
	} else {
		return d.literal.extractFunctionNames()
	}
}

func (d Domain) extractQuantifiers() []Quantifier {
	if !d.isLeaf {
		quantifiers := d.left.extractQuantifiers()
		return append(quantifiers, d.right.extractQuantifiers()...)
	} else {
		return d.literal.extractQuantifiers()
	}
}

func (d Domain) extractIdentifiers() []*Identifier {
	if !d.isLeaf {
		identifiers := d.left.extractIdentifiers()
		return append(identifiers, d.right.extractIdentifiers()...)
	} else {
		return d.literal.extractIdentifiers()
	}
}

func (d Domain) toRAC() ast.Node {
	return nil // dummy to be considered a Node
}

func (d Domain) extractQuantifiedVars(boundedVarsMap *map[string]*Identifier) {
	if !d.isLeaf {
		d.right.extractQuantifiedVars(boundedVarsMap)
		d.left.extractQuantifiedVars(boundedVarsMap)
	} else {
		for _, i := range d.literal.extractQuantifiedVars() {
			(*boundedVarsMap)[i.value] = i
		}
	}
}

// extractBoundedVars only extracts quantified variables that are bounded in all branches of domain tree. This is
// different from extractQuantifiedVars where all quantified variables from any branch of the domain tree are returned.
func (d Domain) extractBoundedVars(boundedVarsMap *map[string]*Identifier) {
	if !d.isLeaf {
		if d.operator == "&&" {
			// Union
			d.right.extractQuantifiedVars(boundedVarsMap)
			d.left.extractQuantifiedVars(boundedVarsMap)
		} else if d.operator == "||" {
			// Intersection
			rightMap := make(map[string]*Identifier)
			d.right.extractQuantifiedVars(&rightMap)
			leftMap := make(map[string]*Identifier)
			d.left.extractQuantifiedVars(&leftMap)
			for name, identifier := range intersection(rightMap, leftMap) {
				(*boundedVarsMap)[name] = identifier
			}
		}
	} else {
		for _, i := range d.literal.extractQuantifiedVars() {
			(*boundedVarsMap)[i.value] = i
		}
	}
}

func domainToRAC(quantifier Quantifier, domain *Domain, unboundedVars *map[string]*Identifier, stmt ast.Stmt) ast.Stmt {
	if !domain.isLeaf {
		if domain.operator == "&&" {
			// We first need to check in which order we need to nest the conjunct domains. E.g. for domains such as
			// 		0 < x < y && 0 < y < 3
			// it is important that the loop of y is on the outside since y needs to be declared in order for x to
			// have a valid bound.
			leftBoundIdentifiers := domain.left.extractIdentifiers()
			rightBoundIdentifiers := domain.right.extractIdentifiers()
			rightQuantifiedVars := map[string]*Identifier{}
			domain.right.extractQuantifiedVars(&rightQuantifiedVars)
			leftQuantifiedVars := map[string]*Identifier{}
			domain.left.extractQuantifiedVars(&leftQuantifiedVars)
			boundLeft := boundIsQuantifiedVar(leftBoundIdentifiers, rightQuantifiedVars)
			boundRight := boundIsQuantifiedVar(rightBoundIdentifiers, leftQuantifiedVars)
			if boundLeft == nil {
				right := domainToRAC(quantifier, domain.right, getFreeVars(unboundedVars, &leftQuantifiedVars), stmt)
				return domainToRAC(quantifier, domain.left, unboundedVars, right)
			} else if boundRight == nil {
				left := domainToRAC(quantifier, domain.left, getFreeVars(unboundedVars, &rightQuantifiedVars), stmt)
				return domainToRAC(quantifier, domain.right, unboundedVars, left)
			} else {
				panic(fmt.Sprintf("Domain %v of quantifier %v uses identifers %v and %v in a cycling dependency between bounds and quantified variables",
					*domain, quantifier, boundLeft, boundRight))
			}
		} else {
			// Disjunction of domains
			copyUnboundedVars := copyMap(unboundedVars)
			left := domainToRAC(quantifier, domain.left, unboundedVars, stmt)
			right := domainToRAC(quantifier, domain.right, copyUnboundedVars, stmt)
			return blockStmt(left, right)
		}
	} else {
		return domain.literal.toRacWithStmt(stmt, unboundedVars)
	}
}

// DomainLiteral provides an interface for the two different types of domains: numeric domains and data structure domains.
type DomainLiteral interface {
	Node
	// toRACWithStmt is used to generate the runtime assertion check for a domain literal that will incorporate the
	// statement that is passed into the function. We cannot simply use toRAC since for nested for-loop generation in
	// the runtime checks of quantifiers, we need to be able to recursively pass statements to the runtime check
	// generation quantifiers.
	toRacWithStmt(stmt ast.Stmt, unboundedVars *map[string]*Identifier) ast.Stmt
	// extractQuantifiedVars returns all quantified variables that are used in the domain literal. For numeric domain
	// literals this is always just the bounded variable. For data structure domain literals it can be the key, the
	// key and the value or just the value.
	extractQuantifiedVars() []*Identifier
}

type NumericDomainLiteral struct {
	variable                     *Identifier
	lower, upper                 Node
	lowerRelation, upperRelation string // lowerRelation is either < or <=, upperRelation is either > or >=
	loopName                     string
}

func (ndl NumericDomainLiteral) String() string {
	return fmt.Sprintf("%v %s %v %s %v", ndl.lower, ndl.lowerRelation, ndl.variable, ndl.upperRelation, ndl.upper)
}

func (ndl NumericDomainLiteral) Variable() *Identifier {
	return ndl.variable
}

func (ndl NumericDomainLiteral) Lower() Node {
	return ndl.lower
}

func (ndl NumericDomainLiteral) Upper() Node {
	return ndl.upper
}

func (ndl NumericDomainLiteral) LowerRelation() string {
	return ndl.lowerRelation
}

func (ndl NumericDomainLiteral) UpperRelation() string {
	return ndl.upperRelation
}

func (ndl NumericDomainLiteral) Type() types.Type {
	return types.Typ[types.Bool]
}

func (ndl NumericDomainLiteral) LoopName() string {
	return ndl.loopName
}

func (ndl NumericDomainLiteral) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	oldExpressions := ndl.lower.extractOldExpressions(labelMap, specInfo, tokenFile)
	return append(oldExpressions, ndl.upper.extractOldExpressions(labelMap, specInfo, tokenFile)...)
}

func (ndl NumericDomainLiteral) extractFunctionNames() []string {
	names := ndl.lower.extractFunctionNames()
	return append(names, ndl.upper.extractFunctionNames()...)
}

func (ndl NumericDomainLiteral) extractQuantifiers() []Quantifier {
	quantifiers := ndl.lower.extractQuantifiers()
	return append(quantifiers, ndl.upper.extractQuantifiers()...)
}

func (ndl NumericDomainLiteral) extractIdentifiers() []*Identifier {
	identifiers := ndl.lower.extractIdentifiers()
	return append(identifiers, ndl.upper.extractIdentifiers()...)
}

func (ndl NumericDomainLiteral) extractQuantifiedVars() []*Identifier {
	return []*Identifier{ndl.variable}
}

func (ndl NumericDomainLiteral) toRAC() ast.Node {
	var init *ast.AssignStmt
	variable := ident(ndl.loopName)
	lower := ndl.lower.toRAC().(ast.Expr)
	if ndl.lowerRelation == "<=" {
		init = assignStmt([]ast.Expr{variable}, []ast.Expr{lower}, token.DEFINE)
	} else {
		reducedLower := binaryExpr(lower, basicLit("1", token.INT), token.ADD)
		init = assignStmt([]ast.Expr{variable}, []ast.Expr{reducedLower}, token.DEFINE)
	}
	cond := ndl.getBoundCondition(variable, ndl.upper.toRAC().(ast.Expr), ndl.upperRelation)
	post := incDecStmt(variable, token.INC)
	return forStmt(init, post, cond, nil)
}

func (ndl NumericDomainLiteral) getBoundCondition(leftSide, rightSide ast.Expr, relation string) *ast.BinaryExpr {
	var cond *ast.BinaryExpr
	if relation == "<=" {
		cond = binaryExpr(leftSide, rightSide, token.LEQ)
	} else {
		cond = binaryExpr(leftSide, rightSide, token.LSS)
	}
	return cond
}

func (ndl NumericDomainLiteral) toRacWithStmt(stmt ast.Stmt, unboundedVars *map[string]*Identifier) ast.Stmt {
	isFiltered := false
	oldStmt := stmt
	isFiltered, ndl.loopName, stmt = filterVariableCheck(ndl.variable.value, stmt, unboundedVars)
	if isFiltered {
		optimizedStmt, _ := ndl.optimizeFiltering(oldStmt)
		return optimizedStmt
	}
	forStmt := ndl.toRAC().(*ast.ForStmt)
	forStmt.Body = blockStmt(stmt)
	return forStmt
}

// optimizeFiltering replaces the filtering loop
//
// 	for x' := e1(+ 1)?; x' o2 e2; x’++ { // specified domain: e1 o1 x’ o2 e2
//  	if (x == x') {
//    		s
//  	}
//	}
//
// by the optimized check
//
// 	if (e1 o1 x && x o2 e2) {
//   	s
// }
func (ndl NumericDomainLiteral) optimizeFiltering(stmt ast.Stmt) (ast.Stmt, bool) {
	var result ast.Stmt
	variable := ndl.variable.toRAC().(*ast.Ident)
	lowerCheck := ndl.getBoundCondition(ndl.lower.toRAC().(ast.Expr), variable, ndl.lowerRelation)
	upperCheck := ndl.getBoundCondition(variable, ndl.upper.toRAC().(ast.Expr), ndl.upperRelation)
	result = ifStmt(nil, nil, binaryExpr(lowerCheck, upperCheck, token.LAND), blockStmt(stmt))
	return result, true
}

type LiteralType int

const (
	KEY = iota
	VALUE
	KEYVALUE
)

type DataStructureDomainLiteral struct {
	literalType   LiteralType
	key, value    *Identifier // at least one of these two is not equal to nil
	structure     Node
	loopKeyName   string
	loopValueName string
}

func (ddl DataStructureDomainLiteral) String() string {
	switch ddl.literalType {
	case KEYVALUE:
		return fmt.Sprintf("(%s, %s) in range %v", ddl.key.String(), ddl.value.String(), ddl.structure)
	case KEY:
		return fmt.Sprintf("%s in range %v", ddl.key.String(), ddl.structure)
	default:
		// case VALUE
		return fmt.Sprintf("(_, %s) in range %v", ddl.value.String(), ddl.structure)
	}
}

func (ddl DataStructureDomainLiteral) LiteralType() LiteralType {
	return ddl.literalType
}

func (ddl DataStructureDomainLiteral) Key() *Identifier {
	return ddl.key
}

func (ddl DataStructureDomainLiteral) Value() *Identifier {
	return ddl.value
}

func (ddl DataStructureDomainLiteral) Structure() Node {
	return ddl.structure
}

func (ddl DataStructureDomainLiteral) Type() types.Type {
	return types.Typ[types.Bool]
}

func (ddl DataStructureDomainLiteral) LoopKeyName() string {
	return ddl.loopKeyName
}

func (ddl DataStructureDomainLiteral) LoopValueName() string {
	return ddl.loopValueName
}

func (ddl DataStructureDomainLiteral) extractOldExpressions(labelMap *map[string]Placement, specInfo SpecInfo, tokenFile *token.File) []Old {
	return ddl.structure.extractOldExpressions(labelMap, specInfo, tokenFile)
}

func (ddl DataStructureDomainLiteral) extractFunctionNames() []string {
	return ddl.structure.extractFunctionNames()
}

func (ddl DataStructureDomainLiteral) extractQuantifiers() []Quantifier {
	return ddl.structure.extractQuantifiers()
}

func (ddl DataStructureDomainLiteral) extractQuantifiedVars() []*Identifier {
	switch ddl.literalType {
	case KEYVALUE:
		return []*Identifier{ddl.key, ddl.value}
	case KEY:
		return []*Identifier{ddl.key}
	default:
		// case VALUE
		return []*Identifier{ddl.value}
	}
}

func (ddl DataStructureDomainLiteral) extractIdentifiers() []*Identifier {
	return ddl.structure.extractIdentifiers()
}

func (ddl DataStructureDomainLiteral) toRAC() ast.Node {
	var key, value ast.Expr
	switch ddl.literalType {
	case KEYVALUE:
		key = ident(ddl.loopKeyName)
		value = ident(ddl.loopValueName)
	case KEY:
		key = ident(ddl.loopKeyName)
	default:
		// case VALUE
		key = ident("_")
		value = ident(ddl.loopValueName)
	}
	return rangeStmt(key, value, ddl.structure.toRAC().(ast.Expr), token.DEFINE, nil)
}

func (ddl DataStructureDomainLiteral) toRacWithStmt(stmt ast.Stmt, unboundedVars *map[string]*Identifier) ast.Stmt {
	keyIsFiltered, valueIsFiltered := false, false
	oldStmt := stmt
	switch ddl.literalType {
	case KEYVALUE:
		keyIsFiltered, ddl.loopKeyName, stmt = filterVariableCheck(ddl.key.value, stmt, unboundedVars)
		valueIsFiltered, ddl.loopValueName, stmt = filterVariableCheck(ddl.value.value, stmt, unboundedVars)
		// Check whether we are filtering for the key and the value, and if so, whether the filtering can be isOptimized
		if keyIsFiltered && valueIsFiltered {
			if optimizedStmt, isOptimized := ddl.optimizeKeyValueFiltering(oldStmt, ddl.loopValueName); isOptimized {
				return optimizedStmt
			}
		}
	case KEY:
		keyIsFiltered, ddl.loopKeyName, stmt = filterVariableCheck(ddl.key.value, stmt, unboundedVars)
		// Check whether we are filtering for the key, and if so, whether the filtering can be isOptimized
		if keyIsFiltered {
			if optimizedStmt, isOptimized := ddl.optimizeKeyFiltering(oldStmt); isOptimized {
				return optimizedStmt
			}
		}
	default:
		// case VALUE
		// No optimizations possible in this case
		ddl.loopKeyName = "_"
		_, ddl.loopValueName, stmt = filterVariableCheck(ddl.value.value, stmt, unboundedVars)
	}
	rangeStmt := ddl.toRAC().(*ast.RangeStmt)
	rangeStmt.Body = blockStmt(stmt)
	return rangeStmt
}

// optimizeKeyFiltering checks whether the underlying structure of the filtered domain is of type array, slice or map.
// In these cases, we return an isOptimized statement using helper methods for filtering arrays/slices or maps.
func (ddl DataStructureDomainLiteral) optimizeKeyFiltering(stmt ast.Stmt) (ast.Stmt, bool) {
	var result ast.Stmt
	isOptimized := false
	switch ddl.structure.Type().(type) {
	case *types.Array, *types.Slice:
		result, isOptimized = ddl.optimizeKeyFilteringArraySlice(result, stmt, isOptimized) // result == true
	case *types.Map:
		result, isOptimized = ddl.optimizeKeyFilteringMap(result, stmt, isOptimized) // result == true
	}
	return result, isOptimized
}

// optimizeKeyValueFiltering checks whether the underlying structure of the filtered domain is of type array, slice or
// map. In these cases, we return an isOptimized statement using helper methods for filtering arrays/slices or maps.
func (ddl DataStructureDomainLiteral) optimizeKeyValueFiltering(stmt ast.Stmt, newValueName string) (ast.Stmt, bool) {
	var result ast.Stmt
	isOptimized := false
	switch ddl.structure.Type().(type) {
	case *types.Array, *types.Slice:
		result, isOptimized = ddl.optimizeKeyValueFilteringArraySlice(result, stmt, isOptimized)
	case *types.Map:
		result, isOptimized = ddl.optimizeKeyValueFilteringMap(newValueName, result, stmt, isOptimized)
	}
	return result, isOptimized
}

// optimizeKeyFilteringArraySlice replaces the filtering loop
//
// 	for x' := range arrayOrSlice {
// 		if (x == x') {
// 			s
// 		}
//	}
//
// by the optimized check
//
// 	if x >= 0 && x < len(arrayOrSlice) {
//   	s
// 	}
func (ddl DataStructureDomainLiteral) optimizeKeyFilteringArraySlice(result ast.Stmt, stmt ast.Stmt,
	isOptimized bool) (ast.Stmt, bool) {
	key := ddl.key.toRAC().(ast.Expr)
	structure := ddl.structure.toRAC().(ast.Expr)
	greaterZero := binaryExpr(key, basicLit("0", token.INT), token.GEQ)
	lessThanArrayLen := binaryExpr(key, callExpr(ident("len"), structure), token.LEQ)
	result = ifStmt(nil, nil, binaryExpr(greaterZero, lessThanArrayLen, token.LAND), blockStmt(stmt))
	isOptimized = true
	return result, isOptimized
}

// optimizeKeyFilteringMap replaces the filtering loop
//
// 	for x' := range map {
// 		if (x == x') {
// 			s
// 		}
//	}
//
// by the optimized check
//
// 	if _, ok := map[x]; ok {
//   	s
// 	}
func (ddl DataStructureDomainLiteral) optimizeKeyFilteringMap(result ast.Stmt, stmt ast.Stmt, isOptimized bool) (ast.Stmt, bool) {
	key := ddl.key.toRAC().(ast.Expr)
	structure := ddl.structure.toRAC().(ast.Expr)
	ok := ident(fmt.Sprintf("ok%d", rand.Intn(100)))
	init := assignStmt([]ast.Expr{ident("_"), ok}, []ast.Expr{indexExpr(structure, key)}, token.DEFINE)
	result = ifStmt(init, nil, ok, blockStmt(stmt))
	isOptimized = true
	return result, isOptimized
}

// optimizeKeyValueFilteringArraySlice replaces the filtering loop
//
// 	for i', x' := range arrayOrSlice {
//  	if (i’ == i && x == x') {
//    		s
//  	}
//	}
//
// by the optimized check
//
// 	if i >= 0 && i < len(arrayOrSlice) && arrayOrSlice[i] == x {
//   	s
// 	}
func (ddl DataStructureDomainLiteral) optimizeKeyValueFilteringArraySlice(result ast.Stmt, stmt ast.Stmt, isOptimized bool) (ast.Stmt, bool) {
	key := ddl.key.toRAC().(ast.Expr)
	value := ddl.value.toRAC().(ast.Expr)
	structure := ddl.structure.toRAC().(ast.Expr)
	greaterZero := binaryExpr(key, basicLit("0", token.INT), token.GEQ)
	lessThanArrayLen := binaryExpr(key, callExpr(ident("len"), structure), token.LEQ)
	equality := binaryExpr(indexExpr(structure, key), value, token.EQL)
	cond := binaryExpr(binaryExpr(greaterZero, lessThanArrayLen, token.LAND), equality, token.LAND)
	result = ifStmt(nil, nil, cond, blockStmt(stmt))
	isOptimized = true
	return result, isOptimized
}

// optimizeKeyValueFilteringMap replaces the filtering loop
//
// 	for k', x' := range map {
//  	if (k’ == k && x == x') {
//    		s
//  	}
//	}
//
// by the optimized check
//
// 	if x', ok := map[k]; ok && x == x' {
//   	s
// 	}
func (ddl DataStructureDomainLiteral) optimizeKeyValueFilteringMap(newValueName string, result ast.Stmt,
	stmt ast.Stmt, isOptimized bool) (ast.Stmt, bool) {
	key := ddl.key.toRAC().(ast.Expr)
	value := ddl.value.toRAC().(ast.Expr)
	newValue := ident(newValueName)
	structure := ddl.structure.toRAC().(ast.Expr)
	ok := ident(fmt.Sprintf("ok%d", rand.Intn(100)))
	init := assignStmt([]ast.Expr{newValue, ok}, []ast.Expr{indexExpr(structure, key)}, token.DEFINE)
	cond := binaryExpr(ok, binaryExpr(value, newValue, token.EQL), token.LAND)
	result = ifStmt(init, nil, cond, blockStmt(stmt))
	isOptimized = true
	return result, isOptimized
}
