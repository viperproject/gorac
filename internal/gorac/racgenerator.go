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
	"golang.org/x/tools/go/ast/astutil"
	"log"
	"math/rand"
	"reflect"
	"regexp"
	"strings"
)

// RACGenerator holds all file information needed for the runtime check generation.
type RACGenerator struct {
	conf                  *Config
	fset                  *token.FileSet
	astFile               *ast.File
	tokenFile             *token.File
	pkg                   *types.Package
	lastStmtAssertIgnored bool
}

// NewRACGenerator creates and returns a new RACGenerator instance.
func NewRACGenerator(conf *Config, fset *token.FileSet, astFile *ast.File, tokenFile *token.File, pkg *types.Package) (rg *RACGenerator) {
	return &RACGenerator{
		conf:                  conf,
		fset:                  fset,
		astFile:               astFile,
		tokenFile:             tokenFile,
		pkg:                   pkg,
		lastStmtAssertIgnored: false,
	}
}

// Generate executes the steps needed to generate the runtime assertion checks for a RACGenerator object.
func (rg *RACGenerator) Generate() (n ast.Node) {
	// Specification is inserted as comments, thus we retrieve all comments from the RACGenerator's ast file with a
	// command map from ast nodes to comments
	cmap := ast.NewCommentMap(rg.fset, rg.astFile, rg.astFile.Comments)
	// Parse specification out of comments and create specInfo objects that contain all information necessary to next
	// add the runtime assertion checks
	sharedVarsMap := make(map[string]*types.Scope)
	exclusiveVarsMap := make(map[string]*types.Scope)
	predicateInfoMap := make(map[string]*PredicateInfo)
	specInfos, racInfosUnsorted := rg.extractSpecification(cmap, &sharedVarsMap, &exclusiveVarsMap, &predicateInfoMap)
	// Since the order of the comment map is not deterministic, we make the rest of the program deterministic by first
	// sorting the specInfo objects and then desugaring. An exception is made for desugaring predicate assertions since
	// these will not result in their own runtime assertion checks but only used in the checks of predicate calls.
	racInfos := rg.desugarSortedRACInfos(racInfosUnsorted, &predicateInfoMap)
	// When writing postconditions that reasons about return parameters and, instead of assigning the return parameter
	// this value and using an empty return statement, a different value is returned, then the return parameter will
	// still have its default value as initialized on function entry (or any value it was assigned before the function
	// exit. In order to mitigate this effect, any named return parameter is assigned the returned expression before
	// the expression is actually returned.
	// This should be done before any other changes to the AST since we don't want to do this for any returns inserted
	// into the AST during RAC generation (for example, when an anonymous function is declared for quantifier checks).
	rg.assignNamedReturnParameter()
	// Check whether functions that have purity annotations are actually pure
	NewPurityChecker(rg.tokenFile, rg.astFile, &specInfos, &racInfos).check()
	// We check that the quantifiers have the correct domain syntax such that later the runtime checks can be generated.
	NewQuantifierChecker(rg.tokenFile, rg.pkg, rg.astFile, &racInfos).check()
	// Add all assignments for old expressions to the Go AST. Declarations must be added later in order to avoid
	// 'undeclared variable' errors for postconditions.
	oldExprConverter := NewOldExprConverter(rg.tokenFile, rg.pkg, rg.astFile, &specInfos, &racInfos,
		&sharedVarsMap, &exclusiveVarsMap)
	oldExprConverter.addAssignments()
	// Add function definitions for predicates to the Go AST.
	rg.addPredicateFunctions(&predicateInfoMap)
	// Add the runtime assertion checks to the parsed ast and return the root node of the modified ast
	n = rg.addRACs(racInfos)
	// Add declarations for old expressions to the Go AST. They are added after the postconditions have been added to
	// the function bodies in order to avoid 'undeclared variable' errors.
	oldExprConverter.addDeclarations()
	// Adds an import for 'fmt' since this is needed for the panic calls. No 'fmt' import is added if no runtime checks
	// were inserted into the AST.
	if len(racInfos) > 1 || (len(racInfos) == 1 && !rg.lastStmtAssertIgnored) {
		rg.addFmtImport()
	}
	return n
}

// extractSpecification iterates through all comments of a given command map and creates specInfo objects for all
// specification comments. The prefix `//@` for single line comments or respecively `/*@` for multiline comments denotes
// the start of a specification comment.
func (rg *RACGenerator) extractSpecification(cmap ast.CommentMap, sharedVarsMap, exclusiveVarsMap *map[string]*types.Scope,
	predicateInfoMap *map[string]*PredicateInfo) (specInfos []SpecInfo, racInfos []RACInfo) {
	var keywords = regexp.MustCompile(`assert|assume|requires|ensures|invariant|pure|:|exclusive|shared|predicate`)
	for node, groups := range cmap { // Iterate over all node and comment group pairs of the command map
		for _, group := range groups {
			// Specification comments can range over multiple lines. Thus, the comments of one comment group need to be
			// appended and parsed as a whole. Therefore, `spec` is initialized as an empty string in each iteration
			spec := ""
			var lines []token.Pos
			for _, comment := range group.List { // Iterate over all comments in the current comment group
				if strings.HasPrefix(comment.Text, "//@") || strings.HasPrefix(comment.Text, "/*@") {
					spec += comment.Text // Append comment to `spec` string
					// Original line information must be preserved in order to allow for correct error messages later on
					for _, ints := range keywords.FindAllStringIndex(comment.Text, -1) {
						lines = append(lines, rg.tokenFile.Pos(rg.tokenFile.Offset(comment.Slash)+ints[0]))
					}
				}
			}
			if spec != "" {
				// Add specification information to the slice of specInfo objects
				rg.getSpecInfos(group, node, &specInfos, &racInfos, sharedVarsMap, exclusiveVarsMap, predicateInfoMap, spec, lines)
			}
		}
		delete(cmap, node) // Delete node of comment from command map
	}
	// Delete all comments (since all nodes were deleted previously). We want to avoid dangling comments in wrong places
	// after modifying the ast which is a known problem for go/ast
	rg.astFile.Comments = cmap.Filter(rg.astFile).Comments()
	return
}

// getSpecInfos parses the specification string and adds a specInfo object that holds the obtained specification asts
// and information on the node and position of the specification.
func (rg *RACGenerator) getSpecInfos(group *ast.CommentGroup, node ast.Node, specInfos *[]SpecInfo, racInfos *[]RACInfo,
	sharedVarsMap, exclusiveVarsMap *map[string]*types.Scope, predicateInfoMap *map[string]*PredicateInfo, spec string,
	lines []token.Pos) {
	specStatements := specparser.Parse(spec, rg.tokenFile.Line(node.Pos()))
	lineIndex := 0
	for _, specAST := range specStatements {
		switch specAST.(type) {
		case specparser.Spec:
			switch specAST.(specparser.Spec).SpecType() {
			case specparser.ASSERT, specparser.ASSUME:
				if rg.conf.generateAssertionChecks {
					rg.getAssertInfo(group, node, racInfos, specAST.(specparser.Spec), spec, lines[lineIndex])
				}
			case specparser.PRE:
				if rg.conf.generatePrePostChecks {
					rg.getPreCondInfo(node, racInfos, specAST.(specparser.Spec), spec, lines[lineIndex])
				}
			case specparser.POST:
				if rg.conf.generatePrePostChecks {
					rg.getPostCondInfo(node, racInfos, specAST.(specparser.Spec), spec, lines[lineIndex])
				}
			case specparser.INV:
				if rg.conf.generateInvariantsChecks {
					rg.getInvariantInfo(node, racInfos, specAST.(specparser.Spec), spec, lines[lineIndex])
				}
			}
		case specparser.Purity:
			rg.getPurityInfo(node, specInfos, spec, lines[lineIndex])
		case specparser.Label:
			rg.getLabelInfo(group, node, specInfos, spec, specAST.(specparser.Label), lines[lineIndex])
		case specparser.SharedVars:
			rg.getSharedVarsInfo(node, sharedVarsMap, exclusiveVarsMap, specAST.(specparser.SharedVars), lines[lineIndex])
		case specparser.ExclusiveVars:
			rg.getExclusiveVarsInfo(node, sharedVarsMap, exclusiveVarsMap, specAST.(specparser.ExclusiveVars), lines[lineIndex])
		case specparser.Predicate:
			rg.getPredicateInfo(node, predicateInfoMap, spec, specAST.(specparser.Predicate), lines[lineIndex])
		}
		lineIndex++
	}
}

// getAssert creates a new specInfo object that represents an assertion or assumption and appends it to the list of
// specInfo objects.
func (rg *RACGenerator) getAssertInfo(commentGroup *ast.CommentGroup, node ast.Node, racInfos *[]RACInfo,
	specAST specparser.Spec, spec string, pos token.Pos) {
	parentFunction := getParentFunction(rg.astFile, node)
	assertion := &AssertInfo{
		original:       spec,
		pos:            pos,
		associatedNode: node,
		parentFunction: parentFunction,
		condition:      specAST.Condition(),
		insertBefore:   commentGroup.End() < node.Pos(),
		isAssume:       specAST.SpecType() == specparser.ASSUME,
	}
	if parentFunction == nil {
		panic(fmt.Sprintf("Assertion '%v' at line %d cannot be outside of a function scope.",
			assertion, rg.tokenFile.Line(pos)))
	}
	*racInfos = append(*racInfos, assertion)
}

// getPreCond creates a new specInfo object that represents a precondition and appends it to the list of specInfo
// objects.
func (rg *RACGenerator) getPreCondInfo(node ast.Node, racInfos *[]RACInfo, specAST specparser.Spec, spec string, pos token.Pos) {
	associatedNode, ok := node.(*ast.FuncDecl)
	if !ok {
		panic(fmt.Sprintf("Precondition '%s' at line %d needs to be associated to a function.",
			specAST, rg.tokenFile.Line(pos)))
	}
	preCondition := &PreCondInfo{
		original:       spec,
		pos:            pos,
		associatedNode: associatedNode,
		condition:      specAST.Condition(),
	}
	*racInfos = append(*racInfos, preCondition)
}

// getPostCond creates a new specInfo object that represents a postcondition and appends it to the list of specInfo
// objects.
func (rg *RACGenerator) getPostCondInfo(node ast.Node, racInfos *[]RACInfo, specAST specparser.Spec, spec string, pos token.Pos) {
	associatedNode, ok := node.(*ast.FuncDecl)
	if !ok {
		panic(fmt.Sprintf("Postcondition '%v' at line %d needs to be associated to a function.",
			specAST, rg.tokenFile.Line(pos)))
	}
	postCondition := &PostCondInfo{
		original:       spec,
		pos:            pos,
		associatedNode: associatedNode,
		condition:      specAST.Condition(),
	}
	*racInfos = append(*racInfos, postCondition)
}

// getInvariant creates a new specInfo object that represents a (loop) invariant and appends it to the list of specInfo
// objects. Only loop invariants are permitted.
func (rg *RACGenerator) getInvariantInfo(node ast.Node, racInfos *[]RACInfo, specAST specparser.Spec, spec string, pos token.Pos) {
	parentFunction := getParentFunction(rg.astFile, node)
	invariant := &InvariantInfo{
		original:       spec,
		pos:            pos,
		associatedNode: node,
		parentFunction: parentFunction,
		condition:      specAST.Condition(),
	}
	*racInfos = append(*racInfos, invariant)
}

// getPurityInfo creates a new specInfo object that represents a purity annotation. Purity annotations are only
// permitted for function declarations.
func (rg *RACGenerator) getPurityInfo(node ast.Node, specInfos *[]SpecInfo, spec string, pos token.Pos) {
	associatedNode, ok := node.(*ast.FuncDecl)
	if !ok {
		panic(fmt.Sprintf("Purity annotation at line %d needs to be associated to a function.", rg.tokenFile.Line(pos)))
	}
	purity := &PurityInfo{
		original:       spec,
		pos:            pos,
		associatedNode: associatedNode,
	}
	*specInfos = append(*specInfos, purity)
}

// getLabelInfo creates a new specInfo object that represents a label used with old expressions and appends it to the
// list of specInfo objects.
func (rg *RACGenerator) getLabelInfo(commentGroup *ast.CommentGroup, node ast.Node, specInfos *[]SpecInfo, spec string,
	label specparser.Label, pos token.Pos) {
	labelinfo := &LabelInfo{
		original:       spec,
		pos:            pos,
		associatedNode: node,
		name:           label.Name(),
		insertBefore:   commentGroup.End() < node.Pos(),
	}
	*specInfos = append(*specInfos, labelinfo)
}

// getSharedVarsInfo iterates over all variables annotated as shared in a given specification and checks whether
//  - each variable is in scope
//  - no variable has already been declared as exclusive
// If the checks are successful, the sharedVarsMap is updated with the variable and the current scope
func (rg *RACGenerator) getSharedVarsInfo(node ast.Node, sharedVarsMap, exclusiveVarsMap *map[string]*types.Scope,
	shared specparser.SharedVars, pos token.Pos) {
	var inner *types.Scope
	if funcDecl, ok := node.(*ast.FuncDecl); ok {
		inner = rg.pkg.Scope().Innermost(funcDecl.Body.Pos())
	} else {
		inner = rg.pkg.Scope().Innermost(node.Pos())
	}
	for _, identifier := range shared.Variables() {
		// Every variable annotated as shared must be in scope of the annotation
		var obj types.Object
		if obj = inner.Lookup(identifier.Value()); obj == nil {
			if _, obj = inner.LookupParent(identifier.Value(), node.Pos()); obj == nil {
				panic(fmt.Sprintf("Shared variable annotation '%v' at line %d refers to variable '%v' that is undeclared or out of scope.",
					shared, rg.tokenFile.Line(pos), identifier))
			}
		}
		// Variables cannot be both shared and exclusive
		if _, declaredExclusive := (*exclusiveVarsMap)[identifier.Value()]; declaredExclusive {
			panic(fmt.Sprintf("Shared variable annotation '%v' at line %d refers to variable '%v' that has already been declared exclusive.",
				shared, rg.tokenFile.Line(pos), identifier))
		}
		(*sharedVarsMap)[identifier.Value()] = inner
	}
}

// getExclusiveVarsInfo iterates over all variables annotated as exclusive in a given specification and checks
// whether
//  - each variable is in scope
//  - no variable has already been declared as shared
// If the checks are successful, the exclusiveVarsMap is updated with the variable and the current scope
func (rg *RACGenerator) getExclusiveVarsInfo(node ast.Node, sharedVarsMap, exclusiveVarsMap *map[string]*types.Scope,
	exclusive specparser.ExclusiveVars, pos token.Pos) {
	var inner *types.Scope
	if funcDecl, ok := node.(*ast.FuncDecl); ok {
		inner = rg.pkg.Scope().Innermost(funcDecl.Body.Pos())
	} else {
		inner = rg.pkg.Scope().Innermost(node.Pos())
	}
	for _, identifier := range exclusive.Variables() {
		// Every variable annotated as exclusive must be in scope of the annotation
		if obj := inner.Lookup(identifier.Value()); obj == nil {
			panic(fmt.Sprintf("Exclusive variable annotation '%v' at line %d refers to variable '%v' that is undeclared or out of scope.",
				exclusive, rg.tokenFile.Line(pos), identifier))
		}
		// Variables cannot be both shared and exclusive
		if _, declaredAddressable := (*sharedVarsMap)[identifier.Value()]; declaredAddressable {
			panic(fmt.Sprintf("Exclusive variable annotation '%v' at line %d refers to variable '%v' that has already been declared shared.",
				exclusive, rg.tokenFile.Line(pos), identifier))
		}
		(*exclusiveVarsMap)[identifier.Value()] = inner
	}
}

// getPredicateInfo declares a predicate information object and inserts it into the map of predicate names to predicate
// information objects of the desugarer used by the rac generator in order to be used for later runtime check generation
// of predicate calls.
func (rg *RACGenerator) getPredicateInfo(node ast.Node, predicateInfoMap *map[string]*PredicateInfo, spec string,
	predicate specparser.Predicate, pos token.Pos) {
	name := predicate.Name().Value()
	predicateInfo := &PredicateInfo{
		original:           spec,
		pos:                pos,
		associatedNode:     node,
		originalName:       name,
		internalName:       name + fmt.Sprintf("Predicate%d", rand.Intn(100)),
		originalParameters: predicate.Parameters(),
		originalAssertion:  predicate.Assertion(),
		generateRAC:        false,
	}
	if existingPredicate, exists := (*predicateInfoMap)[name]; exists {
		panic(fmt.Sprintf("Predicate '%s' declared twice: at line %d and line %d",
			name, rg.tokenFile.Line(existingPredicate.pos), rg.tokenFile.Line(pos)))
	} else {
		(*predicateInfoMap)[name] = predicateInfo
	}
}

// desugarSortedRACInfos allows GoRAC to have deterministic behavior. Since GoRAC starts by extracting comments and
// declaring specInfo objects using the non-deterministic comment map, we might receive a different order for the list of
// specInfo objects when executing the function twice on the same input. Since this is not convenient when running unit
// tests and also might be confusing for users that take a look at the logged output, we sort the specification in
// increasing position number and only afterwards call the desugarer to generate the internal ASTs.
// Note that the alternative of first sorting the comment map and then extracting the specification was disregarded
// since the comment map might be quite large because it could contain many more comments than just the ones for the
// specification. Therefore, it seems to be more efficient to only sort the extracted specInfo objects.
func (rg *RACGenerator) desugarSortedRACInfos(racInfosUnsorted []RACInfo, predicateInfoMap *map[string]*PredicateInfo) []RACInfo {
	desugarer := NewDesugarer(rg.tokenFile, rg.pkg, rg.astFile, predicateInfoMap)
	racInfos := sortRACInfo(racInfosUnsorted)
	for _, racInfo := range racInfos {
		racInfo.ComputeDesugaredNode(desugarer)
	}
	return racInfos
}

// addRACs applies transformations to the given ast that insert runtime assertion checks for all specInfo objects.
func (rg *RACGenerator) addRACs(racInfos []RACInfo) ast.Node {
	var n ast.Node = rg.astFile
	for _, racInfo := range racInfos {
		n = astutil.Apply(rg.astFile, rg.applyAddRACs(racInfo), nil)
	}
	return n
}

// applyAddRACs represents the application function that is applied to each node of the original ast.
func (rg *RACGenerator) applyAddRACs(racInfo RACInfo) astutil.ApplyFunc {
	return func(c *astutil.Cursor) bool {
		if c.Node() == *racInfo.AssociatedNode() {
			switch racInfo.(type) {
			case *AssertInfo:
				rg.preprocessRACAssert(racInfo.(*AssertInfo), c)
			case *PreCondInfo, *PostCondInfo:
				rg.addRACPrePost(racInfo)
			case *InvariantInfo:
				rg.preprocessRACInvariant(racInfo.(*InvariantInfo), c)
			}
			return false
		}
		return true
	}
}

// preprocessRACAssert first checks whether a runtime check should be added for the given assertion specInfo object. If
// so, it generates the runtime assertion check for it and calls the function that adds the check to the ast.
func (rg *RACGenerator) preprocessRACAssert(assert *AssertInfo, c *astutil.Cursor) {
	// No RACs should be added for asserts that occur as last statements in non-void function (code after return is not executed)
	if !assert.insertBefore {
		block := assert.parentFunction.Body
		if block != nil && !isVoid(block.List) {
			if block.List[len(block.List)-1] == assert.associatedNode {
				log.Printf("No check added for assertion '%v' at line %v that is last statement in non-void function.",
					assert, rg.tokenFile.Line(assert.pos))
				rg.lastStmtAssertIgnored = true
				return
			}
		}
	}
	rac := assert.RAC(rg, NotApplicable)
	rg.addRACAssert(rac, assert, c)
}

// addRACAssert adds the runtime check that represents the assertion for the given specInfo object to the ast.
func (rg *RACGenerator) addRACAssert(rac ast.Node, assert *AssertInfo, c *astutil.Cursor) {
	defer func() {
		if recover() != nil { // Recover from astutil's panic if assertion is misplaced
			panic(fmt.Sprintf("Specification '%v' at line %d cannot be associated to a construct of type '%v'.",
				assert.String(), rg.tokenFile.Line(assert.Pos()), reflect.TypeOf(*assert.AssociatedNode())))
		}
	}()
	switch (*assert.AssociatedNode()).(type) {
	case *ast.BlockStmt:
		// Add runtime assertion check as additional statement to block
		blockstmt := (*assert.AssociatedNode()).(*ast.BlockStmt)
		list := blockstmt.List
		list = append([]ast.Stmt{rac.(ast.Stmt)}, list...)
		blockstmt.List = list
	case ast.Expr:
		// Get the statement this expression is a part of and insert the runtime assertion check after it
		stmt := getStmtForExpr(rg.astFile, (*assert.AssociatedNode()).(ast.Expr))
		insert(rg.astFile, (*stmt).(ast.Node), rac, assert.insertBefore)
	default:
		// Add runtime assertion check before or after the current node
		if assert.insertBefore {
			c.InsertBefore(rac)
		} else {
			c.InsertAfter(rac)
		}
	}
}

// addRACPrePost adds the runtime check that represents the a postcondition for the given specInfo object to
// the ast. The runtime assertion checks are included as additional nodes to the associated function body.
func (rg *RACGenerator) addRACPrePost(racInfo RACInfo) {
	insertIntoFunctionBody((*racInfo.AssociatedNode()).(*ast.FuncDecl), racInfo.RAC(rg, NotApplicable).(ast.Stmt))
}

// preprocessRACInvariant first checks whether a runtime invariant check should be added to a for- or range statement.
// Then it calls the correct function that adds the check to the ast.
// Note that adding invariants might result in small changes to be applied to the associated nodes (see documentation
// for `addRACInvariantForLoop` and `addRACInvariantRangeStmt` for details).
func (rg *RACGenerator) preprocessRACInvariant(inv *InvariantInfo, c *astutil.Cursor) {
	switch (*inv.AssociatedNode()).(type) {
	case *ast.ForStmt:
		rg.addRACInvariantForLoop(inv, c)
	case *ast.RangeStmt:
		rg.addRACInvariantRangeStmt(inv, c)
	}
}

// addRACInvariantRangeStmt adds the runtime check that represents the invariant for a range statement to the ast. The
// runtime assertion check is included as both an additional node to the associated range statement body and checks
// before and after the end of the range statement. Since the invariant's specification might reason about variables
// declared in the range statement's header, these variables are extracted and declared outside the range statement. To
// avoid shadowing of variables outside of the range statement, the modified statement and the checks are wrapped in a
// separate block.
func (rg *RACGenerator) addRACInvariantRangeStmt(inv *InvariantInfo, c *astutil.Cursor) {
	node := (*inv.AssociatedNode()).(*ast.RangeStmt)
	racInside := inv.RAC(rg, Inside).(ast.Stmt)
	list := node.Body.List
	list = append([]ast.Stmt{racInside}, list...) // Add runtime assertion check to the range statement body
	node.Body.List = list
	c.Replace(rg.getInvariantScopeBlock(inv, node)) // Replace the old node with the block containing the modified range statement and the check
}

// getInvariantScopeBlock first checks whether the given range statement contains variable declarations in its header.
// If not, it returns a block containing the original range statement and the runtime assertion checks. If declarations
// exist in the header, they are extracted and a block containing the declarations, the range statement with assignments
// instead of declarations and the runtime assertion check is returned.
func (rg *RACGenerator) getInvariantScopeBlock(inv *InvariantInfo, node *ast.RangeStmt) *ast.BlockStmt {
	var block *ast.BlockStmt
	racBefore := inv.RAC(rg, Before).(ast.Stmt)
	racAfter := inv.RAC(rg, After).(ast.Stmt)
	if node.Tok == token.DEFINE { // Check whether declarations exist in the range statement header
		var stmts []ast.Stmt // Initialize new slice of statements that will make up the body of the block that is returned
		decl := node.Key.(*ast.Ident).Obj.Decl
		lhs := decl.(*ast.AssignStmt).Lhs // The left hand side of the range statement header consists of a key and possibly a value
		key := lhs[0].(*ast.Ident)
		if key.Name != "_" { // Adds a declaration statement to the block if the key is declared
			rg.addDeclaration(key, node, &stmts)
		}
		if len(lhs) == 2 { // Adds a declaration statement to the block if the value is declared
			value := lhs[1].(*ast.Ident)
			if value.Name != "_" {
				rg.addDeclaration(value, node, &stmts)
			}
		}
		node.Tok = token.ASSIGN                          // Modify the original range statement to contain an assignment instead of a declaration
		stmts = append(stmts, racBefore, node, racAfter) // Add the modified range statement node and the runtime checks
		block = blockStmt(stmts...)
	} else {
		block = blockStmt(racBefore, node, racAfter)
	}
	return block
}

// addDeclaration adds a declaration for the variables originally declared in the header of the range statement to the
// list of statements that will make up the body of the block statement.
func (rg *RACGenerator) addDeclaration(id *ast.Ident, node *ast.RangeStmt, stmts *[]ast.Stmt) {
	inner := rg.pkg.Scope().Innermost(node.Body.Pos())
	_, obj := inner.LookupParent(id.Name, node.Body.Pos())
	if obj == nil {
		// No test coverage since this should never happen
		panic(fmt.Sprintf("Name %s used in invariant for range statement should have been previously checked by desugarer.", id.Name))
	}
	decl := declStmt(genDecl(token.VAR, []ast.Spec{valueSpec([]*ast.Ident{id}, ident(obj.Type().String()))}))
	*stmts = append(*stmts, decl)
}

// addRACInvariantForLoop adds the runtime check that represents the invariant for a for loop to the ast. The runtime
// assertion check is included as both an additional node to the associated for loop body and checks directly before and
// after the for loop. Since the invariant's specification might reason about variables declared in the for loop's
// header, these variables are extracted and declared outside the loop. To avoid shadowing of variables outside of the
// loop, the modified loop and the checks are wrapped in a separate block.
func (rg *RACGenerator) addRACInvariantForLoop(inv *InvariantInfo, c *astutil.Cursor) {
	node := (*inv.AssociatedNode()).(*ast.ForStmt)
	racBefore := inv.RAC(rg, Before).(ast.Stmt)
	racInside := inv.RAC(rg, Inside).(ast.Stmt)
	racAfter := inv.RAC(rg, After).(ast.Stmt)
	list := node.Body.List
	list = append([]ast.Stmt{racInside}, list...)
	node.Body.List = list
	var block *ast.BlockStmt
	if node.Init != nil {
		// Loop has init statement which holds a declaration. This is extracted and placed before loop.
		init := node.Init
		node.Init = nil
		block = blockStmt(init, racBefore, node, racAfter)
	} else {
		block = blockStmt(racBefore, node, racAfter)
	}
	c.Replace(block)
}

// addPredicateFunctions adds for each predicate that was called somewhere in a specification statement the function
// definition to the Go AST. In Go, all function declarations are at the top level of the AST. Therefore, the function
// definition can simply be inserted into the list of declarations of the ast file.
func (rg *RACGenerator) addPredicateFunctions(predicateInfoMap *map[string]*PredicateInfo) {
	var predicatesToAddUnsorted []RACInfo
	rootScope := rg.pkg.Scope()
	decls := rg.astFile.Decls
	for _, predicate := range *predicateInfoMap {
		if predicate.generateRAC {
			// Check whether predicate names are unique.
			// Both original and internal shouldn't collide with any other function names.
			if obj := rootScope.Lookup(predicate.originalName); obj != nil {
				panic(fmt.Sprintf("Predicate name '%s' at line %d must be unique, collides with object '%v'",
					predicate.originalName, rg.tokenFile.Line(predicate.pos), obj))
			}
			if obj := rootScope.Lookup(predicate.internalName); obj != nil {
				panic(fmt.Sprintf("Internal predicate name '%s' at line %d must be unique, collides with object '%v'",
					predicate.originalName, rg.tokenFile.Line(predicate.pos), obj))
			}
			predicatesToAddUnsorted = append(predicatesToAddUnsorted, predicate)
		}
	}
	// Sort predicate info objects in order to have deterministic behavior of GoRAC.
	predicatesToAddSorted := sortRACInfo(predicatesToAddUnsorted)
	for _, predicate := range predicatesToAddSorted {
		predicateFunc := predicate.RAC(rg, NotApplicable).(*ast.FuncDecl)
		decls = append(decls, predicateFunc)
	}
	rg.astFile.Decls = decls
}

// assignNamedReturnParameters assigns any expression that is returned in a function with named parameters to the named
// parameters before returning.
func (rg *RACGenerator) assignNamedReturnParameter() {
	var returnParameterNames []*ast.Ident
	astutil.Apply(rg.astFile, func(c *astutil.Cursor) bool {
		if funcDecl, ok := c.Node().(*ast.FuncDecl); ok {
			// If the current node is a function, we check whether it has named return parameters. If so, their names
			// are saved in the slice 'returnParameterNames'.
			if funcDecl.Type.Results != nil {
				returnParameterNames = extractReturnParameterNames(funcDecl.Type.Results)
			}
		} else if returnStmt, ok := c.Node().(*ast.ReturnStmt); ok {
			// If the current node is a return statement that returns some expressions, we add assignments that assign
			// each of the returned expressions to the belonging named parameter.
			if len(returnStmt.Results) > 0 {
				assignmentBlock := namedReturnParameterAssignmentBlock(returnParameterNames, returnStmt.Results)
				if len(assignmentBlock.List) > 0 {
					c.InsertBefore(assignmentBlock)
					// We also change the return statement such that it returns the named parameters directly
					var returnParameterExprs []ast.Expr
					for _, param := range returnParameterNames {
						returnParameterExprs = append(returnParameterExprs, param)
					}
					returnStmt.Results = returnParameterExprs
				}
			}
		}
		return true
	}, nil)
}

// extractReturnParameters iterates over the list of return parameters and, if they are named, saves the identifiers
// refering to the names in the list 'names' which is finally returned.
func extractReturnParameterNames(returnParams *ast.FieldList) []*ast.Ident {
	var names []*ast.Ident
	for _, param := range returnParams.List {
		if param.Names != nil {
			// Parameters are named and we add the corresponding identifier objects to our list of return parameters
			for _, identifier := range param.Names {
				names = append(names, identifier)
			}
		}
	}
	return names
}

// namedReturnParameterAssignmentBlock iterates over all identifiers referring to a named parameter and creates an
// assignment of the belonging returned expression to this parameter. The function returns a block statement that is
// made up of all the assignments.
func namedReturnParameterAssignmentBlock(returnParameters []*ast.Ident, returnedExpressions []ast.Expr) *ast.BlockStmt {
	// If the returned expressions are a call to another function that might return multiple parameters, this is handled
	// separately. E.g. in a scenario such as
	// 		func foo() (int, int) { ... }
	// 		func bar() (x int, y int) { return foo() }
	// the function bar is changed to
	// 		func bar() (x int, y int) {
	// 			x, y = foo()
	// 			return x, y
	// 		}
	var assignStmts []ast.Stmt
	if len(returnParameters) > 1 && len(returnedExpressions) == 1 {
		var paramExprs []ast.Expr
		for _, param := range returnParameters {
			paramExprs = append(paramExprs, param)
		}
		stmt := assignStmt(paramExprs, []ast.Expr{returnedExpressions[0]}, token.ASSIGN)
		assignStmts = append(assignStmts, stmt)
	} else {
		for i, param := range returnParameters {
			stmt := assignStmt([]ast.Expr{param}, []ast.Expr{returnedExpressions[i]}, token.ASSIGN)
			assignStmts = append(assignStmts, stmt)
		}
	}
	return blockStmt(assignStmts...)
}

// addFmtImport adds the 'fmt' package to the imports of the ast file if it is not already present.
func (rg *RACGenerator) addFmtImport() {
	var imports *ast.GenDecl
	decls := rg.astFile.Decls
	for _, decl := range decls {
		switch decl.(type) {
		case *ast.GenDecl:
			genDecl := decl.(*ast.GenDecl)
			if genDecl.Tok == token.IMPORT {
				imports = genDecl
				break
			}
		}
	}
	if imports != nil {
		hasFmt := false
		for _, spec := range imports.Specs {
			switch spec.(type) {
			case *ast.ImportSpec:
				importSpec := spec.(*ast.ImportSpec)
				if importSpec.Path.Value == "\"fmt\"" {
					hasFmt = true
					break
				}
			}
		}
		if !hasFmt {
			imports.Specs = append(imports.Specs, importSpec("\"fmt\""))
		}
	} else {
		decls = append([]ast.Decl{genDecl(token.IMPORT, []ast.Spec{importSpec("\"fmt\"")})}, decls...)
	}
	rg.astFile.Decls = decls
}
