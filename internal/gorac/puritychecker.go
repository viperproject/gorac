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
	"golang.org/x/tools/go/ast/astutil"
	"strings"
)

// PurityChecker encapsulates the information needed to check the correctness of purity annotations.
type PurityChecker struct {
	tokenFile *token.File
	astFile   *ast.File
	specInfos *[]SpecInfo
	racInfos  *[]RACInfo
}

// NewPurityChecker returns a new Purity Checker object.
func NewPurityChecker(tokenFile *token.File, astFile *ast.File, specInfos *[]SpecInfo, racInfos *[]RACInfo) *PurityChecker {
	return &PurityChecker{
		tokenFile: tokenFile,
		astFile:   astFile,
		specInfos: specInfos,
		racInfos:  racInfos,
	}
}

// checkPurityAnnotations checks whether functions with purity annotations are actually pure.
// GoRAC defines pureness as follows:
// - the function must have exactly one return parameter
// - the function's body must be pure, i.e.
//		- the body must consist of a single return statement
// 		- the return statement returns a pure expression, i.e.
//				- an expression e is pure if it matches one of the following cases
//						- e is an integer, bool or nil
//						- e is an identifier (variable)
//						- e is a composite literal
//						- e is a dot notation and its base is pure
//						- e is an index expression and its structure is pure
//						- e is an unary expression and its operand is pure
//						- e is a binary expression and both its operands are pure
//						- e is a function call and both the function and the parameters of the call are pure
// - all postconditions for the functions must be pure expressions (no restrictions apply for preconditions)
// For now function literals, dereferences and any other expressions not covered above are considered impure.
// The built-in functions "len" and "cap" are also considered pure.
func (pc *PurityChecker) check() {
	pc.checkSpecInfos()
	pc.checkRACInfos()
}

// checkSpecInfos checks for all specInfo objects whether they are purity annotations. If so, the function that the pure
// annotation belongs to is checked further. The checks follow the purity definition from the documentation of the
// check-function. If the specInfo object is not a pure annotation, it is skipped.
func (pc *PurityChecker) checkSpecInfos() {
	for _, specInfo := range *pc.specInfos {
		if _, ok := specInfo.(*PurityInfo); ok {
			f, _ := (*specInfo.AssociatedNode()).(*ast.FuncDecl)
			if !pureReturn(f) {
				panic(fmt.Sprintf("At line %v, pure function '%s' should have exactly one return parameter, found %d\n",
					pc.tokenFile.Line(specInfo.Pos()), f.Name.Name, len(f.Type.Results.List)))
			}
			if err := pureBody(f.Body); err != nil {
				panic(fmt.Sprintf("At line %v, the pure function '%s' is not pure: %s\n",
					pc.tokenFile.Line(specInfo.Pos()), f.Name.Name, err.Error()))
			}
			if impurePostcondition := pc.purePostConditions(specInfo); impurePostcondition != nil {
				panic(fmt.Sprintf("At line %v, pure function '%s' has impure postcondition '%v'.\n",
					pc.tokenFile.Line(specInfo.Pos()), f.Name.Name, *impurePostcondition))
			}
		}
	}
}

// checkRACInfos iterates over all RACInfo objects and extracts function names used in the specification. For each of
// the function calls, it is checked whether the called function is pure. Note that the built-in functions "len" and
// "cap" are also considered pure.
func (pc *PurityChecker) checkRACInfos() {
	for _, racInfo := range *pc.racInfos {
		funcNames := racInfo.DesugaredNode().extractFunctionNames()
		for _, name := range funcNames {
			if name == "len" || name == "cap" {
				continue
			}
			pc.checkFunctionCallPurity(name, racInfo)
		}
	}
}

// checkFunctionCallPurity walks the Go AST in order to find a function that has the specified name. It then checks
// whether this function is annotated as pure.
func (pc *PurityChecker) checkFunctionCallPurity(funcName string, specInfo SpecInfo) {
	astutil.Apply(pc.astFile, func(c *astutil.Cursor) bool {
		if fun, ok := c.Node().(*ast.FuncDecl); ok {
			if fun.Name.Name == funcName {
				if !strings.Contains(fun.Doc.Text(), "pure") {
					panic(fmt.Sprintf("At line %v in specification '%v' the called function '%s' is not pure.\n",
						pc.tokenFile.Line(specInfo.Pos()), specInfo, fun.Name.Name))
				} else {
					return false // returning false stops the AST walk
				}
			}
		}
		return true
	}, nil)
}

// pureReturn checks whether the associated function of the purity assertion has exactly one return parameter.
func pureReturn(f *ast.FuncDecl) bool {
	if len(f.Type.Results.List) != 1 {
		return false
	}
	return true
}

// pureBody checks whether the associated function of the purity assertion has a pure body. A function body
// is considered pure if it consists of a single return statement that returns a pure expression.
func pureBody(body *ast.BlockStmt) error {
	if len(body.List) == 1 {
		returnStmt, ok := body.List[0].(*ast.ReturnStmt)
		if ok {
			return isPureGoExpression(returnStmt.Results[0]) // can be 0 because of previous `pureReturn` check
		}
	}
	return fmt.Errorf("the body should consist of a single return statement")
}

// isPureGoExpression checks whether a given expression is pure. Different types of expressions are differentiated and if
// a case that is allowed is matched, the function returns nil. For now, function literals, type assertions, slice
// expressions  and any other expressions not covered by a case below are considered impure. In these cases an error is
// returned.
func isPureGoExpression(expr ast.Expr) error {
	switch expr.(type) {
	case *ast.ParenExpr:
		paren := expr.(*ast.ParenExpr)
		return isPureGoExpression(paren.X)
	case *ast.BasicLit:
		return nil
	case *ast.Ident:
		ident := expr.(*ast.Ident)
		if ident.Obj == nil {
			return nil // For example field selector
		}
		switch ident.Obj.Kind {
		case ast.Con, ast.Typ, ast.Var:
			return nil
		case ast.Fun:
			funDecl := ident.Obj.Decl.(*ast.FuncDecl)
			if strings.Contains(funDecl.Doc.Text(), "pure") {
				return nil
			}
		}
	case *ast.CallExpr:
		call := expr.(*ast.CallExpr)
		if isPureGoExpression(call.Fun) == nil {
			if pureGoExprList(call.Args) {
				return nil
			}
		}
	case *ast.CompositeLit:
		composite := expr.(*ast.CompositeLit)
		if isPureGoExpression(composite.Type) == nil {
			if pureGoExprList(composite.Elts) {
				return nil
			}
		}
	case *ast.IndexExpr:
		index := expr.(*ast.IndexExpr)
		if isPureGoExpression(index.X) == nil {
			return nil
		}
	case *ast.SelectorExpr:
		selector := expr.(*ast.SelectorExpr)
		if isPureGoExpression(selector.X) == nil && isPureGoExpression(selector.Sel) == nil {
			return nil
		}
	case *ast.UnaryExpr:
		unary := expr.(*ast.UnaryExpr)
		return isPureGoExpression(unary.X)
	case *ast.BinaryExpr:
		binary := expr.(*ast.BinaryExpr)
		if isPureGoExpression(binary.X) == nil && isPureGoExpression(binary.Y) == nil {
			return nil
		}
	}
	return fmt.Errorf("the expression that is returned must be pure")
}

// pureGoExprList checks all expressions of the list provided for pureness. If all of them are pure, true is returned,
// otherwise false.
func pureGoExprList(exprList []ast.Expr) bool {
	if exprList != nil {
		for _, expr := range exprList {
			if isPureGoExpression(expr) != nil {
				return false
			}
		}
	}
	return true
}

// purePostConditions checks for a given purity annotation whether the function that it is attached to has only pure
// postconditions. For this, all specification info objects are iterated and checked whether we have a postcondition
// for the pure function. If one is found, it's condition is checked for purity.
func (pc *PurityChecker) purePostConditions(purity SpecInfo) *PostCondInfo {
	for _, specInfo := range *pc.specInfos {
		switch specInfo.(type) {
		case *PostCondInfo:
			postCondition := specInfo.(*PostCondInfo)
			if *postCondition.AssociatedNode() == *purity.AssociatedNode() {
				if !pc.isPureSpecExpression(postCondition.condition, postCondition.pos, specInfo) {
					return postCondition
				}
			}
		}
	}
	return nil
}

// isPureSpecExpression checks for a given specparser expression whether it is pure. The purity definition for specparser
// expressions is the same as for Go expressions.
func (pc *PurityChecker) isPureSpecExpression(expr specparser.Node, pos token.Pos, specInfo SpecInfo) bool {
	switch expr.(type) {
	case *specparser.Integer, *specparser.Identifier:
		return true
	case *specparser.Call:
		call := expr.(*specparser.Call)
		if ident, ok := call.Function().(*Identifier); ok {
			pc.checkFunctionCallPurity(ident.value, specInfo)
			return pc.pureSpecExprList(call.Parameters(), pos, specInfo)
		} else {
			return pc.isPureSpecExpression(call.Function(), pos, specInfo) && pc.pureSpecExprList(call.Parameters(), pos, specInfo)
		}
	case *specparser.ArrayLiteral:
		arrayLiteral := expr.(*specparser.ArrayLiteral)
		if pc.isPureSpecExpression(arrayLiteral.Type(), pos, specInfo) {
			var valuesToCheck []specparser.Node
			for _, tuple := range arrayLiteral.Values() {
				valuesToCheck = append(valuesToCheck, tuple[0])
			}
			if pc.pureSpecExprList(valuesToCheck, pos, specInfo) {
				return true
			}
		}
	case *specparser.ArrayType:
		arrayType := expr.(*specparser.ArrayType)
		return pc.isPureSpecExpression(arrayType.Type(), pos, specInfo) && pc.isPureSpecExpression(arrayType.Length(), pos, specInfo)
	case *specparser.StructLiteral:
		structLiteral := expr.(*specparser.StructLiteral)
		if pc.isPureSpecExpression(structLiteral.Identifier(), pos, specInfo) {
			var valuesToCheck []specparser.Node
			for _, tuple := range structLiteral.Values() {
				valuesToCheck = append(valuesToCheck, tuple[0])
			}
			if pc.pureSpecExprList(valuesToCheck, pos, specInfo) {
				return true
			}
		}
	case *specparser.SquareBracket:
		squareBracket := expr.(*specparser.SquareBracket)
		return pc.isPureSpecExpression(squareBracket.Structure(), pos, specInfo)
	case *specparser.DotNotation:
		dotNotation := expr.(*specparser.DotNotation)
		return pc.isPureSpecExpression(dotNotation.Structure(), pos, specInfo) && pc.isPureSpecExpression(dotNotation.Field(), pos, specInfo)
	case specparser.Unary:
		unary := expr.(*specparser.Unary)
		return pc.isPureSpecExpression(unary.Operand(), pos, specInfo)
	case *specparser.Binary:
		binary := expr.(*specparser.Binary)
		return pc.isPureSpecExpression(binary.Left(), pos, specInfo) && pc.isPureSpecExpression(binary.Right(), pos, specInfo)
	case *specparser.Ternary:
		ternary := expr.(*specparser.Ternary)
		return pc.isPureSpecExpression(ternary.Condition(), pos, specInfo) &&
			pc.isPureSpecExpression(ternary.PositiveBranch(), pos, specInfo) &&
			pc.isPureSpecExpression(ternary.NegativeBranch(), pos, specInfo)
	}
	return false
}

// pureSpecExprList checks for a given list of specification expressions whether they are all pure.
func (pc *PurityChecker) pureSpecExprList(list []specparser.Node, pos token.Pos, specInfo SpecInfo) bool {
	for _, node := range list {
		if !pc.isPureSpecExpression(node, pos, specInfo) {
			return false
		}
	}
	return true
}
