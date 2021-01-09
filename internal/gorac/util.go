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
	"golang.org/x/tools/go/ast/astutil"
	"math/rand"
	"strings"
)

// getParentFunction returns the AST function node in whose body the given node is contained.
func getParentFunction(astFile *ast.File, node ast.Node) *ast.FuncDecl {
	var parentFunction *ast.FuncDecl
	astutil.Apply(astFile, func(c *astutil.Cursor) bool {
		if c.Node() == node {
			parent := c.Parent()
			parentConv, ok := parent.(*ast.FuncDecl)
			if parent != nil && !ok {
				parentFunction = getParentFunction(astFile, parent)
				return false
			}
			parentFunction = parentConv
		}
		return true
	}, nil)
	return parentFunction
}

// insert inserts the given node before (if before is true) or after (if before is false) the given place.
func insert(astFile *ast.File, place ast.Node, node ast.Node, before bool) {
	astutil.Apply(astFile, func(c *astutil.Cursor) bool {
		if c.Node() == place {
			if before {
				c.InsertBefore(node)
			} else {
				c.InsertAfter(node)
			}
		}
		return true
	}, nil)
}

// getStmtForExpr returns the statement that a given expression is a part of or nil, if no such statement exists.
func getStmtForExpr(astFile *ast.File, expr ast.Expr) *ast.Stmt {
	var stmt *ast.Stmt
	astutil.Apply(astFile, func(c *astutil.Cursor) bool {
		if currStmt, ok := c.Node().(ast.Stmt); ok {
			stmt = &currStmt
		}
		if c.Node() == expr {
			return false
		}
		return true
	}, nil)
	return stmt
}

// insertIntoFunctionBody inserts a given statement into the body of the given function declaration. The statement
// is added at the beginning of the function.
func insertIntoFunctionBody(f *ast.FuncDecl, stmt ast.Stmt) {
	list := f.Body.List
	list = append([]ast.Stmt{stmt}, list...)
	f.Body.List = list
}

// isVoid checks whether a given slice of statements that make up a block includes a return statement. If a return
// exists, it returns false, if not, the function is void and true is returned.
func isVoid(block []ast.Stmt) bool {
	for _, stmt := range block {
		switch stmt.(type) {
		case *ast.ReturnStmt:
			return false
		case *ast.BlockStmt:
			if !isVoid(stmt.(*ast.BlockStmt).List) {
				return false
			}
		case *ast.RangeStmt:
			body := stmt.(*ast.RangeStmt).Body
			if body != nil && !isVoid(body.List) {
				return false
			}
		case *ast.ForStmt:
			body := stmt.(*ast.ForStmt).Body
			if body != nil && !isVoid(body.List) {
				return false
			}
		case *ast.IfStmt:
			ifStmt := stmt.(*ast.IfStmt)
			if ifStmt.Body != nil && !isVoid(ifStmt.Body.List) {
				return false
			}
			if ifStmt.Else != nil {
				if !isVoid([]ast.Stmt{ifStmt.Else}) {
					return false
				}
			}
		case *ast.SelectStmt:
			body := stmt.(*ast.SelectStmt).Body
			if body != nil && !isVoid(body.List) {
				return false
			}
		case *ast.SwitchStmt:
			body := stmt.(*ast.SwitchStmt).Body
			if body != nil && !isVoid(body.List) {
				return false
			}
		case *ast.TypeSwitchStmt:
			body := stmt.(*ast.TypeSwitchStmt).Body
			if body != nil && !isVoid(body.List) {
				return false
			}
		case *ast.CaseClause:
			body := stmt.(*ast.CaseClause).Body
			if body != nil && !isVoid(body) {
				return false
			}
		case *ast.CommClause:
			body := stmt.(*ast.CommClause).Body
			if body != nil && !isVoid(body) {
				return false
			}
		}
	}
	return true
}

// sortRACInfo sorts a list of SpecInfo objects in increasing order of their starting positions.
func sortRACInfo(racInfos []RACInfo) []RACInfo {
	slice := make([]interface{}, len(racInfos))
	for i := range slice {
		slice[i] = racInfos[i]
	}
	slice = sort(slice, func(i interface{}) int { return int(i.(RACInfo).Pos()) })
	for i := range slice {
		racInfos[i] = slice[i].(RACInfo)
	}
	return racInfos
}

// sort sorts a given slice of interfaces using the provided compare function. The underlying algorithm corresponds
// to quicksort.
func sort(slice []interface{}, compareFunction func(interface{}) int) []interface{} {
	if len(slice) < 2 {
		return slice
	}
	left, right := 0, len(slice)-1
	pivot := rand.Int() % len(slice)
	slice[pivot], slice[right] = slice[right], slice[pivot]
	for i := range slice {
		if compareFunction(slice[i]) < compareFunction(slice[right]) {
			slice[left], slice[i] = slice[i], slice[left]
			left++
		}
	}
	slice[left], slice[right] = slice[right], slice[left]
	sort(slice[:left], compareFunction)
	sort(slice[left+1:], compareFunction)
	return slice
}

// catchPanicWrapper wraps a given AST statement node that represents a runtime assertion checks into a function call
// that holds a defer statement which catches any panic that occurs when executing the runtime assertion check. I.e.
// func() {
//		defer func() {
//			if err := recover(); err != nil {
//				panic(fmt.Sprintf("Line X, Specification 'Y': %v", err))
//			}
//		}()
//		<RAC for specification Y>
//	}()
func catchPanicWrapper(rac ast.Stmt, panicString string) ast.Stmt {
	errIdent := ident("err")
	nilIdent := ident("nil")
	fmtIdent := ident("fmt")
	printIdent := ident("Sprintf")
	panicStringLit := basicLit("\""+panicString+" %v\"", token.STRING)

	body := blockStmt(_panic(callExpr(selectorExpr(fmtIdent, printIdent), panicStringLit, errIdent)))
	init := assignStmt([]ast.Expr{errIdent}, []ast.Expr{callExpr(ident("recover"))}, token.DEFINE)
	cond := binaryExpr(errIdent, nilIdent, token.NEQ)
	ifStmt := ifStmt(init, nil, cond, body)

	deferStmt := deferStmt(*blockStmt(ifStmt))
	return exprStmt(callExpr(funcLit(*blockStmt(deferStmt, rac), funcType(nil, nil))))
}

// filterVariableCheck checks for a given variable name whether it is unbounded. If so, the name is not replaced.
// Otherwise the name is replaced and the statement that was given will be wrapped into an if-statement filtering for
// the original variable.
func filterVariableCheck(varName string, stmt ast.Stmt, unboundedVars *map[string]*Identifier) (bool, string, ast.Stmt) {
	newName := varName
	newStmt := stmt
	isFiltered := false
	if _, ok := (*unboundedVars)[varName]; ok {
		delete(*unboundedVars, varName)
	} else {
		newName = fmt.Sprintf("%s%d", varName, rand.Intn(100))
		newStmt = ifStmt(nil, nil, binaryExpr(ident(newName), ident(varName), token.EQL), blockStmt(stmt))
		isFiltered = true
	}
	return isFiltered, newName, newStmt
}

// copyMap copies a list of strings to identifier pointers into a new list.
func copyMap(originalMap *map[string]*Identifier) *map[string]*Identifier {
	newMap := make(map[string]*Identifier)
	for name, identifier := range *originalMap {
		newMap[name] = identifier
	}
	return &newMap
}

// getFreeVars computes the set unbounded/bounded in order to receive the set of free variables.
func getFreeVars(unbounded, bounded *map[string]*Identifier) *map[string]*Identifier {
	free := map[string]*Identifier{}
	for name, identifier := range *unbounded {
		if _, ok := (*bounded)[name]; !ok {
			free[name] = identifier
		}
	}
	return &free
}

// addBooleanDomains wraps a stmt that is used as the inner most check for quantifiers into for loops iterating over
// the two possible truth values (true and false) for each boolean quantified variable that has no domain.
func addBooleanDomains(stmt ast.Stmt, quantifiedVars []Identifier, domain *Domain) ast.Stmt {
	booleanArrayType := arrayType(basicLit("2", token.INT), ident("bool"))
	booleanValues := compositeLit(booleanArrayType, []ast.Expr{ident("true"), ident("false")})
	emptyKey := ident("_")
	boundedVars := map[string]*Identifier{}
	if domain != nil {
		domain.extractQuantifiedVars(&boundedVars)
	}
	for _, quantifiedVar := range quantifiedVars {
		if _, ok := boundedVars[quantifiedVar.value]; !ok &&
			(quantifiedVar.type_ == types.Typ[types.UntypedBool] ||
				quantifiedVar.type_ == types.Typ[types.Bool]) {
			stmt = rangeStmt(emptyKey, ident(quantifiedVar.value), booleanValues, token.DEFINE, blockStmt(stmt))
		}
	}
	return stmt
}

// boundIsQuantifiedVars checks whether for a given list of identifiers used in domain bounds, there is an identifier
// which is also a quantified variable from a given map of quantified variable identifiers. If such an identifier is
// found, it is returned. Otherwise, the function returns nil.
func boundIsQuantifiedVar(boundIdentifier []*Identifier, quantifiedVars map[string]*Identifier) *Identifier {
	for _, identifier := range boundIdentifier {
		if _, ok := quantifiedVars[identifier.value]; ok {
			return identifier
		}
	}
	return nil
}

// intersection computes the intersection between two given maps of identifier names and their belonging identifier
// pointers.
func intersection(rightMap map[string]*Identifier, leftMap map[string]*Identifier) map[string]*Identifier {
	intersection := make(map[string]*Identifier)
	for name, identifier := range rightMap {
		if _, ok := leftMap[name]; ok {
			intersection[name] = identifier
		}
	}
	return intersection
}

// getTypeIdentifier returns the string representing a struct type. Since types of structs are written as
// "path/to/declaration.structname" and we want to only have "structname" as an identifier, we need to split the string
// and get the last part.
func getTypeIdentifier(type_ types.Type) string {
	typeString := strings.Replace(type_.String(), "untyped ", "", -1)
	typeStringParts := strings.Split(typeString, ".")
	typeIdentifier := typeStringParts[len(typeStringParts)-1]
	if strings.Contains(typeString, "*") && !strings.Contains(typeIdentifier, "*") {
		return "*" + typeIdentifier
	} else {
		return typeIdentifier
	}
}
