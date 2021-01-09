// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"go/ast"
	"go/token"
)

// Helper functions to create various ast.Node objects.

func ident(name string) *ast.Ident {
	return &ast.Ident{
		NamePos: 0,
		Name:    name,
		Obj:     nil,
	}
}

func declStmt(decl ast.Decl) *ast.DeclStmt {
	return &ast.DeclStmt{
		Decl: decl,
	}
}

func genDecl(tok token.Token, spec []ast.Spec) *ast.GenDecl {
	return &ast.GenDecl{
		Doc:    nil,
		TokPos: 0,
		Tok:    tok,
		Lparen: 0,
		Specs:  spec,
		Rparen: 0,
	}
}

func valueSpec(names []*ast.Ident, type_ ast.Expr) *ast.ValueSpec {
	return &ast.ValueSpec{
		Doc:     nil,
		Names:   names,
		Type:    type_,
		Values:  nil,
		Comment: nil,
	}
}

func assignStmt(lhs, rhs []ast.Expr, tok token.Token) *ast.AssignStmt {
	return &ast.AssignStmt{
		Lhs:    lhs,
		TokPos: 0,
		Tok:    tok,
		Rhs:    rhs,
	}
}

func basicLit(value string, kind token.Token) *ast.BasicLit {
	return &ast.BasicLit{
		ValuePos: 0,
		Kind:     kind,
		Value:    value,
	}
}

func compositeLit(type_ ast.Expr, elts []ast.Expr) *ast.CompositeLit {
	return &ast.CompositeLit{
		Type:       type_,
		Lbrace:     0,
		Elts:       elts,
		Rbrace:     0,
		Incomplete: false,
	}
}

func keyValueExpr(key, value ast.Expr) *ast.KeyValueExpr {
	return &ast.KeyValueExpr{
		Key:   key,
		Colon: 0,
		Value: value,
	}
}

func arrayType(len, elt ast.Expr) *ast.ArrayType {
	return &ast.ArrayType{
		Lbrack: 0,
		Len:    len,
		Elt:    elt,
	}
}

func indexExpr(x, index ast.Expr) *ast.IndexExpr {
	return &ast.IndexExpr{
		X:      x,
		Lbrack: 0,
		Index:  index,
		Rbrack: 0,
	}
}

func selectorExpr(x ast.Expr, sel *ast.Ident) *ast.SelectorExpr {
	return &ast.SelectorExpr{
		X:   x,
		Sel: sel,
	}
}

func starExpr(x ast.Expr) *ast.StarExpr {
	return &ast.StarExpr{
		Star: 0,
		X:    x,
	}
}

func unaryExpr(x ast.Expr, op token.Token) *ast.UnaryExpr {
	return &ast.UnaryExpr{
		OpPos: 0,
		Op:    op,
		X:     x,
	}
}

func binaryExpr(x, y ast.Expr, op token.Token) *ast.BinaryExpr {
	return &ast.BinaryExpr{
		X:     x,
		Op:    op,
		OpPos: 0,
		Y:     y,
	}
}

func blockStmt(list ...ast.Stmt) *ast.BlockStmt {
	return &ast.BlockStmt{
		Lbrace: 0,
		List:   list,
		Rbrace: 0,
	}
}

func ifStmt(init, else_ ast.Stmt, cond ast.Expr, body *ast.BlockStmt) *ast.IfStmt {
	return &ast.IfStmt{
		If:   0,
		Init: init,
		Cond: cond,
		Body: body,
		Else: else_,
	}
}

func exprStmt(x ast.Expr) *ast.ExprStmt {
	return &ast.ExprStmt{
		X: x,
	}
}

func callExpr(fun ast.Expr, args ...ast.Expr) *ast.CallExpr {
	return &ast.CallExpr{
		Fun:      fun,
		Lparen:   0,
		Args:     args,
		Ellipsis: 0,
		Rparen:   0,
	}
}

func funcType(params, results *ast.FieldList) *ast.FuncType {
	return &ast.FuncType{
		Func:    0,
		Params:  params,
		Results: results,
	}
}

func funcLit(body ast.BlockStmt, type_ *ast.FuncType) *ast.FuncLit {
	return &ast.FuncLit{
		Type: type_,
		Body: &body,
	}
}

func funcDecl(name *ast.Ident, body ast.BlockStmt, type_ *ast.FuncType) *ast.FuncDecl {
	return &ast.FuncDecl{
		Doc:  nil,
		Recv: nil, // for methods this should be set too
		Name: name,
		Type: type_,
		Body: &body,
	}
}

func deferStmt(body ast.BlockStmt) *ast.DeferStmt {
	return &ast.DeferStmt{
		Defer: 0,
		Call:  callExpr(funcLit(body, funcType(nil, nil))),
	}
}

func _panic(expr ...ast.Expr) *ast.ExprStmt {
	return &ast.ExprStmt{X: &ast.CallExpr{
		Fun: &ast.Ident{
			Name: "panic",
		},
		Args: expr,
	}}
}

func importSpec(value string) *ast.ImportSpec {
	return &ast.ImportSpec{
		Doc:     nil,
		Name:    nil,
		Path:    basicLit(value, token.STRING),
		Comment: nil,
		EndPos:  0,
	}
}

func forStmt(init, post ast.Stmt, cond ast.Expr, body *ast.BlockStmt) *ast.ForStmt {
	return &ast.ForStmt{
		For:  0,
		Init: init,
		Cond: cond,
		Post: post,
		Body: body,
	}
}

func rangeStmt(key, value, x ast.Expr, tok token.Token, body *ast.BlockStmt) *ast.RangeStmt {
	return &ast.RangeStmt{
		For:    0,
		Key:    key,
		Value:  value,
		TokPos: 0,
		Tok:    tok,
		X:      x,
		Body:   body,
	}
}

func incDecStmt(x ast.Expr, tok token.Token) *ast.IncDecStmt {
	return &ast.IncDecStmt{
		X:      x,
		TokPos: 0,
		Tok:    tok,
	}
}

func returnStmt(results []ast.Expr) *ast.ReturnStmt {
	return &ast.ReturnStmt{
		Return:  0,
		Results: results,
	}
}

func fieldList(fields []*ast.Field) *ast.FieldList {
	return &ast.FieldList{
		Opening: 0,
		List:    fields,
		Closing: 0,
	}
}

func field(type_ ast.Expr, names ...*ast.Ident) *ast.Field {
	return &ast.Field{
		Doc:     nil,
		Names:   names,
		Type:    type_,
		Tag:     nil,
		Comment: nil,
	}
}
