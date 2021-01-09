// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package specparser

import (
	"fmt"
	"github.com/antlr/antlr4/runtime/Go/antlr"
)

// SpecGrammarVisitor implements the visiting of all ANTLR ast nodes. For each node the respective specification
// ast node is returned.

type SpecTreeVisitor struct {
	antlr.ParseTreeVisitor
}

func NewSpecGrammarVisitor() SpecGrammarVisitor {
	return &SpecTreeVisitor{
		ParseTreeVisitor: &BaseSpecGrammarVisitor{},
	}
}

func (v *SpecTreeVisitor) Visit(tree antlr.ParseTree) interface{} {
	return tree.Accept(v)
}

func (v *SpecTreeVisitor) VisitChildren(node antlr.RuleNode) interface{} {
	var children []interface{}
	for _, child := range node.GetChildren() {
		children = append(children, child.(antlr.ParseTree).Accept(v))
	}
	return children
}

func (v *SpecTreeVisitor) VisitStart(ctx *StartContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[0]
}

func (v *SpecTreeVisitor) VisitSpecification(ctx *SpecificationContext) interface{} {
	var statements []Node
	children := v.VisitChildren(ctx).([]interface{})
	for _, child := range children {
		statements = append(statements, child.(Node))
	}
	return statements
}

func (v *SpecTreeVisitor) VisitSpecStatement(ctx *SpecStatementContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.SpecStatement() != nil {
		return children[1]
	} else if ctx.Assertion() != nil {
		statement := Spec{
			condition: v.VisitChildren(ctx).([]interface{})[1].(Node),
		}
		switch ctx.kind.GetTokenType() {
		case SpecGrammarLexerASSERT:
			statement.specType = ASSERT
		case SpecGrammarLexerASSUME:
			statement.specType = ASSUME
		case SpecGrammarLexerPRE:
			statement.specType = PRE
		case SpecGrammarLexerPOST:
			statement.specType = POST
		case SpecGrammarLexerINV:
			statement.specType = INV
		default:
			panic(fmt.Sprintf("Invalid spec type for spec node with condition %v.", statement.condition))
		}
		return statement
	} else { // ctx.Purity() != nil
		return children[0]
	}
}

func (v *SpecTreeVisitor) VisitAssertion(ctx *AssertionContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.LPAREN() != nil {
		return children[1]
	} else if ctx.FORALL() != nil && ctx.Domain() != nil {
		domain := children[4].(Domain)
		return UnivQuantifier{
			quantifiedVars: children[1].([][]Node),
			domain:         &domain,
			condition:      children[6].(Node),
		}
	} else if ctx.EXISTS() != nil && ctx.Domain() != nil {
		domain := children[4].(Domain)
		return ExistQuantifier{
			quantifiedVars: children[1].([][]Node),
			domain:         &domain,
			condition:      children[6].(Node),
		}
	} else if ctx.FORALL() != nil {
		return UnivQuantifier{
			quantifiedVars: children[1].([][]Node),
			condition:      children[4].(Node),
		}
	} else if ctx.EXISTS() != nil {
		return ExistQuantifier{
			quantifiedVars: children[1].([][]Node),
			condition:      children[4].(Node),
		}
	} else if ctx.kind != nil {
		switch ctx.kind.GetTokenType() {
		case SpecGrammarLexerNOT:
			return Unary{
				operator: ctx.kind.GetText(),
				operand:  children[1].(Node),
			}
		case SpecGrammarLexerAND, SpecGrammarLexerOR:
			return Binary{
				operator: ctx.kind.GetText(),
				left:     children[0].(Node),
				right:    children[2].(Node),
			}
		case SpecGrammarLexerIMPLIES:
			negatedLeft := Unary{
				operator: "!",
				operand:  children[0].(Node),
			}
			return Binary{
				operator: "==>",
				left:     negatedLeft,
				right:    children[2].(Node),
			}
		case SpecGrammarLexerQUESTION:
			return Ternary{
				condition:      children[0].(Node),
				positiveBranch: children[2].(Node),
				negativeBranch: children[4].(Node),
			}
		}
	} else if ctx.Expression() != nil {
		return children[0]
	}
	panic(fmt.Sprintf("Invalid assertion %v.", ctx))
}

func (v *SpecTreeVisitor) VisitExpression(ctx *ExpressionContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.Expression() != nil {
		return children[1]
	} else {
		return children[0]
	}
}

func (v *SpecTreeVisitor) VisitBinary(ctx *BinaryContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.Unary() != nil {
		return children[0]
	} else {
		return Binary{
			operator: ctx.kind.GetText(),
			left:     children[0].(Node),
			right:    children[2].(Node),
		}
	}
}

func (v *SpecTreeVisitor) VisitPrimary(ctx *PrimaryContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.Operand() != nil {
		return children[0]
	} else if ctx.Squarebracket() != nil {
		return SquareBracket{
			structure: children[0].(Node),
			index:     children[1].(Node),
		}
	} else if ctx.Dotnotation() != nil {
		return DotNotation{
			structure: children[0].(Node),
			field:     children[1].(Node),
		}
	} else if ctx.ExpressionList() != nil {
		return Call{
			function:   children[0].(Node),
			parameters: children[2].([]Node),
		}
	} else {
		return Call{
			function:   children[0].(Node),
			parameters: []Node{},
		}
	}
}

func (v *SpecTreeVisitor) VisitUnary(ctx *UnaryContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.Primary() != nil {
		return children[0]
	} else {
		switch ctx.kind.GetTokenType() {
		case SpecGrammarLexerSTAR:
			return Dereference{
				operand: children[1].(Node),
			}
		default:
			return Unary{
				operator: ctx.kind.GetText(),
				operand:  children[1].(Node),
			}
		}
	}
}

func (v *SpecTreeVisitor) VisitOperand(ctx *OperandContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.Literal() != nil || ctx.Identifier() != nil || ctx.Old() != nil || ctx.AccessPermission() != nil {
		return children[0]
	} else { // case: ( expression )
		return children[1]
	}
}

func (v *SpecTreeVisitor) VisitLiteral(ctx *LiteralContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[0]
}

func (v *SpecTreeVisitor) VisitInteger(ctx *IntegerContext) interface{} {
	return Integer{ctx.GetText()}
}

func (v *SpecTreeVisitor) VisitIdentifier(ctx *IdentifierContext) interface{} {
	return Identifier{value: ctx.GetText()}
}

func (v *SpecTreeVisitor) VisitSquarebracket(ctx *SquarebracketContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[1]
}

func (v *SpecTreeVisitor) VisitDotnotation(ctx *DotnotationContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[1]
}

func (v *SpecTreeVisitor) VisitArrayLit(ctx *ArrayLitContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return ArrayLiteral{
		arrayType: children[0].(ArrayType),
		values:    children[1].([][]Node),
	}
}

func (v *SpecTreeVisitor) VisitStructLit(ctx *StructLitContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return StructLiteral{
		identifier: children[0].(Node),
		values:     children[1].([][]Node),
	}
}

func (v *SpecTreeVisitor) VisitLiteralValue(ctx *LiteralValueContext) interface{} {
	if ctx.ElementList() != nil {
		children := v.VisitChildren(ctx).([]interface{})
		return children[1]
	} else {
		return [][]Node{}
	}
}

func (v *SpecTreeVisitor) VisitElementList(ctx *ElementListContext) interface{} {
	var elements [][]Node
	children := v.VisitChildren(ctx).([]interface{})
	for _, child := range children {
		if child != nil { // skip commas
			elements = append(elements, child.([]Node))
		}
	}
	return elements
}

func (v *SpecTreeVisitor) VisitKeyedElement(ctx *KeyedElementContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.Key() != nil {
		return []Node{children[0].(Node), children[2].(Node)}
	} else {
		return []Node{nil, children[0].(Node)}
	}
}

func (v *SpecTreeVisitor) VisitKey(ctx *KeyContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[0]
}

func (v *SpecTreeVisitor) VisitElement(ctx *ElementContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[0]
}

func (v *SpecTreeVisitor) VisitArrayType(ctx *ArrayTypeContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.ArrayLength() != nil {
		return ArrayType{
			arrayType: children[3].(Node),
			length:    children[1].(Node),
		}
	} else {
		return ArrayType{
			arrayType: children[2].(Node),
			length:    nil,
		}
	}
}

func (v *SpecTreeVisitor) VisitArrayLength(ctx *ArrayLengthContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[0]
}

func (v *SpecTreeVisitor) VisitElementType(ctx *ElementTypeContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[0]
}

func (v *SpecTreeVisitor) VisitTypeLit(ctx *TypeLitContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[0]
}

func (v *SpecTreeVisitor) VisitPointerType(ctx *PointerTypeContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return Dereference{
		operand: children[1].(Node),
	}
}

func (v *SpecTreeVisitor) VisitPurity(ctx *PurityContext) interface{} {
	return Purity{}
}

func (v *SpecTreeVisitor) VisitOld(ctx *OldContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.Identifier() != nil { // labelled old
		return Old{
			label:      ctx.Identifier().GetText(),
			expression: children[5].(Node),
		}
	} else { // unlabelled old
		return Old{
			expression: children[2].(Node),
		}
	}
}

func (v *SpecTreeVisitor) VisitAccessPermission(ctx *AccessPermissionContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return Access{
		operand: children[2].(Node),
	}
}

func (v *SpecTreeVisitor) VisitReference(ctx *ReferenceContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return Unary{
		operator: "&",
		operand:  children[1].(Node),
	}
}

func (v *SpecTreeVisitor) VisitLabel(ctx *LabelContext) interface{} {
	return Label{
		name: ctx.Identifier().GetText(),
	}
}

func (v *SpecTreeVisitor) VisitVariableList(ctx *VariableListContext) interface{} {
	var variableList [][]Node
	children := v.VisitChildren(ctx).([]interface{})
	for _, child := range children {
		if child != nil { // skip commas
			variableList = append(variableList, child.([][]Node)...)
		}
	}
	return variableList
}

func (v *SpecTreeVisitor) VisitVarTypeTuple(ctx *VarTypeTupleContext) interface{} {
	var variablesTypeTuples [][]Node
	children := v.VisitChildren(ctx).([]interface{})
	_type := children[len(children)-1].(Node)
	for i := 0; i < len(children)-1; i++ {
		child := children[i]
		if child != nil { // skip commas
			variablesTypeTuples = append(variablesTypeTuples, []Node{child.(Node), _type})
		}
	}
	return variablesTypeTuples
}

func (v *SpecTreeVisitor) VisitExpressionList(ctx *ExpressionListContext) interface{} {
	var expressionList []Node
	children := v.VisitChildren(ctx).([]interface{})
	for _, child := range children {
		if child != nil { // skip commas
			expressionList = append(expressionList, child.(Node))
		}
	}
	return expressionList
}

func (v *SpecTreeVisitor) VisitDomain(ctx *DomainContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.LPAREN() != nil {
		return children[1].(Node)
	} else if ctx.kind != nil {
		left := children[0].(Domain)
		right := children[2].(Domain)
		return Domain{
			isLeaf:   false,
			left:     &left,
			right:    &right,
			operator: ctx.kind.GetText(),
		}
	} else {
		return Domain{
			isLeaf:  true,
			literal: children[0].(DomainLiteral),
		}
	}
}

func (v *SpecTreeVisitor) VisitDomainLiteral(ctx *DomainLiteralContext) interface{} {
	return v.VisitChildren(ctx).([]interface{})[0]
}

func (v *SpecTreeVisitor) VisitNumericDomainLiteral(ctx *NumericDomainLiteralContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return NumericDomainLiteral{
		lower:         children[0].(Node),
		lowerRelation: ctx.lowerKind.GetText(),
		upper:         children[4].(Node),
		upperRelation: ctx.upperKind.GetText(),
		variable:      children[2].(Identifier),
	}
}

func (v *SpecTreeVisitor) VisitDataStructureDomainLiteral(ctx *DataStructureDomainLiteralContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	var structure Node
	var keyId, valueId Identifier
	var literalType LiteralType
	if ctx.COMMA() != nil && ctx.LPAREN() != nil {
		keyId = children[1].(Identifier)
		valueId = children[3].(Identifier)
		structure = children[5].(Node)
	} else if ctx.COMMA() != nil {
		keyId = children[0].(Identifier)
		valueId = children[2].(Identifier)
		structure = children[3].(Node)
	} else {
		keyId = children[0].(Identifier)
		structure = children[1].(Node)
	}
	var key, value *Identifier
	if keyId.value == "_" {
		literalType = VALUE
		value = &valueId
	} else if valueId.value != "" {
		literalType = KEYVALUE
		key = &keyId
		value = &valueId
	} else {
		literalType = KEY
		key = &keyId
	}
	return DataStructureDomainLiteral{
		literalType: literalType,
		key:         key,
		value:       value,
		structure:   structure,
	}
}

func (v *SpecTreeVisitor) VisitDataStructureRange(ctx *DataStructureRangeContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return children[2].(Node)
}

func (v *SpecTreeVisitor) VisitSharedVarsNotation(ctx *SharedVarsNotationContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return SharedVars{variables: children[2].([]Identifier)}
}

func (v *SpecTreeVisitor) VisitExclusiveVarsNotation(ctx *ExclusiveVarsNotationContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	return ExclusiveVars{variables: children[2].([]Identifier)}
}

func (v *SpecTreeVisitor) VisitIdentifierList(ctx *IdentifierListContext) interface{} {
	var identifierList []Identifier
	children := v.VisitChildren(ctx).([]interface{})
	for _, child := range children {
		if child != nil { // skip commas
			identifierList = append(identifierList, child.(Identifier))
		}
	}
	return identifierList
}

func (v *SpecTreeVisitor) VisitPredicate(ctx *PredicateContext) interface{} {
	children := v.VisitChildren(ctx).([]interface{})
	if ctx.VariableList() != nil {
		return Predicate{
			name:       children[1].(Identifier),
			parameters: children[3].([][]Node),
			assertion:  children[6].(Node),
		}
	} else {
		return Predicate{
			name:      children[1].(Identifier),
			assertion: children[5].(Node),
		}
	}
}
