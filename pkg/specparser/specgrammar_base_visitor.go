// Code generated from SpecGrammar.g4 by ANTLR 4.7.1. DO NOT EDIT.

package specparser // SpecGrammar
import "github.com/antlr/antlr4/runtime/Go/antlr"

type BaseSpecGrammarVisitor struct {
	*antlr.BaseParseTreeVisitor
}

func (v *BaseSpecGrammarVisitor) VisitStart(ctx *StartContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitSpecification(ctx *SpecificationContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitSpecStatement(ctx *SpecStatementContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitAssertion(ctx *AssertionContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitExpression(ctx *ExpressionContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitPrimary(ctx *PrimaryContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitUnary(ctx *UnaryContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitBinary(ctx *BinaryContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitOperand(ctx *OperandContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitLiteral(ctx *LiteralContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitInteger(ctx *IntegerContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitIdentifier(ctx *IdentifierContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitSquarebracket(ctx *SquarebracketContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitDotnotation(ctx *DotnotationContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitArrayLit(ctx *ArrayLitContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitStructLit(ctx *StructLitContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitLiteralValue(ctx *LiteralValueContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitElementList(ctx *ElementListContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitKeyedElement(ctx *KeyedElementContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitKey(ctx *KeyContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitElement(ctx *ElementContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitArrayType(ctx *ArrayTypeContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitArrayLength(ctx *ArrayLengthContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitElementType(ctx *ElementTypeContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitTypeLit(ctx *TypeLitContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitPointerType(ctx *PointerTypeContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitPurity(ctx *PurityContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitSharedVarsNotation(ctx *SharedVarsNotationContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitExclusiveVarsNotation(ctx *ExclusiveVarsNotationContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitOld(ctx *OldContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitLabel(ctx *LabelContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitVariableList(ctx *VariableListContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitExpressionList(ctx *ExpressionListContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitIdentifierList(ctx *IdentifierListContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitVarTypeTuple(ctx *VarTypeTupleContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitAccessPermission(ctx *AccessPermissionContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitReference(ctx *ReferenceContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitDomain(ctx *DomainContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitDomainLiteral(ctx *DomainLiteralContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitNumericDomainLiteral(ctx *NumericDomainLiteralContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitDataStructureDomainLiteral(ctx *DataStructureDomainLiteralContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitDataStructureRange(ctx *DataStructureRangeContext) interface{} {
	return v.VisitChildren(ctx)
}

func (v *BaseSpecGrammarVisitor) VisitPredicate(ctx *PredicateContext) interface{} {
	return v.VisitChildren(ctx)
}
