// Code generated from SpecGrammar.g4 by ANTLR 4.7.1. DO NOT EDIT.

package specparser // SpecGrammar
import "github.com/antlr/antlr4/runtime/Go/antlr"

// A complete Visitor for a parse tree produced by SpecGrammarParser.
type SpecGrammarVisitor interface {
	antlr.ParseTreeVisitor

	// Visit a parse tree produced by SpecGrammarParser#start.
	VisitStart(ctx *StartContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#specification.
	VisitSpecification(ctx *SpecificationContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#specStatement.
	VisitSpecStatement(ctx *SpecStatementContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#assertion.
	VisitAssertion(ctx *AssertionContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#expression.
	VisitExpression(ctx *ExpressionContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#primary.
	VisitPrimary(ctx *PrimaryContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#unary.
	VisitUnary(ctx *UnaryContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#binary.
	VisitBinary(ctx *BinaryContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#operand.
	VisitOperand(ctx *OperandContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#literal.
	VisitLiteral(ctx *LiteralContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#integer.
	VisitInteger(ctx *IntegerContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#identifier.
	VisitIdentifier(ctx *IdentifierContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#squarebracket.
	VisitSquarebracket(ctx *SquarebracketContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#dotnotation.
	VisitDotnotation(ctx *DotnotationContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#arrayLit.
	VisitArrayLit(ctx *ArrayLitContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#structLit.
	VisitStructLit(ctx *StructLitContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#literalValue.
	VisitLiteralValue(ctx *LiteralValueContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#elementList.
	VisitElementList(ctx *ElementListContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#keyedElement.
	VisitKeyedElement(ctx *KeyedElementContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#key.
	VisitKey(ctx *KeyContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#element.
	VisitElement(ctx *ElementContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#arrayType.
	VisitArrayType(ctx *ArrayTypeContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#arrayLength.
	VisitArrayLength(ctx *ArrayLengthContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#elementType.
	VisitElementType(ctx *ElementTypeContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#typeLit.
	VisitTypeLit(ctx *TypeLitContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#pointerType.
	VisitPointerType(ctx *PointerTypeContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#purity.
	VisitPurity(ctx *PurityContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#sharedVarsNotation.
	VisitSharedVarsNotation(ctx *SharedVarsNotationContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#exclusiveVarsNotation.
	VisitExclusiveVarsNotation(ctx *ExclusiveVarsNotationContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#old.
	VisitOld(ctx *OldContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#label.
	VisitLabel(ctx *LabelContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#variableList.
	VisitVariableList(ctx *VariableListContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#expressionList.
	VisitExpressionList(ctx *ExpressionListContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#identifierList.
	VisitIdentifierList(ctx *IdentifierListContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#varTypeTuple.
	VisitVarTypeTuple(ctx *VarTypeTupleContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#accessPermission.
	VisitAccessPermission(ctx *AccessPermissionContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#reference.
	VisitReference(ctx *ReferenceContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#domain.
	VisitDomain(ctx *DomainContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#domainLiteral.
	VisitDomainLiteral(ctx *DomainLiteralContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#numericDomainLiteral.
	VisitNumericDomainLiteral(ctx *NumericDomainLiteralContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#dataStructureDomainLiteral.
	VisitDataStructureDomainLiteral(ctx *DataStructureDomainLiteralContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#dataStructureRange.
	VisitDataStructureRange(ctx *DataStructureRangeContext) interface{}

	// Visit a parse tree produced by SpecGrammarParser#predicate.
	VisitPredicate(ctx *PredicateContext) interface{}
}
