// Code generated from SpecGrammar.g4 by ANTLR 4.7.1. DO NOT EDIT.

package specparser // SpecGrammar
import "github.com/antlr/antlr4/runtime/Go/antlr"

// BaseSpecGrammarListener is a complete listener for a parse tree produced by SpecGrammarParser.
type BaseSpecGrammarListener struct{}

var _ SpecGrammarListener = &BaseSpecGrammarListener{}

// VisitTerminal is called when a terminal node is visited.
func (s *BaseSpecGrammarListener) VisitTerminal(node antlr.TerminalNode) {}

// VisitErrorNode is called when an error node is visited.
func (s *BaseSpecGrammarListener) VisitErrorNode(node antlr.ErrorNode) {}

// EnterEveryRule is called when any rule is entered.
func (s *BaseSpecGrammarListener) EnterEveryRule(ctx antlr.ParserRuleContext) {}

// ExitEveryRule is called when any rule is exited.
func (s *BaseSpecGrammarListener) ExitEveryRule(ctx antlr.ParserRuleContext) {}

// EnterStart is called when production start is entered.
func (s *BaseSpecGrammarListener) EnterStart(ctx *StartContext) {}

// ExitStart is called when production start is exited.
func (s *BaseSpecGrammarListener) ExitStart(ctx *StartContext) {}

// EnterSpecification is called when production specification is entered.
func (s *BaseSpecGrammarListener) EnterSpecification(ctx *SpecificationContext) {}

// ExitSpecification is called when production specification is exited.
func (s *BaseSpecGrammarListener) ExitSpecification(ctx *SpecificationContext) {}

// EnterSpecStatement is called when production specStatement is entered.
func (s *BaseSpecGrammarListener) EnterSpecStatement(ctx *SpecStatementContext) {}

// ExitSpecStatement is called when production specStatement is exited.
func (s *BaseSpecGrammarListener) ExitSpecStatement(ctx *SpecStatementContext) {}

// EnterAssertion is called when production assertion is entered.
func (s *BaseSpecGrammarListener) EnterAssertion(ctx *AssertionContext) {}

// ExitAssertion is called when production assertion is exited.
func (s *BaseSpecGrammarListener) ExitAssertion(ctx *AssertionContext) {}

// EnterExpression is called when production expression is entered.
func (s *BaseSpecGrammarListener) EnterExpression(ctx *ExpressionContext) {}

// ExitExpression is called when production expression is exited.
func (s *BaseSpecGrammarListener) ExitExpression(ctx *ExpressionContext) {}

// EnterPrimary is called when production primary is entered.
func (s *BaseSpecGrammarListener) EnterPrimary(ctx *PrimaryContext) {}

// ExitPrimary is called when production primary is exited.
func (s *BaseSpecGrammarListener) ExitPrimary(ctx *PrimaryContext) {}

// EnterUnary is called when production unary is entered.
func (s *BaseSpecGrammarListener) EnterUnary(ctx *UnaryContext) {}

// ExitUnary is called when production unary is exited.
func (s *BaseSpecGrammarListener) ExitUnary(ctx *UnaryContext) {}

// EnterBinary is called when production binary is entered.
func (s *BaseSpecGrammarListener) EnterBinary(ctx *BinaryContext) {}

// ExitBinary is called when production binary is exited.
func (s *BaseSpecGrammarListener) ExitBinary(ctx *BinaryContext) {}

// EnterOperand is called when production operand is entered.
func (s *BaseSpecGrammarListener) EnterOperand(ctx *OperandContext) {}

// ExitOperand is called when production operand is exited.
func (s *BaseSpecGrammarListener) ExitOperand(ctx *OperandContext) {}

// EnterLiteral is called when production literal is entered.
func (s *BaseSpecGrammarListener) EnterLiteral(ctx *LiteralContext) {}

// ExitLiteral is called when production literal is exited.
func (s *BaseSpecGrammarListener) ExitLiteral(ctx *LiteralContext) {}

// EnterInteger is called when production integer is entered.
func (s *BaseSpecGrammarListener) EnterInteger(ctx *IntegerContext) {}

// ExitInteger is called when production integer is exited.
func (s *BaseSpecGrammarListener) ExitInteger(ctx *IntegerContext) {}

// EnterIdentifier is called when production identifier is entered.
func (s *BaseSpecGrammarListener) EnterIdentifier(ctx *IdentifierContext) {}

// ExitIdentifier is called when production identifier is exited.
func (s *BaseSpecGrammarListener) ExitIdentifier(ctx *IdentifierContext) {}

// EnterSquarebracket is called when production squarebracket is entered.
func (s *BaseSpecGrammarListener) EnterSquarebracket(ctx *SquarebracketContext) {}

// ExitSquarebracket is called when production squarebracket is exited.
func (s *BaseSpecGrammarListener) ExitSquarebracket(ctx *SquarebracketContext) {}

// EnterDotnotation is called when production dotnotation is entered.
func (s *BaseSpecGrammarListener) EnterDotnotation(ctx *DotnotationContext) {}

// ExitDotnotation is called when production dotnotation is exited.
func (s *BaseSpecGrammarListener) ExitDotnotation(ctx *DotnotationContext) {}

// EnterArrayLit is called when production arrayLit is entered.
func (s *BaseSpecGrammarListener) EnterArrayLit(ctx *ArrayLitContext) {}

// ExitArrayLit is called when production arrayLit is exited.
func (s *BaseSpecGrammarListener) ExitArrayLit(ctx *ArrayLitContext) {}

// EnterStructLit is called when production structLit is entered.
func (s *BaseSpecGrammarListener) EnterStructLit(ctx *StructLitContext) {}

// ExitStructLit is called when production structLit is exited.
func (s *BaseSpecGrammarListener) ExitStructLit(ctx *StructLitContext) {}

// EnterLiteralValue is called when production literalValue is entered.
func (s *BaseSpecGrammarListener) EnterLiteralValue(ctx *LiteralValueContext) {}

// ExitLiteralValue is called when production literalValue is exited.
func (s *BaseSpecGrammarListener) ExitLiteralValue(ctx *LiteralValueContext) {}

// EnterElementList is called when production elementList is entered.
func (s *BaseSpecGrammarListener) EnterElementList(ctx *ElementListContext) {}

// ExitElementList is called when production elementList is exited.
func (s *BaseSpecGrammarListener) ExitElementList(ctx *ElementListContext) {}

// EnterKeyedElement is called when production keyedElement is entered.
func (s *BaseSpecGrammarListener) EnterKeyedElement(ctx *KeyedElementContext) {}

// ExitKeyedElement is called when production keyedElement is exited.
func (s *BaseSpecGrammarListener) ExitKeyedElement(ctx *KeyedElementContext) {}

// EnterKey is called when production key is entered.
func (s *BaseSpecGrammarListener) EnterKey(ctx *KeyContext) {}

// ExitKey is called when production key is exited.
func (s *BaseSpecGrammarListener) ExitKey(ctx *KeyContext) {}

// EnterElement is called when production element is entered.
func (s *BaseSpecGrammarListener) EnterElement(ctx *ElementContext) {}

// ExitElement is called when production element is exited.
func (s *BaseSpecGrammarListener) ExitElement(ctx *ElementContext) {}

// EnterArrayType is called when production arrayType is entered.
func (s *BaseSpecGrammarListener) EnterArrayType(ctx *ArrayTypeContext) {}

// ExitArrayType is called when production arrayType is exited.
func (s *BaseSpecGrammarListener) ExitArrayType(ctx *ArrayTypeContext) {}

// EnterArrayLength is called when production arrayLength is entered.
func (s *BaseSpecGrammarListener) EnterArrayLength(ctx *ArrayLengthContext) {}

// ExitArrayLength is called when production arrayLength is exited.
func (s *BaseSpecGrammarListener) ExitArrayLength(ctx *ArrayLengthContext) {}

// EnterElementType is called when production elementType is entered.
func (s *BaseSpecGrammarListener) EnterElementType(ctx *ElementTypeContext) {}

// ExitElementType is called when production elementType is exited.
func (s *BaseSpecGrammarListener) ExitElementType(ctx *ElementTypeContext) {}

// EnterTypeLit is called when production typeLit is entered.
func (s *BaseSpecGrammarListener) EnterTypeLit(ctx *TypeLitContext) {}

// ExitTypeLit is called when production typeLit is exited.
func (s *BaseSpecGrammarListener) ExitTypeLit(ctx *TypeLitContext) {}

// EnterPointerType is called when production pointerType is entered.
func (s *BaseSpecGrammarListener) EnterPointerType(ctx *PointerTypeContext) {}

// ExitPointerType is called when production pointerType is exited.
func (s *BaseSpecGrammarListener) ExitPointerType(ctx *PointerTypeContext) {}

// EnterPurity is called when production purity is entered.
func (s *BaseSpecGrammarListener) EnterPurity(ctx *PurityContext) {}

// ExitPurity is called when production purity is exited.
func (s *BaseSpecGrammarListener) ExitPurity(ctx *PurityContext) {}

// EnterSharedVarsNotation is called when production sharedVarsNotation is entered.
func (s *BaseSpecGrammarListener) EnterSharedVarsNotation(ctx *SharedVarsNotationContext) {}

// ExitSharedVarsNotation is called when production sharedVarsNotation is exited.
func (s *BaseSpecGrammarListener) ExitSharedVarsNotation(ctx *SharedVarsNotationContext) {}

// EnterExclusiveVarsNotation is called when production exclusiveVarsNotation is entered.
func (s *BaseSpecGrammarListener) EnterExclusiveVarsNotation(ctx *ExclusiveVarsNotationContext) {}

// ExitExclusiveVarsNotation is called when production exclusiveVarsNotation is exited.
func (s *BaseSpecGrammarListener) ExitExclusiveVarsNotation(ctx *ExclusiveVarsNotationContext) {}

// EnterOld is called when production old is entered.
func (s *BaseSpecGrammarListener) EnterOld(ctx *OldContext) {}

// ExitOld is called when production old is exited.
func (s *BaseSpecGrammarListener) ExitOld(ctx *OldContext) {}

// EnterLabel is called when production label is entered.
func (s *BaseSpecGrammarListener) EnterLabel(ctx *LabelContext) {}

// ExitLabel is called when production label is exited.
func (s *BaseSpecGrammarListener) ExitLabel(ctx *LabelContext) {}

// EnterVariableList is called when production variableList is entered.
func (s *BaseSpecGrammarListener) EnterVariableList(ctx *VariableListContext) {}

// ExitVariableList is called when production variableList is exited.
func (s *BaseSpecGrammarListener) ExitVariableList(ctx *VariableListContext) {}

// EnterExpressionList is called when production expressionList is entered.
func (s *BaseSpecGrammarListener) EnterExpressionList(ctx *ExpressionListContext) {}

// ExitExpressionList is called when production expressionList is exited.
func (s *BaseSpecGrammarListener) ExitExpressionList(ctx *ExpressionListContext) {}

// EnterIdentifierList is called when production identifierList is entered.
func (s *BaseSpecGrammarListener) EnterIdentifierList(ctx *IdentifierListContext) {}

// ExitIdentifierList is called when production identifierList is exited.
func (s *BaseSpecGrammarListener) ExitIdentifierList(ctx *IdentifierListContext) {}

// EnterVarTypeTuple is called when production varTypeTuple is entered.
func (s *BaseSpecGrammarListener) EnterVarTypeTuple(ctx *VarTypeTupleContext) {}

// ExitVarTypeTuple is called when production varTypeTuple is exited.
func (s *BaseSpecGrammarListener) ExitVarTypeTuple(ctx *VarTypeTupleContext) {}

// EnterAccessPermission is called when production accessPermission is entered.
func (s *BaseSpecGrammarListener) EnterAccessPermission(ctx *AccessPermissionContext) {}

// ExitAccessPermission is called when production accessPermission is exited.
func (s *BaseSpecGrammarListener) ExitAccessPermission(ctx *AccessPermissionContext) {}

// EnterReference is called when production reference is entered.
func (s *BaseSpecGrammarListener) EnterReference(ctx *ReferenceContext) {}

// ExitReference is called when production reference is exited.
func (s *BaseSpecGrammarListener) ExitReference(ctx *ReferenceContext) {}

// EnterDomain is called when production domain is entered.
func (s *BaseSpecGrammarListener) EnterDomain(ctx *DomainContext) {}

// ExitDomain is called when production domain is exited.
func (s *BaseSpecGrammarListener) ExitDomain(ctx *DomainContext) {}

// EnterDomainLiteral is called when production domainLiteral is entered.
func (s *BaseSpecGrammarListener) EnterDomainLiteral(ctx *DomainLiteralContext) {}

// ExitDomainLiteral is called when production domainLiteral is exited.
func (s *BaseSpecGrammarListener) ExitDomainLiteral(ctx *DomainLiteralContext) {}

// EnterNumericDomainLiteral is called when production numericDomainLiteral is entered.
func (s *BaseSpecGrammarListener) EnterNumericDomainLiteral(ctx *NumericDomainLiteralContext) {}

// ExitNumericDomainLiteral is called when production numericDomainLiteral is exited.
func (s *BaseSpecGrammarListener) ExitNumericDomainLiteral(ctx *NumericDomainLiteralContext) {}

// EnterDataStructureDomainLiteral is called when production dataStructureDomainLiteral is entered.
func (s *BaseSpecGrammarListener) EnterDataStructureDomainLiteral(ctx *DataStructureDomainLiteralContext) {
}

// ExitDataStructureDomainLiteral is called when production dataStructureDomainLiteral is exited.
func (s *BaseSpecGrammarListener) ExitDataStructureDomainLiteral(ctx *DataStructureDomainLiteralContext) {
}

// EnterDataStructureRange is called when production dataStructureRange is entered.
func (s *BaseSpecGrammarListener) EnterDataStructureRange(ctx *DataStructureRangeContext) {}

// ExitDataStructureRange is called when production dataStructureRange is exited.
func (s *BaseSpecGrammarListener) ExitDataStructureRange(ctx *DataStructureRangeContext) {}

// EnterPredicate is called when production predicate is entered.
func (s *BaseSpecGrammarListener) EnterPredicate(ctx *PredicateContext) {}

// ExitPredicate is called when production predicate is exited.
func (s *BaseSpecGrammarListener) ExitPredicate(ctx *PredicateContext) {}
