// Code generated from SpecGrammar.g4 by ANTLR 4.7.1. DO NOT EDIT.

package specparser // SpecGrammar
import "github.com/antlr/antlr4/runtime/Go/antlr"

// SpecGrammarListener is a complete listener for a parse tree produced by SpecGrammarParser.
type SpecGrammarListener interface {
	antlr.ParseTreeListener

	// EnterStart is called when entering the start production.
	EnterStart(c *StartContext)

	// EnterSpecification is called when entering the specification production.
	EnterSpecification(c *SpecificationContext)

	// EnterSpecStatement is called when entering the specStatement production.
	EnterSpecStatement(c *SpecStatementContext)

	// EnterAssertion is called when entering the assertion production.
	EnterAssertion(c *AssertionContext)

	// EnterExpression is called when entering the expression production.
	EnterExpression(c *ExpressionContext)

	// EnterPrimary is called when entering the primary production.
	EnterPrimary(c *PrimaryContext)

	// EnterUnary is called when entering the unary production.
	EnterUnary(c *UnaryContext)

	// EnterBinary is called when entering the binary production.
	EnterBinary(c *BinaryContext)

	// EnterOperand is called when entering the operand production.
	EnterOperand(c *OperandContext)

	// EnterLiteral is called when entering the literal production.
	EnterLiteral(c *LiteralContext)

	// EnterInteger is called when entering the integer production.
	EnterInteger(c *IntegerContext)

	// EnterIdentifier is called when entering the identifier production.
	EnterIdentifier(c *IdentifierContext)

	// EnterSquarebracket is called when entering the squarebracket production.
	EnterSquarebracket(c *SquarebracketContext)

	// EnterDotnotation is called when entering the dotnotation production.
	EnterDotnotation(c *DotnotationContext)

	// EnterArrayLit is called when entering the arrayLit production.
	EnterArrayLit(c *ArrayLitContext)

	// EnterStructLit is called when entering the structLit production.
	EnterStructLit(c *StructLitContext)

	// EnterLiteralValue is called when entering the literalValue production.
	EnterLiteralValue(c *LiteralValueContext)

	// EnterElementList is called when entering the elementList production.
	EnterElementList(c *ElementListContext)

	// EnterKeyedElement is called when entering the keyedElement production.
	EnterKeyedElement(c *KeyedElementContext)

	// EnterKey is called when entering the key production.
	EnterKey(c *KeyContext)

	// EnterElement is called when entering the element production.
	EnterElement(c *ElementContext)

	// EnterArrayType is called when entering the arrayType production.
	EnterArrayType(c *ArrayTypeContext)

	// EnterArrayLength is called when entering the arrayLength production.
	EnterArrayLength(c *ArrayLengthContext)

	// EnterElementType is called when entering the elementType production.
	EnterElementType(c *ElementTypeContext)

	// EnterTypeLit is called when entering the typeLit production.
	EnterTypeLit(c *TypeLitContext)

	// EnterPointerType is called when entering the pointerType production.
	EnterPointerType(c *PointerTypeContext)

	// EnterPurity is called when entering the purity production.
	EnterPurity(c *PurityContext)

	// EnterSharedVarsNotation is called when entering the sharedVarsNotation production.
	EnterSharedVarsNotation(c *SharedVarsNotationContext)

	// EnterExclusiveVarsNotation is called when entering the exclusiveVarsNotation production.
	EnterExclusiveVarsNotation(c *ExclusiveVarsNotationContext)

	// EnterOld is called when entering the old production.
	EnterOld(c *OldContext)

	// EnterLabel is called when entering the label production.
	EnterLabel(c *LabelContext)

	// EnterVariableList is called when entering the variableList production.
	EnterVariableList(c *VariableListContext)

	// EnterExpressionList is called when entering the expressionList production.
	EnterExpressionList(c *ExpressionListContext)

	// EnterIdentifierList is called when entering the identifierList production.
	EnterIdentifierList(c *IdentifierListContext)

	// EnterVarTypeTuple is called when entering the varTypeTuple production.
	EnterVarTypeTuple(c *VarTypeTupleContext)

	// EnterAccessPermission is called when entering the accessPermission production.
	EnterAccessPermission(c *AccessPermissionContext)

	// EnterReference is called when entering the reference production.
	EnterReference(c *ReferenceContext)

	// EnterDomain is called when entering the domain production.
	EnterDomain(c *DomainContext)

	// EnterDomainLiteral is called when entering the domainLiteral production.
	EnterDomainLiteral(c *DomainLiteralContext)

	// EnterNumericDomainLiteral is called when entering the numericDomainLiteral production.
	EnterNumericDomainLiteral(c *NumericDomainLiteralContext)

	// EnterDataStructureDomainLiteral is called when entering the dataStructureDomainLiteral production.
	EnterDataStructureDomainLiteral(c *DataStructureDomainLiteralContext)

	// EnterDataStructureRange is called when entering the dataStructureRange production.
	EnterDataStructureRange(c *DataStructureRangeContext)

	// EnterPredicate is called when entering the predicate production.
	EnterPredicate(c *PredicateContext)

	// ExitStart is called when exiting the start production.
	ExitStart(c *StartContext)

	// ExitSpecification is called when exiting the specification production.
	ExitSpecification(c *SpecificationContext)

	// ExitSpecStatement is called when exiting the specStatement production.
	ExitSpecStatement(c *SpecStatementContext)

	// ExitAssertion is called when exiting the assertion production.
	ExitAssertion(c *AssertionContext)

	// ExitExpression is called when exiting the expression production.
	ExitExpression(c *ExpressionContext)

	// ExitPrimary is called when exiting the primary production.
	ExitPrimary(c *PrimaryContext)

	// ExitUnary is called when exiting the unary production.
	ExitUnary(c *UnaryContext)

	// ExitBinary is called when exiting the binary production.
	ExitBinary(c *BinaryContext)

	// ExitOperand is called when exiting the operand production.
	ExitOperand(c *OperandContext)

	// ExitLiteral is called when exiting the literal production.
	ExitLiteral(c *LiteralContext)

	// ExitInteger is called when exiting the integer production.
	ExitInteger(c *IntegerContext)

	// ExitIdentifier is called when exiting the identifier production.
	ExitIdentifier(c *IdentifierContext)

	// ExitSquarebracket is called when exiting the squarebracket production.
	ExitSquarebracket(c *SquarebracketContext)

	// ExitDotnotation is called when exiting the dotnotation production.
	ExitDotnotation(c *DotnotationContext)

	// ExitArrayLit is called when exiting the arrayLit production.
	ExitArrayLit(c *ArrayLitContext)

	// ExitStructLit is called when exiting the structLit production.
	ExitStructLit(c *StructLitContext)

	// ExitLiteralValue is called when exiting the literalValue production.
	ExitLiteralValue(c *LiteralValueContext)

	// ExitElementList is called when exiting the elementList production.
	ExitElementList(c *ElementListContext)

	// ExitKeyedElement is called when exiting the keyedElement production.
	ExitKeyedElement(c *KeyedElementContext)

	// ExitKey is called when exiting the key production.
	ExitKey(c *KeyContext)

	// ExitElement is called when exiting the element production.
	ExitElement(c *ElementContext)

	// ExitArrayType is called when exiting the arrayType production.
	ExitArrayType(c *ArrayTypeContext)

	// ExitArrayLength is called when exiting the arrayLength production.
	ExitArrayLength(c *ArrayLengthContext)

	// ExitElementType is called when exiting the elementType production.
	ExitElementType(c *ElementTypeContext)

	// ExitTypeLit is called when exiting the typeLit production.
	ExitTypeLit(c *TypeLitContext)

	// ExitPointerType is called when exiting the pointerType production.
	ExitPointerType(c *PointerTypeContext)

	// ExitPurity is called when exiting the purity production.
	ExitPurity(c *PurityContext)

	// ExitSharedVarsNotation is called when exiting the sharedVarsNotation production.
	ExitSharedVarsNotation(c *SharedVarsNotationContext)

	// ExitExclusiveVarsNotation is called when exiting the exclusiveVarsNotation production.
	ExitExclusiveVarsNotation(c *ExclusiveVarsNotationContext)

	// ExitOld is called when exiting the old production.
	ExitOld(c *OldContext)

	// ExitLabel is called when exiting the label production.
	ExitLabel(c *LabelContext)

	// ExitVariableList is called when exiting the variableList production.
	ExitVariableList(c *VariableListContext)

	// ExitExpressionList is called when exiting the expressionList production.
	ExitExpressionList(c *ExpressionListContext)

	// ExitIdentifierList is called when exiting the identifierList production.
	ExitIdentifierList(c *IdentifierListContext)

	// ExitVarTypeTuple is called when exiting the varTypeTuple production.
	ExitVarTypeTuple(c *VarTypeTupleContext)

	// ExitAccessPermission is called when exiting the accessPermission production.
	ExitAccessPermission(c *AccessPermissionContext)

	// ExitReference is called when exiting the reference production.
	ExitReference(c *ReferenceContext)

	// ExitDomain is called when exiting the domain production.
	ExitDomain(c *DomainContext)

	// ExitDomainLiteral is called when exiting the domainLiteral production.
	ExitDomainLiteral(c *DomainLiteralContext)

	// ExitNumericDomainLiteral is called when exiting the numericDomainLiteral production.
	ExitNumericDomainLiteral(c *NumericDomainLiteralContext)

	// ExitDataStructureDomainLiteral is called when exiting the dataStructureDomainLiteral production.
	ExitDataStructureDomainLiteral(c *DataStructureDomainLiteralContext)

	// ExitDataStructureRange is called when exiting the dataStructureRange production.
	ExitDataStructureRange(c *DataStructureRangeContext)

	// ExitPredicate is called when exiting the predicate production.
	ExitPredicate(c *PredicateContext)
}
