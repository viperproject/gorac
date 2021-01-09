// ANTLR grammar
// generate sources with: antlr4 -Dlanguage=Go -o . -package specparser -visitor SpecGrammar.g4
// some rules adapted from https://github.com/antlr/grammars-v4/tree/master/golang
grammar SpecGrammar;

// TOKENS

// Specification keywords

ASSERT      : 'assert';
ASSUME      : 'assume';
PRE         : 'requires';
POST        : 'ensures';
INV         : 'invariant';
PURE        : 'pure';
OLD         : 'old';
FORALL      : 'forall';
EXISTS      : 'exists';
ACCESS      : 'acc';
IN          : 'in';
RANGE       : 'range';
SHARED      : 'shared';
EXCLUSIVE   : 'exclusive';
PREDICATE   : 'predicate';

// Basic

IDENTIFIER      : [A-Za-z_@][A-Za-z0-9_]*; // covers true, false, nil too
INTEGER         : [0-9]+;

// Brackets

LPAREN  : '(';
RPAREN  : ')';
LSB     : '[';
RSB     : ']';
LCB     : '{';
RCB     : '}';

// Logical

NOT     : '!';
AND     : '&&';
OR      : '||';
IMPLIES : '==>';

// Relational

EQ      : '==';
NEQ     : '!=';
LESS    : '<';
GREAT   : '>';
LEQ     : '<=';
GEQ     : '>=';

// Arithmetic

DIV     : '/';
MOD     : '%';

// Mixed

DOT         : '.';
COLON       : ':';
COMMA       : ',';
PLUS        : '+';
MINUS       : '-';
STAR        : '*';
QUESTION    : '?';
REFERENCE   : '&';

WHITESPACE      : [ \r\n\t]+ -> skip;
SPECSTART       : '/*@' -> skip;
SPECEND         : '@*/' -> skip;
SPECLINESTART   : '//@' -> skip;

// RULES

start : specification EOF;

specification
    : specStatement (specStatement)*
    ;

specStatement
    : LPAREN specStatement RPAREN
    | kind=ASSERT assertion
    | kind=ASSUME assertion
    | kind=PRE assertion
    | kind=POST assertion
    | kind=INV assertion
    | purity
    | label
    | sharedVarsNotation
    | exclusiveVarsNotation
    | predicate
    ;

assertion
    : LPAREN assertion RPAREN
    | FORALL variableList COLON COLON domain IMPLIES assertion
    | EXISTS variableList COLON COLON domain AND expression
    | FORALL variableList COLON COLON assertion // if all quantified variables are boolean, the domain is empty
    | EXISTS variableList COLON COLON expression // if all quantified variables are boolean, the domain is empty
    | expression
    | kind=NOT assertion
    | assertion kind=AND assertion
    | assertion kind=OR assertion
    | expression kind=IMPLIES assertion
    | expression kind=QUESTION assertion COLON assertion
    ;

expression
    : LPAREN expression RPAREN
    | primary
    | unary
    | binary
    ;

primary
    : operand
    | primary (dotnotation | squarebracket)
    | primary LPAREN expressionList RPAREN
    | primary LPAREN RPAREN
    ;

unary
    : primary
    | kind=(PLUS | MINUS | NOT | STAR) unary
    ;

binary
    : binary kind=(DIV | MOD | STAR) binary // Split due to precedence
    | binary kind=(PLUS | MINUS) binary
    | binary kind=(LEQ | GEQ | GREAT | LESS) binary
    | binary kind=(EQ | NEQ) binary
    | binary kind=AND binary
    | binary kind=OR binary
    | unary
    ;

operand
    : literal
    | identifier
    | old
    | accessPermission
    | LPAREN expression RPAREN
    ;

literal
    : integer
    | arrayLit
    | structLit
    ;

integer
    : kind=INTEGER
    ;

identifier
    : IDENTIFIER
    ;

squarebracket
    : LSB expression RSB
    ;

dotnotation
    : DOT identifier
    ;

arrayLit
    : arrayType literalValue
    ;

structLit
    : identifier literalValue
    ;

literalValue
    : LCB (elementList COMMA?)? RCB
    ;

elementList
    : keyedElement (COMMA keyedElement)*
    ;

keyedElement
    : (key COLON)? element
    ;

key
    : identifier
    | expression
    | literalValue
    ;

element
    : expression
    | literalValue
    ;

arrayType
    : LSB arrayLength RSB elementType
    | LSB RSB elementType
    ;

arrayLength
    : expression
    ;

elementType
    : identifier
    | typeLit
    ;

typeLit
    : arrayType
    | pointerType
    ;

pointerType
    : STAR elementType
    ;

purity
    : PURE
    ;

sharedVarsNotation
    : SHARED COLON identifierList
    ;

exclusiveVarsNotation
    : EXCLUSIVE COLON identifierList
    ;

old
    : OLD LPAREN expression RPAREN
    | OLD LSB identifier RSB LPAREN expression RPAREN
    ;

label
    : identifier COLON
    ;

variableList
    : varTypeTuple (COMMA varTypeTuple)* COMMA?
    ;

expressionList
    : expression (COMMA expression)*
    ;

identifierList
    : identifier (COMMA identifier)*
    ;

varTypeTuple
    : identifier (COMMA identifier)* elementType
    ;

accessPermission
    : ACCESS LPAREN primary RPAREN
    | ACCESS LPAREN reference RPAREN
    ;

reference
    : REFERENCE primary
    ;

domain
    : LPAREN domain RPAREN
    | domain kind=AND domain
    | domain kind=OR domain
    | domainLiteral
    ;

domainLiteral
    : numericDomainLiteral
    | dataStructureDomainLiteral
    ;

numericDomainLiteral
    : expression lowerKind=(LEQ | LESS) identifier upperKind=(LEQ | LESS) expression
    ;

dataStructureDomainLiteral
    : LPAREN identifier COMMA identifier RPAREN dataStructureRange
    | identifier COMMA identifier dataStructureRange
    | identifier dataStructureRange
    ;

dataStructureRange
    : IN RANGE expression
    ;

predicate
    : PREDICATE identifier LPAREN variableList RPAREN LCB assertion RCB
    | PREDICATE identifier LPAREN RPAREN LCB assertion RCB
    ;