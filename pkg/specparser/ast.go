// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package specparser

import (
	"fmt"
	"strings"
)

// Node provides an interace for all specification ast nodes. Every node must implement a string method.
type Node interface {
	String() string
}

// SpecType defines what kind of spec construct we are dealing with.
type SpecType int

const (
	ASSERT SpecType = iota
	ASSUME
	PRE
	POST
	INV
)

// Spec defines ast nodes for all spec constructs that hold a condition. E.g. assertions, assumptions,
// pre- and postconditions and invariants.
type Spec struct {
	specType  SpecType
	condition Node
}

func (s Spec) String() string {
	var specString string
	switch s.specType {
	case ASSERT:
		specString = "assert"
	case ASSUME:
		specString = "assume"
	case PRE:
		specString = "requires"
	case POST:
		specString = "ensures"
	case INV:
		specString = "invariant"
	default:
		panic(fmt.Sprintf("Invalid spec type for spec node with condition %v.", s.condition))
	}
	return fmt.Sprintf("%s %v", specString, s.condition)
}

func (s Spec) Condition() Node {
	return s.condition
}

func (s Spec) SpecType() SpecType {
	return s.specType
}

// Unary specification nodes are of the type <operator> <operand>, e.g. +42, -1337 or !true. Note that the unary &
// operator can only be used inside access permissions.
type Unary struct {
	operator string
	operand  Node
}

func (u Unary) String() string {
	return fmt.Sprintf("%s%v", u.operator, u.operand)
}

func (u Unary) Operator() string {
	return u.operator
}

func (u Unary) Operand() Node {
	return u.operand
}

// Binary specification nodes are of the type <operand1> <operator> <operand2>, e.g. true || false (logical),
// 42 + 1337 (arithmetical), 42 < 1337 (relational) or true != false (equations).
// Binary nodes that represent arithmetic, logical or relational operators are of the regular binary kind. Special
// consideration is given to tenary operators and implications:
// An implication A ==> B is converted internally into !A || B. However, for the sake of usability we want to output
// the actual string A ==> B, thus we need to keep track of the node being an implication by checking the provided operand.
type Binary struct {
	operator string
	left     Node
	right    Node
}

func (b Binary) String() string {
	left := b.left
	if b.operator == "==>" {
		left = b.left.(Unary).operand
	}
	return fmt.Sprintf("(%v %s %v)", left, b.operator, b.right)
}

func (b Binary) Operator() string {
	return b.operator
}

func (b Binary) Left() Node {
	return b.left
}

func (b Binary) Right() Node {
	return b.right
}

// Ternary nodes represent specification of the form e1 ? e2 : e3, meaning that if e1 holds then e2 is evaluated and
// otherwise e3 is evaluated.
type Ternary struct {
	condition, positiveBranch, negativeBranch Node
}

func (t Ternary) String() string {
	return fmt.Sprintf("(%v ? %v : %v)", t.condition, t.positiveBranch, t.negativeBranch)
}

func (t Ternary) Condition() Node {
	return t.condition
}

func (t Ternary) PositiveBranch() Node {
	return t.positiveBranch
}

func (t Ternary) NegativeBranch() Node {
	return t.negativeBranch
}

// Identifier specification nodes define all named entities that refer to some kind of object.
type Identifier struct {
	value string
}

func (i Identifier) String() string {
	return i.value
}

func (i Identifier) Value() string {
	return i.value
}

// Integer specification nodes are used for all parsed integers.
type Integer struct {
	value string
}

func (i Integer) String() string {
	return i.value
}

func (i Integer) Value() string {
	return i.value
}

// Dereference specification nodes are of the form *<operand>, e.g. *structVal or *variableName.
type Dereference struct {
	operand Node
}

func (d Dereference) String() string {
	return fmt.Sprintf("(*%v)", d.operand)
}

func (d Dereference) Operand() Node {
	return d.operand
}

// SquareBracket speficiation nodes are of the form <structure>[<index>], e.g. for the integer array a: a[42]
// or for the map m of integers to booleans: m[1337].
type SquareBracket struct {
	structure Node
	index     Node
}

func (s SquareBracket) String() string {
	return fmt.Sprintf("%v[%v]", s.structure, s.index)
}

func (s SquareBracket) Structure() Node {
	return s.structure
}

func (s SquareBracket) Index() Node {
	return s.index
}

// DotNotation specification nodes have the form <structure>.<field>, e.g. someStruct.someField
type DotNotation struct {
	structure Node
	field     Node
}

func (d DotNotation) String() string {
	return fmt.Sprintf("%v.%v", d.structure, d.field)
}

func (d DotNotation) Structure() Node {
	return d.structure
}

func (d DotNotation) Field() Node {
	return d.field
}

// ArrayLiteral specification nodes are of the form <arraytype><values>, where <arraytype> is defined below.
// Examples are [42]int{1, 2, 3} or [1337]bool{}.
type ArrayLiteral struct {
	arrayType ArrayType
	values    [][]Node // (key, value) tuples, where key can also be nil if not named
}

// StringNodeTuples creates a string for the output of a list of node tuples, e.g. the values of array or struct
// literals or the quantified variables list of universal or existential quantifiers.
func StringNodeTuples(values [][]Node, separator string) string {
	var nodeStrings []string
	for _, value := range values {
		if value[0] == nil {
			nodeStrings = append(nodeStrings, value[1].String())
		} else {
			nodeStrings = append(nodeStrings, value[0].String()+separator+value[1].String())
		}
	}
	return strings.Join(nodeStrings, ", ")
}

func (a ArrayLiteral) String() string {
	return fmt.Sprintf("%v{%v}", a.arrayType, StringNodeTuples(a.values, ":"))
}

func (a ArrayLiteral) Type() ArrayType {
	return a.arrayType
}

func (a ArrayLiteral) Values() [][]Node {
	return a.values
}

// ArrayType speficiation nodes are of the form [<length>]<arrayType>, e.g. [42]int or [1337][42]bool.
type ArrayType struct {
	arrayType Node
	length    Node
}

func (a ArrayType) String() string {
	if a.length != nil {
		return fmt.Sprintf("[%v]%v", a.length, a.arrayType)
	} else {
		return fmt.Sprintf("[]%v", a.arrayType)
	}
}

func (a ArrayType) Type() Node {
	return a.arrayType
}

func (a ArrayType) Length() Node {
	return a.length
}

// StructLiteral specification nodes are of the form <identifier><values>, e.g. someStruct{key: 42}.
type StructLiteral struct {
	identifier Node
	values     [][]Node // (key, value) tuples, where key can also be nil if not named
}

func (s StructLiteral) String() string {
	return fmt.Sprintf("%v{%v}", s.identifier, StringNodeTuples(s.values, ":"))
}

func (s StructLiteral) Identifier() Node {
	return s.identifier
}

func (s StructLiteral) Values() [][]Node {
	return s.values
}

// Purity specification nodes represent the purity annotations of functions. They do not hold any information
// but simply represent the annotations for their associated nodes.
type Purity struct {
}

func (p Purity) String() string {
	return fmt.Sprintf("pure")
}

// Old specification nodes are used to reason about values from previous program states. The label is used to specify
// which previous program state to use. If it is empty, the old expression refers to the program state at the
// beginning of the function. We address this as an "unlabelled old expression".
type Old struct {
	label      string // can be empty if old expression is unlabelled
	expression Node
}

func (o Old) String() string {
	if o.label != "" {
		return fmt.Sprintf("old[%s](%v)", o.label, o.expression)
	} else {
		return fmt.Sprintf("old(%v)", o.expression)
	}
}

func (o Old) Expression() Node {
	return o.expression
}

func (o Old) Label() string {
	return o.label
}

// Label specification nodes are used together with labelled old expressions. Labels are used to define which previous
// program states the old expressions should be evaluated in.
type Label struct {
	name string
}

func (l Label) String() string {
	return fmt.Sprintf("%v:", l.name)
}

func (l Label) Name() string {
	return l.name
}

// UnivQuantifier nodes represent universally quantified specifications. They are of the form
// forall (<identifier> <type>)+ :: domain ==> condition
type UnivQuantifier struct {
	quantifiedVars [][]Node // (identifier, type) list
	domain         *Domain  // can be empty if only boolean variables are used
	condition      Node
}

func (u UnivQuantifier) String() string {
	if u.domain != nil {
		return fmt.Sprintf("(forall %s :: %v ==> %v)",
			StringNodeTuples(u.quantifiedVars, " "), u.domain, u.condition)
	} else {
		return fmt.Sprintf("(forall %s :: %v)",
			StringNodeTuples(u.quantifiedVars, " "), u.condition)
	}
}

func (u UnivQuantifier) Domain() *Domain {
	return u.domain
}

func (u UnivQuantifier) Condition() Node {
	return u.condition
}

func (u UnivQuantifier) QuantifiedVars() [][]Node {
	return u.quantifiedVars
}

// ExistQuantifier nodes represent existentially quantified specifications. They are of the form
// exists (<identifier> <type>)+ :: domain ==> condition
type ExistQuantifier struct {
	quantifiedVars [][]Node // (identifier, type) list
	domain         *Domain
	condition      Node
}

func (e ExistQuantifier) String() string {
	if e.domain != nil {
		return fmt.Sprintf("(exists %s :: %v && %v)",
			StringNodeTuples(e.quantifiedVars, " "), e.domain, e.condition)
	} else {
		return fmt.Sprintf("(exists %s :: %v)",
			StringNodeTuples(e.quantifiedVars, " "), e.condition)
	}
}

func (e ExistQuantifier) Domain() *Domain {
	return e.domain
}

func (e ExistQuantifier) Condition() Node {
	return e.condition
}

func (e ExistQuantifier) QuantifiedVars() [][]Node {
	return e.quantifiedVars
}

// Domain nodes represent the domain expression of quantifiers. They are conjunctions or disjunctions of domain literals.
type Domain struct {
	isLeaf      bool
	literal     DomainLiteral // nil if non-leaf domain node
	left, right *Domain       // nil if leaf domain node
	operator    string        // either && or || if non-leaf, empty if leaf
}

func (d Domain) String() string {
	if d.left != nil && d.right != nil {
		return fmt.Sprintf("(%s %s %s)", d.left.String(), d.operator, d.right.String())
	} else {
		return d.literal.String()
	}
}

func (d Domain) IsLeaf() bool {
	return d.isLeaf
}

func (d Domain) DomainLiteral() DomainLiteral {
	return d.literal
}

func (d Domain) Left() *Domain {
	return d.left
}

func (d Domain) Right() *Domain {
	return d.right
}

func (d Domain) Operator() string {
	return d.operator
}

// DomainLiteral provides an interface for the two different types of domains: numeric domains and data structure domains.
type DomainLiteral interface {
	String() string
}

// NumericDomainLiteral nodes represent numeric domains of the form 'e1 < x <= e2' or similar.
type NumericDomainLiteral struct {
	variable                     Identifier
	lower, upper                 Node
	lowerRelation, upperRelation string // lowerRelation is either < or <=, upperRelation is either > or >=
}

func (ndl NumericDomainLiteral) String() string {
	return fmt.Sprintf("%v %s %v %s %v", ndl.lower, ndl.lowerRelation, ndl.variable, ndl.upperRelation, ndl.upper)
}

func (ndl NumericDomainLiteral) Variable() Identifier {
	return ndl.variable
}

func (ndl NumericDomainLiteral) Lower() Node {
	return ndl.lower
}

func (ndl NumericDomainLiteral) Upper() Node {
	return ndl.upper
}

func (ndl NumericDomainLiteral) LowerRelation() string {
	return ndl.lowerRelation
}

func (ndl NumericDomainLiteral) UpperRelation() string {
	return ndl.upperRelation
}

type LiteralType int

const (
	KEY = iota
	VALUE
	KEYVALUE
)

// DataStructureDomainLiteral nodes represent data structure domains of the form 'x in range map/array/slice' or similar.
type DataStructureDomainLiteral struct {
	literalType LiteralType
	key, value  *Identifier // at least one of these two is not equal to nil
	structure   Node
}

func (ddl DataStructureDomainLiteral) String() string {
	switch ddl.literalType {
	case KEYVALUE:
		return fmt.Sprintf("(%s, %s) in range %v", ddl.key.String(), ddl.value.String(), ddl.structure)
	case KEY:
		return fmt.Sprintf("%s in range %v", ddl.key.String(), ddl.structure)
	default:
		// case VALUE
		return fmt.Sprintf("(_, %s) in range %v", ddl.value.String(), ddl.structure)
	}
}

func (ddl DataStructureDomainLiteral) LiteralType() LiteralType {
	return ddl.literalType
}

func (ddl DataStructureDomainLiteral) Key() *Identifier {
	return ddl.key
}

func (ddl DataStructureDomainLiteral) Value() *Identifier {
	return ddl.value
}

func (ddl DataStructureDomainLiteral) Structure() Node {
	return ddl.structure
}

// Access specification nodes are used to reason about access permissions for fields. They are of the form
// acc(<operand>) where the operand either refers to some field, e.g. acc(structVariable.field), to a dereference,
// e.g. acc(*<operand>) or a reference acc(&<operand>). Note that the unary & operator can only be used inside
// access permissions.
type Access struct {
	operand Node
}

func (a Access) String() string {
	return fmt.Sprintf("acc(%v)", a.operand)
}

func (a Access) Operand() Node {
	return a.operand
}

// Call specification nodes represent calls to functions. They are of the form
// <funcName>(<expression1>, ..., <expressionN>)
// where the function name is a node refering to some function and the expressions 1 - N are the parameters for the call.
type Call struct {
	function   Node
	parameters []Node // can be empty if no parameters exist
}

// stringNodeArray creates a string for the output of an array of nodes, e.g. the parameters of a function call.
func stringNodeArray(nodes []Node) string {
	var nodeStrings []string
	for _, value := range nodes {
		nodeStrings = append(nodeStrings, value.String())
	}
	return strings.Join(nodeStrings, ", ")
}

func (c Call) String() string {
	return fmt.Sprintf("%v(%s)", c.function, stringNodeArray(c.parameters))
}

func (c Call) Function() Node {
	return c.function
}

func (c Call) Parameters() []Node {
	return c.parameters
}

// SharedVars nodes represent the annotation of whether variables used in old-expressions are shared. They are of
// the form
// shared: <identifier1>, ... , <identifierN>
type SharedVars struct {
	variables []Identifier
}

func (a SharedVars) String() string {
	var variableNodes []Node
	for _, variable := range a.variables {
		variableNodes = append(variableNodes, variable)
	}
	return fmt.Sprintf("shared: %s", stringNodeArray(variableNodes))
}
func (a SharedVars) Variables() []Identifier {
	return a.variables
}

// ExclusiveVars nodes represent the annotation of whether variables used in old-expressions are exclusive. They are of
// the form
// exclusive: <identifier1>, ... , <identifierN>
type ExclusiveVars struct {
	variables []Identifier
}

func (n ExclusiveVars) String() string {
	var variableNodes []Node
	for _, variable := range n.variables {
		variableNodes = append(variableNodes, variable)
	}
	return fmt.Sprintf("exclusive: %s", stringNodeArray(variableNodes))
}
func (n ExclusiveVars) Variables() []Identifier {
	return n.variables
}

// Predicate nodes represent predicates which can be interpreted as functions written as part of the specification.
// They are of the form
// predicate <name>((<identifier> <type>)*) { <assertion> }
type Predicate struct {
	name       Identifier
	parameters [][]Node // (identifier, type) list, can be empty if no parameters
	assertion  Node
}

func (p Predicate) String() string {
	return fmt.Sprintf("predicate %v(%s) { %v }",
		p.name, StringNodeTuples(p.parameters, " "), p.assertion)
}

func (p Predicate) Name() Identifier {
	return p.name
}

func (p Predicate) Parameters() [][]Node {
	return p.parameters
}

func (p Predicate) Assertion() Node {
	return p.assertion
}
