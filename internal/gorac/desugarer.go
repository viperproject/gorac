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
	"go/types"
	"golang.org/x/tools/go/ast/astutil"
	"log"
	"math/rand"
	"reflect"
	"regexp"
	"strconv"
	"strings"
)

// Desugarer holds all objects needed for desugaring specparser nodes.
type Desugarer struct {
	tokenFile            *token.File
	pkg                  *types.Package
	astFile              *ast.File
	oldVariableNameRegex *regexp.Regexp
	quantifiedVarsMap    map[string]*Identifier
	predicateVarsMap     map[string]Identifier
	predicateInfoMap     *map[string]*PredicateInfo
}

// NewDesugarer creates and returns a new Desugarer object.
func NewDesugarer(tokenFile *token.File, pkg *types.Package, astFile *ast.File,
	predicateInfoMap *map[string]*PredicateInfo) (d *Desugarer) {
	return &Desugarer{
		tokenFile:            tokenFile,
		pkg:                  pkg,
		astFile:              astFile,
		oldVariableNameRegex: regexp.MustCompile("[a-zA-Z]+"),
		quantifiedVarsMap:    make(map[string]*Identifier),
		predicateVarsMap:     make(map[string]Identifier),
		predicateInfoMap:     predicateInfoMap,
	}
}

// desugar converts a given specparser node into an internal ast node. During desugaring typing information is determined
// and added to the nodes. Some runtime assertion specific type checks that are not covered by the type checker used on
// specInfo objects are performed.
func (d *Desugarer) desugar(node specparser.Node, nodePos, specPos token.Pos) Node {
	switch node.(type) {
	case specparser.Integer:
		return d.desugarInteger(node.(specparser.Integer))
	case specparser.Identifier:
		return d.desugarIdentifier(node.(specparser.Identifier), nodePos, specPos)
	case specparser.Unary:
		return d.desugarUnary(node.(specparser.Unary), nodePos, specPos)
	case specparser.Dereference:
		return d.desugarDereference(node.(specparser.Dereference), nodePos, specPos)
	case specparser.Binary:
		return d.desugarBinary(node.(specparser.Binary), nodePos, specPos)
	case specparser.Ternary:
		return d.desugarTernary(node.(specparser.Ternary), nodePos, specPos)
	case specparser.SquareBracket:
		return d.desugarSquareBracket(node.(specparser.SquareBracket), nodePos, specPos)
	case specparser.DotNotation:
		return d.desugarDotNotation(node.(specparser.DotNotation), nodePos, specPos)
	case specparser.ArrayLiteral:
		return d.desugarArrayLiteral(node.(specparser.ArrayLiteral), nodePos, specPos)
	case specparser.ArrayType:
		return d.desugarArrayType(node.(specparser.ArrayType), nodePos, specPos)
	case specparser.StructLiteral:
		return d.desugarStructLiteral(node.(specparser.StructLiteral), nodePos, specPos)
	case specparser.Old:
		return d.desugarOld(node.(specparser.Old), nodePos, specPos)
	case specparser.Access:
		return d.desugarAccess(node.(specparser.Access), nodePos, specPos)
	case specparser.Call:
		return d.desugarCall(node.(specparser.Call), nodePos, specPos)
	case specparser.UnivQuantifier:
		return d.desugarUnivQuantifier(node.(specparser.UnivQuantifier), nodePos, specPos)
	case specparser.ExistQuantifier:
		return d.desugarExistQuantifier(node.(specparser.ExistQuantifier), nodePos, specPos)
	case specparser.Domain:
		return d.desugarDomain(node.(specparser.Domain), nodePos, specPos)
	case specparser.NumericDomainLiteral:
		return d.desugarNumericDomainLiteral(node.(specparser.NumericDomainLiteral), nodePos, specPos)
	case specparser.DataStructureDomainLiteral:
		return d.desugarDataStructureDomainLiteral(node.(specparser.DataStructureDomainLiteral), nodePos, specPos)
	default:
		panic(fmt.Sprintf("At line %v desugaring not possible for invalid specparser.Node '%v'",
			d.tokenFile.Line(nodePos), node))
	}
}

// desugarInteger returns an internal integer node corresponding to the given specparser integer node.
func (d *Desugarer) desugarInteger(s specparser.Integer) Node {
	return &Integer{
		type_: types.Typ[types.Int],
		value: s.Value(),
	}
}

// desugarIdentifier looks up the object the parsed identifer refers to and if found, returns an internal identifier
// object that holds the identifiers name as its value and the found object's type. If no object that corresponds to
// the given name is found in the scope of the specification, the function panics.
func (d *Desugarer) desugarIdentifier(identifier specparser.Identifier, nodePos, specPos token.Pos) Node {
	name := identifier.Value()
	inner := d.pkg.Scope().Innermost(nodePos)
	if _, obj := inner.LookupParent(name, nodePos); obj != nil {
		return d.checkIdentifier(name, specPos, identifier, obj.Type())
	} else if obj := inner.Lookup(name); obj != nil {
		return d.checkIdentifier(name, specPos, identifier, obj.Type())
	} else if quantifiedVar, ok := d.quantifiedVarsMap[name]; ok {
		log.Printf("At line %d identifier '%v' has type '%v'.", d.tokenFile.Line(specPos), identifier, quantifiedVar.type_)
		return quantifiedVar
	} else if predicateVar, ok := d.predicateVarsMap[name]; ok {
		log.Printf("At line %d identifier '%v' has type '%v'.", d.tokenFile.Line(specPos), identifier, predicateVar.type_)
		return &predicateVar
	} else {
		panic(fmt.Sprintf("At line %d identifier '%v' undefined or not in scope.", d.tokenFile.Line(specPos), identifier))
	}
}

// checkIdentifier checks for a given identifier that has been declared in the current scope whether the identifier has
// also been used as a quantified variable. If so, an error is thrown. If not, a desugared identifier object is returned.
func (d *Desugarer) checkIdentifier(name string, specPos token.Pos, identifier specparser.Identifier, type_ types.Type) Node {
	if _, ok := d.quantifiedVarsMap[name]; ok {
		panic(fmt.Sprintf("At line %d identifier '%v' defined both in scope and quantifier.", d.tokenFile.Line(specPos), identifier))
	}
	log.Printf("At line %d identifier '%v' has type '%v'.", d.tokenFile.Line(specPos), identifier, type_)
	return &Identifier{
		type_: type_,
		value: name,
	}
}

// desugarBinary returns an internal binary node corresponding to the given specparser binary node. Arithmetic operations
// receive integer types, boolean operations are bool.
func (d *Desugarer) desugarBinary(b specparser.Binary, nodePos, specPos token.Pos) Node {
	left := d.desugar(b.Left(), nodePos, specPos)
	right := d.desugar(b.Right(), nodePos, specPos)
	switch b.Operator() {
	case "*", "/", "+", "-", "%":
		return Binary{
			type_:    types.Typ[types.Int],
			operator: b.Operator(),
			left:     left,
			right:    right,
		}
	default: // Boolean ||, && or ==>
		return Binary{
			type_:    types.Typ[types.Bool],
			operator: b.Operator(),
			left:     left,
			right:    right,
		}
	}
}

// desugarTernary returns an internal ternary node corresponding to the given specparser ternary node. For ternary
// operations of the form <expression> ? <assertion1> : <assertion2>, the two assertions need to be of the same type.
func (d *Desugarer) desugarTernary(ternary specparser.Ternary, nodePos, specPos token.Pos) Node {
	condition := d.desugar(ternary.Condition(), nodePos, specPos)
	if condition.Type() != types.Typ[types.Bool] && condition.Type() != types.Typ[types.UntypedBool] {
		panic(fmt.Sprintf("Condition '%v' of ternary operator '%v' at line %d needs to be boolean",
			condition, ternary, d.tokenFile.Line(specPos)))
	}
	positiveBranch := d.desugar(ternary.PositiveBranch(), nodePos, specPos)
	if positiveBranch.Type() != types.Typ[types.Bool] && positiveBranch.Type() != types.Typ[types.UntypedBool] {
		panic(fmt.Sprintf("Branch '%v' of ternary operator '%v' at line %d needs to be boolean",
			positiveBranch, ternary, d.tokenFile.Line(specPos)))
	}
	negativeBranch := d.desugar(ternary.NegativeBranch(), nodePos, specPos)
	if negativeBranch.Type() != types.Typ[types.Bool] && negativeBranch.Type() != types.Typ[types.UntypedBool] {
		panic(fmt.Sprintf("Branch '%v' of ternary operator '%v' at line %d needs to be boolean",
			negativeBranch, ternary, d.tokenFile.Line(specPos)))
	}
	return Ternary{
		condition:      condition,
		positiveBranch: positiveBranch,
		negativeBranch: negativeBranch,
		type_:          positiveBranch.Type(),
	}
}

// desugarDereference returns an internal dereference node corresponding to the given specparser dereference node. The
// type is equal to the type the operand is pointing toward.
func (d *Desugarer) desugarDereference(u specparser.Dereference, nodePos, specPos token.Pos) Node {
	operand := d.desugar(u.Operand(), nodePos, specPos)
	if ptr, ok := operand.Type().(*types.Pointer); ok {
		return &Dereference{
			type_:   ptr.Elem(),
			operand: operand,
		}
	} else {
		panic(fmt.Sprintf("Dereferenced expression '%v' at line %v must have a pointer type, has type '%v'",
			operand, d.tokenFile.Line(specPos), operand.Type()))
	}
}

// desugarUnary returns an internal unary node corresponding to the given specparser unary. Negations are of boolean
// types while plus or minus unary operations are of integer type.
func (d *Desugarer) desugarUnary(u specparser.Unary, nodePos, specPos token.Pos) Node {
	operand := d.desugar(u.Operand(), nodePos, specPos)
	switch u.Operator() {
	case "!":
		return &Unary{
			type_:    types.Typ[types.Bool],
			operand:  operand,
			operator: u.Operator(),
		}
	case "&": // should only be used inside access permissions
		return &Unary{
			type_:    &types.Pointer{},
			operand:  operand,
			operator: u.Operator(),
		}
	default: // Unary + or -
		return &Unary{
			type_:    types.Typ[types.Int],
			operand:  operand,
			operator: u.Operator(),
		}
	}
}

// desugarSquareBracket returns an internal square bracket node corresponding to the given specparser square bracket. The
// type is equal to the operands type.
func (d *Desugarer) desugarSquareBracket(s specparser.SquareBracket, nodePos, specPos token.Pos) Node {
	structure := d.desugar(s.Structure(), nodePos, specPos)
	index := d.desugar(s.Index(), nodePos, specPos)
	return &SquareBracket{
		type_:     d.getSquareBracketType(structure.Type(), s, nodePos, specPos),
		structure: structure,
		index:     index,
	}
}

// getSquareBracketType retrieves the underlying type of the square bracket (i.e. the array, slice or map access).
func (d *Desugarer) getSquareBracketType(t types.Type, s specparser.SquareBracket, nodePos, specPos token.Pos) types.Type {
	switch t.(type) {
	case *types.Array:
		return t.(*types.Array).Elem()
	case *types.Slice:
		return t.(*types.Slice).Elem()
	case *types.Map:
		return t.(*types.Map).Elem()
	case *types.Pointer: // syntactic sugar of Go allows x[0] for what is actually (*x)[0]
		return d.getSquareBracketType(t.(*types.Pointer).Elem(), s, nodePos, specPos)
	default:
		panic(fmt.Sprintf("Invalid type '%v' for structure used in square bracket '%v' at line %v",
			t, s, d.tokenFile.Line(specPos)))
	}
}

// desugarDotNotation returns an internal dot notation node corresponding to the given specparser dot notation. It is
// checked whether the dot notation is performed on a struct. The type of the dot notation object corresponds to the
// selected field.
func (d *Desugarer) desugarDotNotation(dotN specparser.DotNotation, nodePos, specPos token.Pos) Node {
	structure := d.desugar(dotN.Structure(), nodePos, specPos)
	var structType *types.Struct
	var ok bool
	switch structure.Type().(type) {
	case *types.Pointer:
		ptr, _ := (structure.Type()).(*types.Pointer)
		structType, ok = ptr.Elem().Underlying().(*types.Struct)
		// Check whether implicit dereference needs to be added to internal AST
		if _, isDereference := (structure).(*Dereference); !isDereference {
			structure = &Dereference{
				type_:   structure.Type(),
				operand: structure,
			}
		}
	case *types.Struct, *types.Named:
		structType, ok = (structure.Type().Underlying()).(*types.Struct)
	}
	if !ok {
		panic(fmt.Sprintf("At line %d field access '%v': data structure must be struct or pointer to struct, found '%v': '%v'",
			d.tokenFile.Line(specPos), dotN, dotN.Structure(), structure.Type()))
	}
	fieldType := d.lookupFieldType(structType, dotN, nodePos, specPos)
	return &DotNotation{
		type_:     fieldType,
		structure: structure,
		field: &Identifier{
			type_: fieldType,
			value: dotN.Field().String(),
		},
	}
}

func (d *Desugarer) lookupFieldType(structType *types.Struct, dotN specparser.DotNotation, nodePos token.Pos,
	specPos token.Pos) types.Type {
	var fieldType types.Type
	for i := 0; i < structType.NumFields(); i++ { // Iterate over all fields of the struct
		if dotN.Field().String() == structType.Field(i).Name() {
			fieldType = structType.Field(i).Type() // If field that is selected is found, save its type to return
			break
		}
	}
	if fieldType == nil {
		if method := d.lookupMethod(dotN.Field().String()); method != nil {
			typeName := method.Type.Results.List[0].Type.(*ast.Ident).Name
			inner := d.pkg.Scope().Innermost(nodePos)
			if _, obj := inner.LookupParent(typeName, nodePos); obj != nil {
				fieldType = obj.Type()
			}
		} else {
			panic(fmt.Sprintf("At line %d field access '%v' has no field or method with name '%s'",
				d.tokenFile.Line(specPos), dotN, dotN.Field().String()))
		}
	}
	return fieldType
}

func (d *Desugarer) lookupMethod(methodName string) *ast.FuncDecl {
	var method *ast.FuncDecl
	astutil.Apply(d.astFile, func(c *astutil.Cursor) bool {
		if fun, ok := c.Node().(*ast.FuncDecl); ok {
			if fun.Name.Name == methodName {
				method = c.Node().(*ast.FuncDecl)
				return false
			}
		}
		return true
	}, nil)
	return method
}

// desugarArrayLiteral returns an internal array literal node corresponding to the given specparser array literal. The
// type is equal to the array type's type. If keys are provided in the list of array literal members, they are desugared
// as well.
func (d *Desugarer) desugarArrayLiteral(a specparser.ArrayLiteral, nodePos, specPos token.Pos) Node {
	arrayType := d.desugar(a.Type(), nodePos, specPos).(*ArrayType)
	var values [][]Node
	for _, tuple := range a.Values() {
		var key, value Node
		value = d.desugar(tuple[1], nodePos, specPos)
		if tuple[0] != nil {
			key = &Identifier{
				type_: value.Type(),
				value: tuple[0].String(),
			}
		}
		values = append(values, []Node{key, value})
	}
	return &ArrayLiteral{
		type_:     arrayType.Type(),
		arrayType: *arrayType,
		values:    values,
	}
}

// desugarArrayType returns an internal array type node corresponding to the given specparser array type. The
// type is equal to the underlying array type.
func (d *Desugarer) desugarArrayType(a specparser.ArrayType, nodePos, specPos token.Pos) Node {
	arrayType := d.desugar(a.Type(), nodePos, specPos)
	if a.Length() != nil {
		length := d.desugar(a.Length(), nodePos, specPos)
		evalLen, evalLenErr := strconv.Atoi(length.String())
		if evalLenErr != nil {
			// if "length" is not a single integer but a complex expression, evalLen is 0 because evaluating
			// "length" is not possible before runtime
			evalLen = 0
		}
		return &ArrayType{
			type_:     types.NewArray(arrayType.Type(), int64(evalLen)),
			arrayType: arrayType,
			length:    length,
		}
	} else {
		return &ArrayType{
			type_:     types.NewSlice(arrayType.Type()),
			arrayType: arrayType,
		}
	}
}

// desugarStructLiteral returns an internal struct literal node corresponding to the given specparser struct literal. The
// type is equal to the struct identifiers type. If keys are provided in the list of struct literal members, they are
// desugared as well.
func (d *Desugarer) desugarStructLiteral(s specparser.StructLiteral, nodePos, specPos token.Pos) Node {
	identifier := d.desugar(s.Identifier(), nodePos, specPos)
	var values [][]Node
	for _, tuple := range s.Values() {
		var key, value Node
		value = d.desugar(tuple[1], nodePos, specPos)
		if tuple[0] != nil {
			key = &Identifier{
				type_: value.Type(),
				value: tuple[0].String(),
			}
		}
		values = append(values, []Node{key, value})
	}
	return &StructLiteral{
		type_:      identifier.Type(),
		identifier: identifier,
		values:     values,
	}
}

func (d *Desugarer) desugarOld(o specparser.Old, nodePos, specPos token.Pos) Node {
	expression := d.desugar(o.Expression(), nodePos, specPos)
	starReplaced := strings.ReplaceAll(o.Expression().String(), "*", "star")
	identString := strings.Join(d.oldVariableNameRegex.FindAllString(starReplaced, -1), "")
	//identString := d.oldVariableNameRegex.ReplaceAllString(, "")
	identifier := Identifier{
		type_: expression.Type(),
		// Important: Name must contain "OLD" in order to be recognizable as an old identifier.
		// This is used by gorac.util.isOldExpression and gorac.util.isOldAssignment when distinguishing the place
		// where a postcondition needs to be put in the corresponding function body.
		value: fmt.Sprintf("%s%sOLD%d", identString, o.Label(), rand.Intn(100)),
	}
	return &Old{
		type_:      expression.Type(),
		label:      o.Label(),
		expression: expression,
		identifier: identifier,
	}
}

func (d *Desugarer) desugarAccess(a specparser.Access, nodePos, specPos token.Pos) Node {
	// Access permissions can only be stated on identifiers referring to pointers and dot notations with their structure
	// being a pointer (which would have already been desugared into a dereference before).
	operand := d.desugar(a.Operand(), nodePos, specPos)
	switch operand.(type) {
	case *Unary:
		unary := operand.(*Unary)
		if unary.operator == "&" {
			// References used in access permissions need to be pure. Taking the address of a composite literal is not
			// deterministic, thus the operation & on composite literals is not pure. Is this the case, an error is thrown.
			switch unary.operand.(type) {
			case *StructLiteral, *ArrayLiteral:
				panic(fmt.Sprintf("Reference used in access permission '%v' at line %d impure on composite literal.",
					a, d.tokenFile.Line(specPos)))
			}
			return Access{
				type_:   types.Typ[types.Bool],
				operand: unary,
			}
		}
	case *DotNotation:
		dotNotation := operand.(*DotNotation)
		if _, ok := dotNotation.structure.(*Dereference); ok {
			return Access{
				type_:   types.Typ[types.Bool],
				operand: dotNotation.structure,
			}
		}
	case *Identifier:
		isPointerType := false
		if _, ok := operand.Type().(*types.Pointer); ok {
			isPointerType = true
		} else if _, ok := operand.Type().(*types.Slice); ok {
			isPointerType = true
		} else if _, ok := operand.Type().(*types.Map); ok {
			isPointerType = true
		}
		if isPointerType {
			return Access{
				type_:   types.Typ[types.Bool],
				operand: operand,
			}
		}
	}
	panic(fmt.Sprintf("Access permission '%v' at line %d must contain field access, pointer or reference, has '%v'",
		a, d.tokenFile.Line(specPos), reflect.TypeOf(a.Operand())))
}

func (d *Desugarer) desugarCall(c specparser.Call, nodePos, specPos token.Pos) Node {
	switch c.Function().(type) {
	case specparser.Identifier:
		// Check whether we are dealing with a predicate call. If so, return the desugared predicate call.
		if predicate := (*d.predicateInfoMap)[c.Function().(specparser.Identifier).Value()]; predicate != nil {
			return d.desugarPredicateCall(c, nodePos, specPos, predicate)
		}
	case specparser.DotNotation:
		// fall through
	default:
		panic(fmt.Sprintf("The function used in the call expression '%v' at line %d must be an identifier or dot notation, is '%T'",
			c, d.tokenFile.Line(specPos), c.Function()))
	}
	return d.desugarFunctionCall(c, nodePos, specPos)
}

func (d *Desugarer) desugarPredicateCall(c specparser.Call, nodePos, specPos token.Pos, predicate *PredicateInfo) Node {
	predicateScope := d.pkg.Scope().Innermost(predicate.pos)
	// Check that the predicate definition is in the same scope as the predicate call
	if !predicateScope.Contains(nodePos) {
		panic(fmt.Sprintf("Predicate call '%v' at line %d out of scope of predicate declaration '%v' at line %d",
			c, d.tokenFile.Line(specPos), predicate, d.tokenFile.Line(predicate.pos)))
	}
	// Desugar the predicate's assertion and its parameters. This also sets the field predicate.GenerateRAC to true in
	// order to later include a function definition into the Go AST.
	predicate.ComputeDesugaredNode(d)
	// Check that each value passed into the predicate has the correct type
	var parameterValues []Node
	for _, p := range c.Parameters() {
		parameterValues = append(parameterValues, d.desugar(p, nodePos, specPos))
	}
	if variable, value, correctType, actualType, ok := checkParameterTypes(parameterValues, predicate.desugaredParameters); !ok {
		panic(fmt.Sprintf("Cannot use type '%v' of value '%v' as type '%v' for parameter '%v' in predicate call '%v' at line %d",
			actualType, value, correctType, *variable, c, d.tokenFile.Line(specPos)))
	}
	return PredicateCall{
		type_:      types.Typ[types.Bool],
		parameters: parameterValues,
		predicate:  predicate,
	}
}

// checkParameterTypes iterates over all values passed into a given predicate call. For each value it checks whether
// its type corresponds to the belonging variable's types. If all types match, 'true' and four nil values are returned.
// If a value does not match the type of the corresponding variable, 'false' is returned together with the value, the
// variable and both of their mismatching types.
func checkParameterTypes(parameterValues []Node, parameterVariables []Identifier) (variable *Identifier, value Node,
	correctType, actualType types.Type, ok bool) {
	for i := range parameterValues {
		value := parameterValues[i]
		variable := parameterVariables[i]
		if getTypeIdentifier(value.Type()) != getTypeIdentifier(variable.Type()) {
			return &variable, value, variable.Type(), value.Type(), false
		}
	}
	return nil, nil, nil, nil, true
}

func (d *Desugarer) desugarFunctionCall(c specparser.Call, nodePos token.Pos, specPos token.Pos) Node {
	function := d.desugar(c.Function(), nodePos, specPos)
	var parameters []Node
	for _, p := range c.Parameters() {
		parameters = append(parameters, d.desugar(p, nodePos, specPos))
	}
	var type_ types.Type
	switch function.(type) {
	case *DotNotation, DotNotation:
		type_ = function.Type()
	case *Identifier:
		name := function.(*Identifier).value
		// Quote from types package: Builtins don't have a valid type.
		// See: https://golang.org/pkg/go/types/#Builtin
		// Thus, for built-in functions, the type will be nil.
		if name == "len" || name == "cap" {
			type_ = types.Typ[types.Int]
		} else {
			type_ = d.getSignatureType(function, c, specPos)
		}
	default:
		type_ = d.getSignatureType(function, c, specPos)
	}
	return FunctionCall{
		type_:      type_,
		function:   function,
		parameters: parameters,
	}
}

func (d *Desugarer) getSignatureType(function Node, c specparser.Call, specPos token.Pos) types.Type {
	sig, ok := function.Type().(*types.Signature)
	if !ok {
		panic(fmt.Sprintf("Function call expression '%v' at line %d must be of type signature, has '%v'",
			c, d.tokenFile.Line(specPos), function.Type()))
	}
	return sig.Results().At(0).Type()
}

func (d *Desugarer) desugarUnivQuantifier(uq specparser.UnivQuantifier, nodePos, specPos token.Pos) Node {
	var quantifiedVars []Identifier
	// Add quantifier variables to quantified variable map such that they can be found when desugaring the domain and 
	// condition of the quantifier.
	for _, tuple := range uq.QuantifiedVars() {
		variable := d.desugarQuantifiedVariable(uq, tuple, nodePos, specPos)
		if _, ok := d.quantifiedVarsMap[variable.value]; ok {
			panic(fmt.Sprintf("Quantified variable '%v' from quantifier '%v' at line %d must have unique name",
				variable, uq, d.tokenFile.Line(specPos)))
		}
		d.quantifiedVarsMap[variable.value] = &variable
		quantifiedVars = append(quantifiedVars, variable)
	}
	condition := d.desugar(uq.Condition(), nodePos, specPos)
	var domainPtr *Domain
	if uq.Domain() != nil {
		domain := d.desugar(*uq.Domain(), nodePos, specPos).(Domain)
		domainPtr = &domain
	}
	// Remove all quantified variables from the quantified variable map such that they are not bound when desugaring
	// further quantifiers that might be used in the same expression.
	for _, quantifiedVar := range quantifiedVars {
		delete(d.quantifiedVarsMap, quantifiedVar.value)
	}
	return UnivQuantifier{
		quantifiedVars: quantifiedVars,
		domain:         domainPtr,
		condition:      condition,
	}
}

func (d *Desugarer) desugarExistQuantifier(eq specparser.ExistQuantifier, nodePos, specPos token.Pos) Node {
	var quantifiedVars []Identifier
	// Add quantifier variables to quantified variable map such that they can be found when desugaring the domain and
	// condition of the quantifier.
	for _, tuple := range eq.QuantifiedVars() {
		variable := d.desugarQuantifiedVariable(eq, tuple, nodePos, specPos)
		if _, ok := d.quantifiedVarsMap[variable.value]; ok {
			panic(fmt.Sprintf("Quantified variable '%v' from quantifier '%v' at line %d must have unique name",
				variable, eq, d.tokenFile.Line(specPos)))
		}
		d.quantifiedVarsMap[variable.value] = &variable
		quantifiedVars = append(quantifiedVars, variable)
	}
	condition := d.desugar(eq.Condition(), nodePos, specPos)
	var domainPtr *Domain
	if eq.Domain() != nil {
		domain := d.desugar(*eq.Domain(), nodePos, specPos).(Domain)
		domainPtr = &domain
	}
	// Remove all quantified variables from the quantified variable map such that they are not bound when desugaring
	// further quantifiers that might be used in the same expression.
	for _, quantifiedVar := range quantifiedVars {
		delete(d.quantifiedVarsMap, quantifiedVar.value)
	}
	return ExistQuantifier{
		quantifiedVars: quantifiedVars,
		domain:         domainPtr,
		condition:      condition,
	}
}

func (d *Desugarer) desugarDomain(domain specparser.Domain, nodePos, specPos token.Pos) Node {
	if !domain.IsLeaf() {
		left := d.desugar(*domain.Left(), nodePos, specPos).(Domain)
		right := d.desugar(*domain.Right(), nodePos, specPos).(Domain)
		return Domain{
			isLeaf:   false,
			left:     &left,
			right:    &right,
			operator: domain.Operator(),
		}
	} else {
		return Domain{
			isLeaf:  true,
			literal: d.desugar(domain.DomainLiteral(), nodePos, specPos).(DomainLiteral),
		}
	}
}

func (d *Desugarer) desugarNumericDomainLiteral(ndl specparser.NumericDomainLiteral, nodePos, specPos token.Pos) Node {
	identifier := ndl.Variable()
	variable := d.checkDeclaration(&identifier, ndl, specPos)
	lower := d.desugar(ndl.Lower(), nodePos, specPos)
	upper := d.desugar(ndl.Upper(), nodePos, specPos)
	return NumericDomainLiteral{
		variable:      variable,
		lower:         lower,
		upper:         upper,
		lowerRelation: ndl.LowerRelation(),
		upperRelation: ndl.UpperRelation(),
	}
}

func (d *Desugarer) desugarDataStructureDomainLiteral(ddl specparser.DataStructureDomainLiteral, nodePos, specPos token.Pos) Node {
	var keyPtr, valuePtr *Identifier
	var literalType LiteralType
	switch ddl.LiteralType() {
	case specparser.KEY:
		keyPtr = d.checkDeclaration(ddl.Key(), ddl, specPos)
		literalType = KEY
	case specparser.VALUE:
		valuePtr = d.checkDeclaration(ddl.Value(), ddl, specPos)
		literalType = VALUE
	case specparser.KEYVALUE:
		keyPtr = d.checkDeclaration(ddl.Key(), ddl, specPos)
		valuePtr = d.checkDeclaration(ddl.Value(), ddl, specPos)
		literalType = KEYVALUE
	}
	structure := d.desugar(ddl.Structure(), nodePos, specPos)
	return DataStructureDomainLiteral{
		literalType: literalType,
		key:         keyPtr,
		value:       valuePtr,
		structure:   structure,
	}
}

func (d *Desugarer) checkDeclaration(variable *specparser.Identifier, dl specparser.DomainLiteral,
	specPos token.Pos) *Identifier {
	identifier, ok := d.quantifiedVarsMap[variable.Value()]
	if !ok {
		panic(fmt.Sprintf("Quantified variable '%v' used in domain '%v' at line %d is not declared",
			variable, dl, d.tokenFile.Line(specPos)))
	}
	return identifier
}

// desugarQuantifiedVariable desugars quantified variables since desugaring quantified variables as regular identifiers
// would not work because their identifiers won't be in scope.
func (d *Desugarer) desugarQuantifiedVariable(quantifier specparser.Node, tuple []specparser.Node, nodePos, specPos token.Pos) Identifier {
	variable, okVariable := tuple[0].(specparser.Identifier)
	if !okVariable {
		panic(fmt.Sprintf("Quantifier '%v' at line %d must have identifier as quantified variable, has '%v'",
			quantifier, d.tokenFile.Line(specPos), tuple[0]))
	}
	type_, okType := tuple[1].(specparser.Identifier)
	if !okType {
		panic(fmt.Sprintf("Quantifier '%v' at line %d must have identifier as type of quantified variable '%v', has '%v'",
			quantifier, d.tokenFile.Line(specPos), tuple[0], tuple[1]))
	}
	desugaredType := d.desugar(type_, nodePos, specPos).(*Identifier)
	return Identifier{
		type_: desugaredType.type_,
		value: variable.Value(),
	}
}
