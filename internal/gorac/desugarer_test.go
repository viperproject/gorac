// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"bytes"
	"log"
	"os"
	"strings"
	"testing"
)

// Unit tests for desugarer.go

func TestUnary(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	import "fmt"
	func foo() {
		bar := true 
		//@ assert !bar && +42 - -42 != 0
		fmt.Println(bar)
	}`
	ComputeRuntimeAssertionChecks(config, input)
	logString := strings.Join(strings.Split(buf.String(), " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 5 identifier 'bar' has type 'bool'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestSquareBracket(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	import "fmt"
	func foo() {
		bar := [42]int{1, 2, 3} 
		//@ assert bar[1] == 2
		fmt.Println(bar)
	}`
	ComputeRuntimeAssertionChecks(config, input)
	logString := strings.Join(strings.Split(buf.String(), " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 5 identifier 'bar' has type '[42]int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestDotNotation_Success(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	import "fmt"
	func foo() {
		bar := struct {
			val int
		} {
			val: 42,
		}
		//@ assert bar.val == 42
		fmt.Println(bar)
	}`
	ComputeRuntimeAssertionChecks(config, input)
	logString := strings.Join(strings.Split(buf.String(), " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 9 identifier 'bar' has type 'struct{val int}'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestDotNotation_Panic(t *testing.T) {
	wantPanic := "At line 5 field access 'x.bar': data structure must be struct or pointer to struct, found 'x': 'int'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	import "fmt"
	func foo() {
		x := 42
		//@ assert x.bar == 42
		fmt.Println(x)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestArrayLiteral(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	import "fmt"
	func foo() {
		bar := [42]int{1, 2, 3} 
		//@ assert bar != [42]int{3, 2, 1}
		fmt.Println(bar)
	}`
	ComputeRuntimeAssertionChecks(config, input)
	loggedLines := strings.Split(buf.String(), "\n")
	logString := strings.Join(strings.Split(loggedLines[0], " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 5 identifier 'bar' has type '[42]int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
	logString = strings.Join(strings.Split(loggedLines[1], " ")[2:], " ")
	t.Log(logString)
	wantLog = "At line 5 identifier 'int' has type 'int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestStructLiteral(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	import "fmt"
	type s struct {
		val int
	}
	func foo() {
		bar := s{42} 
		//@ assert bar != s{val: 1337} 
		fmt.Println(bar)
	}`
	ComputeRuntimeAssertionChecks(config, input)
	loggedLines := strings.Split(buf.String(), "\n")
	logString := strings.Join(strings.Split(loggedLines[0], " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 8 identifier 'bar' has type 'cmd/gorac.s'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
	logString = strings.Join(strings.Split(loggedLines[1], " ")[2:], " ")
	t.Log(logString)
	wantLog = "At line 8 identifier 's' has type 'cmd/gorac.s'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestOld(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	//@ requires x != 42
	func foo(x int) {
		x = 42 //@ shared: x	
		//@ assert old(x) != 42 
	}`
	ComputeRuntimeAssertionChecks(config, input)
	loggedLines := strings.Split(buf.String(), "\n")
	logString := strings.Join(strings.Split(loggedLines[0], " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 2 identifier 'x' has type 'int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
	logString = strings.Join(strings.Split(loggedLines[1], " ")[2:], " ")
	t.Log(logString)
	wantLog = "At line 5 identifier 'x' has type 'int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestFunctionCall_FunctionPanic(t *testing.T) {
	wantPanic := "The function used in the call expression 'a[0](42)' at line 8 must be an identifier or dot notation, is 'specparser.SquareBracket'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo(x int) int {
		return 42
	}
	func bar() {
		var a [1]func(int) int
		a[0] = foo
		//@ assert a[0](42) == 42 
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestFunctionCall_TypePanic(t *testing.T) {
	wantPanic := "Function call expression 'x(42)' at line 5 must be of type signature, has 'int'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	import "fmt"
	func bar() {
		x := 42	
		//@ assert x(42) == 42 
		fmt.Println(x)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestFunctionCall(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	//@ pure
	func foo(x int) int {
		return 42
	}
	func bar() {
		//@ assert foo(42) == foo(1337)
	}`
	ComputeRuntimeAssertionChecks(config, input)
	loggedLines := strings.Split(buf.String(), "\n")
	logString := strings.Join(strings.Split(loggedLines[0], " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 7 identifier 'foo' has type 'func(x int) int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
	logString = strings.Join(strings.Split(loggedLines[1], " ")[2:], " ")
	t.Log(logString)
	wantLog = "At line 7 identifier 'foo' has type 'func(x int) int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestQuantifierVariable_ExternalNameClash(t *testing.T) {
	wantPanic := "At line 4 identifier 'a' defined both in scope and quantifier."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int, a, b bool :: x in range a ==> x > 0 && (a || b)
		return a
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestUniversalQuantifierVariable_InternalNameClash(t *testing.T) {
	wantPanic := "Quantified variable 'x' from quantifier '(forall x int, x bool :: x in range a ==> ((x > 0) && x))' at line 4 must have unique name"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int, x bool :: x in range a ==> x > 0 && x
		return a
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestExistentialQuantifierVariable_InternalNameClash(t *testing.T) {
	wantPanic := "Quantified variable 'x' from quantifier '(exists x int, x bool :: x in range a && ((x > 0) && x))' at line 4 must have unique name"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int, x bool :: x in range a && x > 0 && x
		return a
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestQuantifierDomain_UndeclaredVariable(t *testing.T) {
	wantPanic := "Quantified variable 'y' used in domain 'y in range a' at line 4 is not declared"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int, b bool :: y in range a && x > 0 && b
		return a
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestQuantifierVariable_NotIdentifier(t *testing.T) {
	wantPanic := "Quantifier '(exists x [3]int, b bool :: y in range a && ((x > 0) && b))' at line 4 must have identifier as type of quantified variable 'x', has '[3]int'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x[3] int, b bool :: y in range a && x > 0 && b
		return a
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestAccess_DotNotation_Implicit(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	type s struct {
		val int
	}
	//@ requires acc(x.val)
	func foo(x *s) {
		x.val = 42
	}`
	ComputeRuntimeAssertionChecks(config, input)
	logString := strings.Join(strings.Split(buf.String(), " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 5 identifier 'x' has type '*cmd/gorac.s'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestAccess_DotNotation_Explicit(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	type s struct {
		val int
	}
	//@ requires acc((*x).val)
	func foo(x *s) {
		x.val = 42
	}`
	ComputeRuntimeAssertionChecks(config, input)
	logString := strings.Join(strings.Split(buf.String(), " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 5 identifier 'x' has type '*cmd/gorac.s'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestAccess_Pointer(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	//@ requires acc(x)
	func foo(x *int) int{
		return *x	
	}`
	ComputeRuntimeAssertionChecks(config, input)
	logString := strings.Join(strings.Split(buf.String(), " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 2 identifier 'x' has type '*int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestAccess_Slice(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	//@ requires acc(x)
	func foo(x []int) []int{
		return x	
	}`
	ComputeRuntimeAssertionChecks(config, input)
	logString := strings.Join(strings.Split(buf.String(), " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 2 identifier 'x' has type '[]int'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestAccess_Map(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	//@ requires acc(x)
	func foo(x map[int]bool) map[int]bool{
		return x	
	}`
	ComputeRuntimeAssertionChecks(config, input)
	logString := strings.Join(strings.Split(buf.String(), " ")[2:], " ")
	t.Log(logString)
	wantLog := "At line 2 identifier 'x' has type 'map[int]bool'."
	if clean(logString) != clean(wantLog) {
		t.Errorf("logger got:\n %v logger want:\n %s", logString, wantLog)
	}
}

func TestAccess_NonAccessible(t *testing.T) {
	wantPanic := "Access permission 'acc(x)' at line 2 must contain field access, pointer or reference, has 'specparser.Identifier'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	//@ requires acc(x)
	func foo(x int) int {
		return x	
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestAccess_NonAccessible_NoPtrStruct(t *testing.T) {
	wantPanic := "Access permission 'acc(x.val)' at line 5 must contain field access, pointer or reference, has 'specparser.DotNotation'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	type s struct {
		val int
	}
	//@ requires acc(x.val)
	func foo(x s) {
		x.val = 42
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestAccess_NonAccessible_DoubleImplicit(t *testing.T) {
	wantPanic := "Access permission 'acc(x.tStruct.val)' at line 8 must contain field access, pointer or reference, has 'specparser.DotNotation'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	type s struct {
		tStruct t // no pointer!
	}
	type t struct {
		val int
	}
	//@ requires acc(x.tStruct.val)
	func foo(x *s) {
		x.tStruct.val = 42
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestAccessPermission_ReferenceCompositeLiteral(t *testing.T) {
	wantPanic := "Reference used in access permission 'acc(&bar{})' at line 4 impure on composite literal."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	type bar struct {}
	func foo() {
		//@ assert acc(&bar{}) 
	}`
	ComputeRuntimeAssertionChecks(config, input)
}
