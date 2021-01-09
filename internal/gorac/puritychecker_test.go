// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"testing"
)

// Unit tests for puritychecker.go

func TestPurityBinaryExpr(t *testing.T) {
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			t.Errorf("got panic:\n %v want no panic", gotPanic.(string))
		}
	}()
	input := `package test
	//@ pure 
	func foo() bool { 
		return true || false 
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPurityUnaryExpr(t *testing.T) {
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			t.Errorf("got panic:\n %v want no panic", gotPanic.(string))
		}
	}()
	input := `package test
	//@ pure 
	func foo() bool { 
		return !true
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPurityCall(t *testing.T) {
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			t.Errorf("got panic:\n %v want no panic", gotPanic.(string))
		}
	}()
	input := `package test
	//@ pure 
	func foo() int { 
		return bar(1, 2, 3) 
	}
	//@ pure 
	func bar(x, y, z int) int { 
		return x + y + z
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPurityDotNotation(t *testing.T) {
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			t.Errorf("got panic:\n %v want no panic", gotPanic.(string))
		}
	}()
	input := `package test
	type s struct {
		val int
	}
	//@ pure
	func foo() int { 
		return s{42}.val
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPurityCompositeLiterals(t *testing.T) {
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			t.Errorf("got panic:\n %v want no panic", gotPanic.(string))
		}
	}()
	input := `package test
	type s struct {
		val int
	}
	//@ pure
	func foo() s { 
		return s{42}
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestMisplacedPurity(t *testing.T) {
	wantPanic := "Purity annotation at line 4 needs to be associated to a function."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	import "fmt"
	func foo() {
		//@ pure
		fmt.Println("hello world!")
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestMultipleReturnValues(t *testing.T) {
	wantPanic := "At line 2, pure function 'foo' should have exactly one return parameter, found 2"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	//@ pure
	func foo() (int, int) {
		return 42, 1337
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestMultipleStatementsInBody(t *testing.T) {
	wantPanic := "At line 2, the pure function 'foo' is not pure: the body should consist of a single return statement"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	//@ pure
	func foo() int {
		x := 42
		return x
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestImpureExpression(t *testing.T) {
	wantPanic := "At line 3, the pure function 'foo' is not pure: the expression that is returned must be pure"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	var x = [3]int{1,2,3}
	//@ pure
	func foo() int {
		return x[1]
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestImpureParameter(t *testing.T) {
	wantPanic := "At line 3, the pure function 'foo' is not pure: the expression that is returned must be pure"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	var x = [3]int{1,2,3}
	//@ pure 
	func foo() int { 
		return bar(1, 2, x[2]) 
	}
	//@ pure 
	func bar(x, y, z int) int { 
		return x + y + z
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestFunctionCallExpression(t *testing.T) {
	input := `package test
	//@ pure
	func foo(x int) int {
		return 42
	}
	func bar() {
		//@ assert foo(42) == foo(1337)
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		return 42
	}
	func bar() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'assert (foo(42) == foo(1337))': %v", err))
				}
			}()
			if !(foo(42) == foo(1337)) {
				panic("Assertion '(foo(42) == foo(1337))' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestMethodCallExpression(t *testing.T) {
	input := `package test
	type s struct {
		val int
	}
	//@ pure
	func (x s) Val() int {
		return x.val
	}
	func foo() s {
		x := s{42}
		//@ assert x.Val() == 42
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type s struct {
		val int
	}
	func (x s) Val() int {
		return x.val
	}
	func foo() s {
		x := s{42}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 11, Specification 'assert (x.Val() == 42)': %v", err))
				}
			}()
			if !(x.Val() == 42) {
				panic("Assertion '(x.Val() == 42)' violated.")
			}
		}()
		return x
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestNonPureFunctionCall(t *testing.T) {
	wantPanic := "At line 4 in specification 'assert (foo(1, 1, 1) == 3)' the called function 'foo' is not pure."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo(x, y, z int) int {
		res := x + y + z
		//@ assert foo(1, 1, 1) == 3
		return res
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPurityBuildin(t *testing.T) {
	input := `package test
	func foo() int {
		a := [1337]int{1, 3, 3, 7}	
		//@ assert len(a) == 1337 
		return a[42]
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() int {
		a := [1337]int{1, 3, 3, 7}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (len(a) == 1337)': %v", err))
				}
			}()
			if !(len(a) == 1337) {
				panic("Assertion '(len(a) == 1337)' violated.")
			}
		}()
		return a[42]
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestNonPurePostcondition(t *testing.T) {
	wantPanic := "At line 2 in specification 'ensures (foo(1, 1, 1) == 3)' the called function 'foo' is not pure."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	//@ ensures foo(1, 1, 1) == 3
	func foo(x, y, z int) int {
		res := x + y + z
		return res
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPurePostcondition(t *testing.T) {
	wantPanic := "At line 2 in specification 'ensures (foo(1, 1, 1) == 3)' the called function 'foo' is not pure."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	//@ pure
	func bar() int {
		return 42
	}
	//@ requires x > y && y > z
	//@ ensures bar() == 42 
	func foo(x, y, z int) int {
		res := x + y + z
		return res
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func bar() int {
		return 42
	}
	func foo(x, y, z int) int {
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 7, Specification 'ensures (bar() == 42)': %v", err))
					}
				}()
				if !(bar() == 42) {
					panic("Postcondition '(bar() == 42)' violated.")
				}
			}()
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 6, Specification 'requires ((x > y) && (y > z))': %v", err))
				}
			}()
			if !(x > y && y > z) {
				panic("Precondition '((x > y) && (y > z))' violated.")
			}
		}()
		res := x + y + z
		return res
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestParenthesis(t *testing.T) {
	input := `package test
	//@ pure
	func isOutlier(i int) bool {
		return !(0 <= i && i <= 10000000000)
	}
	
	//@ requires len(values) < 100
	//@ requires forall i int :: _, i in range values && 0 <= i <= 10000000000 ==> !isOutlier(i)
	func processValues(values []int) {
		// ...
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func isOutlier(i int) bool {
		return !(0 <= i && i <= 10000000000)
	}
	func processValues(values []int) {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 8, Specification 'requires (forall i int :: ((_, i) in range values && 0 <= i <= 10000000000) ==> !isOutlier(i))': %v", err))
				}
			}()
			if !func() bool {
				for _, i := range values {
					if 0 <= i && i <= 10000000000 {
						if !!isOutlier(i) {
							return false
						}
					}
				}
				return true
			}() {
				panic("Precondition '(forall i int :: ((_, i) in range values && 0 <= i <= 10000000000) ==> !isOutlier(i))' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'requires (len(values) < 100)': %v", err))
				}
			}()
			if !(len(values) < 100) {
				panic("Precondition '(len(values) < 100)' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}
