// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"regexp"
	"strings"
	"testing"
)

// Unit tests for oldexprconverter.go

func cleanOld(s string) string {
	oldRegex := regexp.MustCompile("OLD[0-9]*")
	s = oldRegex.ReplaceAllString(s, "")
	return strings.Join(strings.Fields(s), "")
}

func TestOldExpression_Postcondition(t *testing.T) {
	input := `package test
	//@ ensures old(x) == 42
	func foo(x int) int {
		x = 1337
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		var xOLD81 int
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 2, Specification 'ensures (old(x) == 42)': %v", err))
					}
				}()
				if !(xOLD81 == 42) {
					panic("Postcondition '(old(x) == 42)' violated.")
				}
			}()
		}()
		xOLD81 = x
		x = 1337
		return x
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_Multiple(t *testing.T) {
	input := `package test
	//@ ensures old(i) == 0 && old(a)[old(i)] == 42
	func foo(a [3]int, i int) int {
		a[0] = 1337
		i = 1
		return a[i]
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(a [3]int, i int) int {
		var iOLD47 int
		var aOLD87 [3]int
		var iOLD81 int
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 2, Specification 'ensures ((old(i) == 0) && (old(a)[old(i)] == 42))': %v", err))
					}
				}()
				if !(iOLD81 == 0 && aOLD87[iOLD47] == 42) {
					panic("Postcondition '((old(i) == 0) && (old(a)[old(i)] == 42))' violated.")
				}
			}()
		}()
		iOLD47 = i
		aOLD87 = a
		iOLD81 = i
		a[0] = 1337
		i = 1
		return a[i]
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_Precondition(t *testing.T) {
	wantPanic := "No old expressions allowed in precondition requires (old(x) == 42) at line 2."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	//@ requires old(x) == 42
	func foo(x int) int {
		x = 1337
		return x
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestOldExpression_Assert(t *testing.T) {
	input := `package test
	func foo(a [3]int, i int) int { //@ shared: i
		a[0] = 1337
		i = 1
		//@ assert old(i) == 0
		return a[i]
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(a [3]int, i int) int {
		var iOLD81 int
		iOLD81 = i
		a[0] = 1337
		i = 1
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 5, Specification 'assert (old(i) == 0)': %v", err))
				}
			}()
			if !(iOLD81 == 0) {
				panic("Assertion '(old(i) == 0)' violated.")
			}
		}()
		return a[i]
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_Invariant(t *testing.T) {
	input := `package test
	func foo(a [3]int, x int) int {
		x = 42 //@ shared: x
		//@ invariant a[i] == old(x)
		for i := 0; i < len(a); i++ {
			a[i] = 42
		}
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(a [3]int, x int) int {
		var xOLD81 int
		xOLD81 = x
		x = 42
		{
			i := 0
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant (a[i] == old(x))': %v", err))
					}
				}()
				if !(a[i] == xOLD81) {
					panic("Invariant '(a[i] == old(x))' violated before loop execution.")
				}
			}()
			for ; i < len(a); i++ {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 5, Specification 'invariant (a[i] == old(x))': %v", err))
						}
					}()
					if !(a[i] == xOLD81) {
						panic("Invariant '(a[i] == old(x))' violated during loop execution.")
					}
				}()
				a[i] = 42
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant (a[i] == old(x))': %v", err))
					}
				}()
				if !(a[i] == xOLD81) {
					panic("Invariant '(a[i] == old(x))' violated after loop execution.")
				}
			}()
		}
		return x
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_Mixed(t *testing.T) {
	input := `package test
	//@ ensures old(x) == 1337
	//@ shared: a, x
	func foo(a [3]int, x int) int {
		x = 42
		//@ invariant a[i] == old(x)
		for i := 0; i < len(a); i++ {
			a[i] = 42
		}
		//@ assert old(a) == [3]int{1337, 1337, 1337}
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(a [3]int, x int) int {
		var aOLD81 [3]int
		var xOLD47 int
		var xOLD87 int
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 2, Specification 'ensures (old(x) == 1337)': %v", err))
					}
				}()
				if !(xOLD87 == 1337) {
					panic("Postcondition '(old(x) == 1337)' violated.")
				}
			}()
		}()
		aOLD81 = a
		xOLD47 = x
		xOLD87 = x
		x = 42
		{
			i := 0
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 7, Specification 'invariant (a[i] == old(x))': %v", err))
					}
				}()
				if !(a[i] == xOLD47) {
					panic("Invariant '(a[i] == old(x))' violated before loop execution.")
				}
			}()
			for ; i < len(a); i++ {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 7, Specification 'invariant (a[i] == old(x))': %v", err))
						}
					}()
					if !(a[i] == xOLD47) {
						panic("Invariant '(a[i] == old(x))' violated during loop execution.")
					}
				}()
				a[i] = 42
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 7, Specification 'invariant (a[i] == old(x))': %v", err))
					}
				}()
				if !(a[i] == xOLD47) {
					panic("Invariant '(a[i] == old(x))' violated after loop execution.")
				}
			}()
		}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 10, Specification 'assert (old(a) == [3]int{1337, 1337, 1337})': %v", err))
				}
			}()
			if !(aOLD81 == [3]int{1337, 1337, 1337}) {
				panic("Assertion '(old(a) == [3]int{1337, 1337, 1337})' violated.")
			}
		}()
		return x
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_LabelPostconditions(t *testing.T) {
	input := `package test
	//@ ensures old(x) == 0
	//@ ensures old[L1](x) == 1
	//@ ensures old[L2](x) == 2
	func foo(x int) int {
		x = 1
		/*@ L1: @*/
		x = 2
		/*@ L2: @*/
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		var xL2OLD47 int
		var xL1OLD87 int
		var xOLD81 int
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 4, Specification 'ensures (old[L2](x) == 2)': %v", err))
					}
				}()
				if !(xL2OLD47 == 2) {
					panic("Postcondition '(old[L2](x) == 2)' violated.")
				}
			}()
		}()
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 3, Specification 'ensures (old[L1](x) == 1)': %v", err))
					}
				}()
				if !(xL1OLD87 == 1) {
					panic("Postcondition '(old[L1](x) == 1)' violated.")
				}
			}()
		}()
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 2, Specification 'ensures (old(x) == 0)': %v", err))
					}
				}()
				if !(xOLD81 == 0) {
					panic("Postcondition '(old(x) == 0)' violated.")
				}
			}()
		}()
		xOLD81 = x
		x = 1
		xL1OLD87 = x
		x = 2
		xL2OLD47 = x
		return x
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_LabelAssertions(t *testing.T) {
	input := `package test
	func foo(x int) int { //@ shared: x
		x = 1
		/*@ L1: @*/
		x = 2
		/*@ L2: @*/
		//@ assume old(x) == 0
		//@ assert old[L1](x) == 1
		//@ assume old[L2](x) == 2
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		var xL2OLD47 int
		var xL1OLD87 int
		var xOLD81 int
		xOLD81 = x
		x = 1
		xL1OLD87 = x
		x = 2
		xL2OLD47 = x
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'assume (old(x) == 0)': %v", err))
				}
			}()
			if !(xOLD81 == 0) {
				panic("Assumption '(old(x) == 0)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 8, Specification 'assert (old[L1](x) == 1)': %v", err))
				}
			}()
			if !(xL1OLD87 == 1) {
				panic("Assertion '(old[L1](x) == 1)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 9, Specification 'assume (old[L2](x) == 2)': %v", err))
				}
			}()
			if !(xL2OLD47 == 2) {
				panic("Assumption '(old[L2](x) == 2)' violated.")
			}
		}()
		return x
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_GoLabels(t *testing.T) {
	input := `package test
	func foo(x int) int {
		//@ shared: x
		x = 1
		L1: x = 2
		//@ assume old(x) == 0
		//@ assert old[L1](x) == 1
		if false {
			goto L1
		}
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		var xL1OLD87 int
		var xOLD81 int
		xOLD81 = x
		x = 1
		xL1OLD87 = x
		L1:
		x = 2
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 6, Specification 'assume (old(x) == 0)': %v", err))
				}
			}()
			if !(xOLD81 == 0) {
				panic("Assumption '(old(x) == 0)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'assert (old[L1](x) == 1)': %v", err))
				}
			}()
			if !(xL1OLD87 == 1) {
				panic("Assertion '(old[L1](x) == 1)' violated.")
			}
		}()
		if false {
			goto L1
		}
		return x
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_MixedLabels(t *testing.T) {
	input := `package test
	func foo(x int) int { //@ shared: x
		x = 1
		L1: x = 2
		/*@ L2: @*/
		//@ assume old(x) == 0
		//@ assert old[L1](x) == 1
		//@ assert old[L2](x) == 2
		if false {
			goto L1
		}
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		var xL2OLD47 int
		var xL1OLD87 int
		var xOLD81 int
		xOLD81 = x
		x = 1
		xL1OLD87 = x
		L1:
		x = 2
		xL2OLD47 = x
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 6, Specification 'assume (old(x) == 0)': %v", err))
				}
			}()
			if !(xOLD81 == 0) {
				panic("Assumption '(old(x) == 0)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'assert (old[L1](x) == 1)': %v", err))
				}
			}()
			if !(xL1OLD87 == 1) {
				panic("Assertion '(old[L1](x) == 1)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 8, Specification 'assert (old[L2](x) == 2)': %v", err))
				}
			}()
			if !(xL2OLD47 == 2) {
				panic("Assertion '(old[L2](x) == 2)' violated.")
			}
		}()
		if false {
			goto L1
		}
		return x
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_LabelUndeclaredVariable(t *testing.T) {
	wantPanic := "At line 3 identifier 'i' undefined or not in scope."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo(x []int) int { //@ shared: x
		//@ assert old(x[i]) == 42
		//@ shared: i
		i := 1
		return x[i]
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestOldExpression_OldStructDeclaration(t *testing.T) {
	input := `package test
	type s struct {
		val int
	}
	//@ ensures old(x) == s{42}
	func foo(x s) s {
		x.val = 1337
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type s struct {
		val int
	}
	func foo(x s) s {
		var xOLD81 s
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'ensures (old(x) == s{42})': %v", err))
					}
				}()
				if !(xOLD81 == s{42}) {
					panic("Postcondition '(old(x) == s{42})' violated.")
				}
			}()
		}()
		xOLD81 = x
		x.val = 1337
		return x
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_UndeclaredLabel(t *testing.T) {
	wantPanic := "Old expression old[L](x) from specification assert (old[L](x) == 1337) at line 4 refers to undeclared label L."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo(x int) int {
		x = 42
		//@ assert old[L](x) == 1337
		return x
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestOldExpression_LabelOrder(t *testing.T) {
	wantPanic := "Nested inner old expression old[L]((*x)) must be evaluated before outer old expression old((*old[L]((*x)))) at line 8."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	//@ requires **x == 1 && **y == 0
  	func test2(x, y **int) int {
       	*x  = *y
       	**y = 2
       	a, b := 42, 42
       	//@ L:
		//@ assert old(*old[L](*x)) == 0
		return a + b
  	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestOldExpression_Nested(t *testing.T) {
	input := `package test
	//@ ensures old(i) == 0 && old(a[old(i)]) == 42
	func foo(a [3]int, i int) int {
		a[0] = 1337
		i = 1
		return a[i]
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(a [3]int, i int) int {
		var iOLD87 int
		var aoldiOLD47 int
		var iOLD81 int
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 2, Specification 'ensures ((old(i) == 0) && (old(a[old(i)]) == 42))': %v", err))
					}
				}()
				if !(iOLD81 == 0 && aoldiOLD47 == 42) {
					panic("Postcondition '((old(i) == 0) && (old(a[old(i)]) == 42))' violated.")
				}
			}()
		}()
		iOLD87 = i
		aoldiOLD47 = a[iOLD87]
		iOLD81 = i
		a[0] = 1337
		i = 1
		return a[i]
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_BinaryNested(t *testing.T) {
	input := `package test
	//@ requires x == 41
	func foo(x int) int {
		y := 1 //@ shared: y
		//@ L:
		x = 1337 //@ shared: x
		//@ assert old[L](old(x) + y) == 42
		//@ assert old[L](old(x) - y) == 40
		return x + y
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		var xOLD47 int
		var oldxyLOLD59 int
		var xOLD81 int
		var oldxyLOLD87 int
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (x == 41)': %v", err))
				}
			}()
			if !(x == 41) {
				panic("Precondition '(x == 41)' violated.")
			}
		}()
		xOLD47 = x
		xOLD81 = x
		y := 1
		oldxyLOLD87 = xOLD81 + y
		oldxyLOLD59 = xOLD47 - y
		x = 1337
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'assert (old[L]((old(x) + y)) == 42)': %v", err))
				}
			}()
			if !(oldxyLOLD87 == 42) {
				panic("Assertion '(old[L]((old(x) + y)) == 42)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 8, Specification 'assert (old[L]((old(x) - y)) == 40)': %v", err))
				}
			}()
			if !(oldxyLOLD59 == 40) {
				panic("Assertion '(old[L]((old(x) - y)) == 40)' violated.")
			}
		}()
		return x + y
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_Array(t *testing.T) {
	input := `package test
	//@ requires a[0] == 42
	func array(a [3]int) {
		a[0] = 1337 //@ shared: a
		//@ assert old(a)[0] == 42
		//@ assert old(a[0]) == 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func array(a [3]int) {
		var aOLD87 int
		var aOLD81 [3]int
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (a[0] == 42)': %v", err))
				}
			}()
			if !(a[0] == 42) {
				panic("Precondition '(a[0] == 42)' violated.")
			}
		}()
		aOLD87 = a[0]
		aOLD81 = a
		a[0] = 1337
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 6, Specification 'assert (old(a[0]) == 42)': %v", err))
				}
			}()
			if !(aOLD87 == 42) {
				panic("Assertion '(old(a[0]) == 42)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 5, Specification 'assert (old(a)[0] == 42)': %v", err))
				}
			}()
			if !(aOLD81[0] == 42) {
				panic("Assertion '(old(a)[0] == 42)' violated.")
			}
		}()
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_Slice(t *testing.T) {
	input := `package test
	//@ requires s[0] == 42
	func slice(s []int) {
		s[0] = 1337 //@ shared: s
		//@ assert old(s)[0] == 1337
		//@ assert old(s[0]) == 42
	}
	`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func slice(s []int) {
		var sOLD87 int
		var sOLD81 []int
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (s[0] == 42)': %v", err))
				}
			}()
			if !(s[0] == 42) {
				panic("Precondition '(s[0] == 42)' violated.")
			}
		}()
		sOLD87 = s[0]
		sOLD81 = s
		s[0] = 1337
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 6, Specification 'assert (old(s[0]) == 42)': %v", err))
				}
			}()
			if !(sOLD87 == 42) {
				panic("Assertion '(old(s[0]) == 42)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 5, Specification 'assert (old(s)[0] == 1337)': %v", err))
				}
			}()
			if !(sOLD81[0] == 1337) {
				panic("Assertion '(old(s)[0] == 1337)' violated.")
			}
		}()
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestOldExpression_Pointer(t *testing.T) {
	input := `package test
	//@ requires p[0] == 42
	func pointer(p *[3]int) {
		p[0] = 1337 //@ shared: p
		//@ assert old(p)[0] == 1337
		//@ assert old(p[0]) == 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func pointer(p *[3]int) {
		var pOLD87 int
		var pOLD81 *[3]int
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (p[0] == 42)': %v", err))
				}
			}()
			if !(p[0] == 42) {
				panic("Precondition '(p[0] == 42)' violated.")
			}
		}()
		pOLD87 = p[0]
		pOLD81 = p
		p[0] = 1337
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 6, Specification 'assert (old(p[0]) == 42)': %v", err))
				}
			}()
			if !(pOLD87 == 42) {
				panic("Assertion '(old(p[0]) == 42)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 5, Specification 'assert (old(p)[0] == 1337)': %v", err))
				}
			}()
			if !(pOLD81[0] == 1337) {
				panic("Assertion '(old(p)[0] == 1337)' violated.")
			}
		}()
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestShared_DeclaredNonAddressable(t *testing.T) {
	wantPanic := "Shared variable annotation 'shared: x' at line 3 refers to variable 'x' that has already been declared exclusive."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo(x int) { 
		//@ exclusive: x shared: x
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestShared_UndeclaredVariable(t *testing.T) {
	wantPanic := "Shared variable annotation 'shared: x' at line 3 refers to variable 'x' that is undeclared or out of scope."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo() { 
		//@ shared: x
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestExclusive_DeclaredAddressable(t *testing.T) {
	wantPanic := "Exclusive variable annotation 'exclusive: x' at line 3 refers to variable 'x' that has already been declared shared."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo(x int) { 
		//@ shared: x exclusive: x
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestExclusive_UndeclaredVariable(t *testing.T) {
	wantPanic := "Exclusive variable annotation 'exclusive: x' at line 3 refers to variable 'x' that is undeclared or out of scope."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo() { 
		//@ exclusive: x
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestOldExpression_LabelDeclaredTwice(t *testing.T) {
	wantPanic := "Label L defined twice at line 4 and line 2"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	func foo() {
		//@ L:
		//@ L:
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestExclusive_Assertion(t *testing.T) {
	wantPanic := "At line 5 in old expression 'old(p[0])' the exclusive variable 'p' is not allowed. " +
		"Exclusive variables are supported in postconditions only. Declare 'p' as shared or remove from old expression.\n"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	//@ requires p[0] == 42
	func pointer(p *[3]int) {
		p[0] = 1337 //@ exclusive: p
		//@ assert old(p[0]) == 42
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestDefaultExclusive_Assertion(t *testing.T) {
	wantPanic := "At line 5 in old expression 'old(p[0])' the variable 'p' is considered by default as exclusive. " +
		"However, exclusive variables are supported in postconditions only. Declare 'p' as shared or remove from old expression."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	//@ requires p[0] == 42
	func pointer(p *[3]int) {
		p[0] = 1337 
		//@ assert old(p[0]) == 42 
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestExclusive_Postcondition(t *testing.T) {
	input := `package test
	//@ requires p[0] == 42
	//@ ensures old(p[0]) == 42 
	func pointer(p *[3]int) { //@ exclusive: p
		p[0] = 1337 
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func pointer(p *[3]int) {
		var pOLD87 int
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 3, Specification 'ensures (old(p[0]) == 42)': %v", err))
					}
				}()
				if !(pOLD87 == 42) {
					panic("Postcondition '(old(p[0]) == 42)' violated.")
				}
			}()
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (p[0] == 42)': %v", err))
				}
			}()
			if !(p[0] == 42) {
				panic("Precondition '(p[0] == 42)' violated.")
			}
		}()
		pOLD87 = p[0]
		p[0] = 1337
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestDefaultExclusive_Postcondition(t *testing.T) {
	input := `package test
	//@ requires p[0] == 42
	//@ ensures old(p[0]) == 42 
	func pointer(p *[3]int) {
		p[0] = 1337 
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func pointer(p *[3]int) {
		var pOLD87 int
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 3, Specification 'ensures (old(p[0]) == 42)': %v", err))
					}
				}()
				if !(pOLD87 == 42) {
					panic("Postcondition '(old(p[0]) == 42)' violated.")
				}
			}()
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (p[0] == 42)': %v", err))
				}
			}()
			if !(p[0] == 42) {
				panic("Precondition '(p[0] == 42)' violated.")
			}
		}()
		pOLD87 = p[0]
		p[0] = 1337
	}`
	if cleanOld(got) != cleanOld(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}
