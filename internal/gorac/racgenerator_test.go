// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/format"
	"go/token"
	"log"
	"os"
	"regexp"
	"strings"
	"testing"
)

// Unit tests for the GoRAC framework.
// Please see go-runtime-checking/specparser/parser_test.go for unit tests concerning different parsing input.

var config = &Config{
	inputFile:                "",
	outputFile:               "",
	printInputFile:           false,
	printInputAST:            false,
	printOutputFile:          false,
	printOutputAST:           false,
	writeOutputFile:          false,
	generateAssertionChecks:  true,
	generatePrePostChecks:    true,
	generateInvariantsChecks: true,
}

func getTestOutput(fset *token.FileSet, n ast.Node) string {
	var buf2 bytes.Buffer
	if err := format.Node(&buf2, fset, n); err != nil {
		panic(err)
	}
	return fmt.Sprintf("%s", buf2.Bytes())
}

func clean(s string) string {
	generatedVars := regexp.MustCompile("[A-Za-z_@][A-Za-z_]*[0-9][0-9]*")
	s = generatedVars.ReplaceAllString(s, "")
	return strings.Join(strings.Fields(s), "")
}

func checkLog(buf bytes.Buffer, wantLog string, t *testing.T) {
	loggedLines := strings.Split(buf.String(), "\n")
	ignoredCheckLogged := false
	var logString string
	for _, line := range loggedLines {
		logString = strings.Join(strings.Split(line, " ")[2:], " ")
		if clean(logString) == clean(wantLog) {
			ignoredCheckLogged = true
			break
		}
	}
	t.Log(logString)
	if !ignoredCheckLogged {
		t.Errorf("logger got:\n %v logger want:\n %s", buf.String(), wantLog)
	}
}

func TestAssertion(t *testing.T) {
	input := `package test
	import (
		"math/rand"
	)
	func main() {
		rand.Int()
		//@ assert true
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import (
		"fmt"
		"math/rand"
	)
	func main() {
		rand.Int()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'assert true': %v", err))
				}
			}()
			if !true {
				panic("Assertion 'true' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestAssumption(t *testing.T) {
	input := `package test
	func main() {
		//@ assume true
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func main() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assume true': %v", err))
				}
			}()
			if !true {
				panic("Assumption 'true' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestPrecondition(t *testing.T) {
	input := `package test
	//@ requires true
	func foo() int {
		return 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires true': %v", err))
				}
			}()
			if !true {
				panic("Precondition 'true' violated.")
			}
		}()
		return 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestPostcondition(t *testing.T) {
	input := `package test
	//@ ensures true
	func foo() int {
		return 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() int {
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 2, Specification 'ensures true': %v", err))
					}
				}()
				if !true {
					panic("Postcondition 'true' violated.")
				}
			}()
		}()
		return 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestContracts(t *testing.T) {
	input := `package test
	//@ requires n > 0
	//@ ensures x == n + 1 
	func foo(n int) (x int) {
		return n + 1
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(n int) (x int) {
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 3, Specification 'ensures (x == (n + 1))': %v", err))
					}
				}()
				if !(x == n+1) {
					panic("Postcondition '(x == (n + 1))' violated.")
				}
			}()
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (n > 0)': %v", err))
				}
			}()
			if !(n > 0) {
				panic("Precondition '(n > 0)' violated.")
			}
		}()
		{
			x = n + 1
		}
		return x 
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestInvariant_Condition(t *testing.T) {
	input := `package test
	func foo() {
		i := 0
		//@ invariant true
		for i < 42 {
			i++
		}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		i := 0
		{
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			for i < 42 {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
						}
					}()
					if !true {
						panic("Invariant 'true' violated during loop execution.")
					}
				}()
				i++
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestInvariant_ForClause(t *testing.T) {
	input := `package test
	func foo() {
		//@ invariant true
		for i := 0; i < 42; i++ {}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		{
			i := 0
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 4, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			for ; i < 42; i++ {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 4, Specification 'invariant true': %v", err))
						}
					}()
					if !true {
						panic("Invariant 'true' violated during loop execution.")
					}
				}()
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 4, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestInvariant_ForClauseEmptyInit(t *testing.T) {
	input := `package test
	func foo() {
		i := 0
		//@ invariant true
		for ; i < 42; i++ {}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		i := 0
		{
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			for ; i < 42; i++ {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
						}
					}()
					if !true {
						panic("Invariant 'true' violated during loop execution.")
					}
				}()
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestInvariant_RangeClauseNoDeclaration(t *testing.T) {
	input := `package test
	func foo() {
		arr := []int{1, 2, 3}
		var i int
		//@ invariant true
		for i = range arr {
			i++
		}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		arr := []int{1, 2, 3}
		var i int
		{
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 6, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			for i = range arr {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 6, Specification 'invariant true': %v", err))
						}
					}()
					if !true {
						panic("Invariant 'true' violated during loop execution.")
					}
				}()
				i++
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 6, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestInvariant_RangeClauseSingleDeclaration(t *testing.T) {
	input := `package test
	func foo() {
		arr := []int{1, 2, 3}
		//@ invariant true
		for i := range arr {
			i++
		}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		arr := []int{1, 2, 3}
		{
			var i int
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			for i = range arr {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
						}
					}()
					if !true {
						panic("Invariant 'true' violated during loop execution.")
					}
				}()
				i++
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestInvariant_RangeClauseDoubleDeclaration(t *testing.T) {
	input := `package test
	func foo() {
		arr := []int{1, 2, 3}
		//@ invariant true
		for i, j := range arr {
			i++
			j++
		}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		arr := []int{1, 2, 3}
		{
			var i int
			var j int
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			for i, j = range arr {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
						}
					}()
					if !true {
						panic("Invariant 'true' violated during loop execution.")
					}
				}()
				i++
				j++
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestInvariant_RangeClauseEmptyDeclaration(t *testing.T) {
	input := `package test
	func foo() {
		arr := []int{1, 2, 3}
		//@ invariant true
		for i, _ := range arr {
			i++
		}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		arr := []int{1, 2, 3}
		{
			var i int
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			for i, _ = range arr {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
						}
					}()
					if !true {
						panic("Invariant 'true' violated during loop execution.")
					}
				}()
				i++
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestInvariant_RangeClauseMap(t *testing.T) {
	input := `package test
	func foo() {
		m := map[int]bool{
			1: true,
			2: false,
		}
		//@ invariant true
		for i, j := range m {
			i++
			j = !j
		}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		m := map[int]bool{
			1: true,
			2: false,
		}
		{
			var i int
			var j bool
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 8, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			for i, j = range m {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 8, Specification 'invariant true': %v", err))
						}
					}()
					if !true {
						panic("Invariant 'true' violated during loop execution.")
					}
				}()
				i++
				j = !j
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 8, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestMultiline(t *testing.T) {
	input := `package test
	//@ requires true
	//@ requires false ||
	//@         false
	//@ ensures 42
	//@ < 1337
	func main() {
		/*@
		assert 42 == 42
		assume false && true
			     || false

		assert 
		true
		@*/
		j := 0
		//@ invariant true
		/*@ invariant j 
                      != 
                      1337 @*/
		for i := j; i < 42; i++ {}	
		return
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func main() {
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 5, Specification 'ensures (42 < 1337)': %v", err))
					}
				}()
				if !(42 < 1337) {
					panic("Postcondition '(42 < 1337)' violated.")
				}
			}()
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'requires (false || false)': %v", err))
				}
			}()
			if !(false || false) {
				panic("Precondition '(false || false)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires true': %v", err))
				}
			}()
			if !true {
				panic("Precondition 'true' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 9, Specification 'assert (42 == 42)': %v", err))
				}
			}()
			if !(42 == 42) {
				panic("Assertion '(42 == 42)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 10, Specification 'assume ((false && true) || false)': %v", err))
				}
			}()
			if !(false && true || false) {
				panic("Assumption '((false && true) || false)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 13, Specification 'assert true': %v", err))
				}
			}()
			if !true {
				panic("Assertion 'true' violated.")
			}
		}()
		j := 0
		{
			i := j
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 21, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated before loop execution.")
				}
			}()
			{
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 21, Specification 'invariant (j != 1337)': %v", err))
						}
					}()
					if !(j != 1337) {
						panic("Invariant '(j != 1337)' violated before loop execution.")
					}
				}()
				for ; i < 42; i++ {
					func() {
						defer func() {
							if err := recover(); err != nil {
								panic(fmt.Sprintf("Line 21, Specification 'invariant (j != 1337)': %v", err))
							}
						}()
						if !(j != 1337) {
							panic("Invariant '(j != 1337)' violated during loop execution.")
						}
					}()
					func() {
						defer func() {
							if err := recover(); err != nil {
								panic(fmt.Sprintf("Line 21, Specification 'invariant true': %v", err))
							}
						}()
						if !true {
							panic("Invariant 'true' violated during loop execution.")
						}
					}()
				}
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 21, Specification 'invariant (j != 1337)': %v", err))
						}
					}()
					if !(j != 1337) {
						panic("Invariant '(j != 1337)' violated after loop execution.")
					}
				}()
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 21, Specification 'invariant true': %v", err))
					}
				}()
				if !true {
					panic("Invariant 'true' violated after loop execution.")
				}
			}()
		}
		return
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestLastStatementOfVoid(t *testing.T) {
	input := `package test
	import "fmt"
	func foo() {
		bar := 1
		fmt.Println(bar)
		//@ assert bar == 1
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		bar := 1
		fmt.Println(bar)
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 6, Specification 'assert (bar == 1)': %v", err))
				}
			}()
			if !(bar == 1) {
				panic("Assertion '(bar == 1)' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestLastStatementOfNonVoid_ReturnBlock(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	func foo() int {
		bar := 1
		{
			return bar
		}
		//@ assert bar == 1
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	func foo() int {
		bar := 1
		{
			return bar
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
	wantLog := "No check added for assertion 'assert (bar == 1)' at line 7 that is last statement in non-void function."
	checkLog(buf, wantLog, t)
}

func TestLastStatementOfNonVoid_Switch(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	func foo() int {
		switch true {
		case true:
			return 42
		case false:
			return 1337
		default:
			return 42 + 1337
		}
		//@ assert true || false
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	func foo() int {
		switch true {
		case true:
			return 42
		case false:
			return 1337
		default:
			return 42 + 1337
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
	wantLog := "No check added for assertion 'assert (true || false)' at line 11 that is last statement in non-void function."
	checkLog(buf, wantLog, t)
}

func TestLastStatementOfNonVoid_TypeSwitch(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	func foo() int {
		var bar interface{}
		switch bar.(type) {
		case int:
			return 42
		case bool:
			return 1337
		default:
			return 42 + 1337
		}
		//@ assert true || false
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	func foo() int {
		var bar interface{}
		switch bar.(type) {
		case int:
			return 42
		case bool:
			return 1337
		default:
			return 42 + 1337
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
	wantLog := "No check added for assertion 'assert (true || false)' at line 12 that is last statement in non-void function."
	checkLog(buf, wantLog, t)
}

func TestLastStatementOfNonVoid_IfStmt(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	func foo() int {
		if true {
			if false {
			} else {
				return 42
			}
			return 42 + 1337
		} else {
			return 1337
		}
		//@ assert true || false
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	func foo() int {
		if true {
			if false {
			} else {
				return 42
			}
			return 42 + 1337
		} else {
			return 1337
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
	wantLog := "No check added for assertion 'assert (true || false)' at line 12 that is last statement in non-void function."
	checkLog(buf, wantLog, t)
}

func TestLastStatementOfNonVoid_RangeStmt(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	func foo() int {
		for i := range [3]int{1, 2, 3} {
			return i
		}
		return 42
		//@ assert true || false
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	func foo() int {
		for i := range [3]int{1, 2, 3} {
			return i
		}
		return 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
	wantLog := "No check added for assertion 'assert (true || false)' at line 7 that is last statement in non-void function."
	checkLog(buf, wantLog, t)
}

func TestLastStatementOfNonVoid_ForSelectStmt(t *testing.T) {
	var buf bytes.Buffer
	log.SetOutput(&buf)
	defer func() {
		log.SetOutput(os.Stderr)
	}()
	input := `package test
	func foo(c1, c2 chan int) int {
		for {
			select {
			case c1 <- 0:
				return 42	
			case <-c2:
				return 1337
			default:
				return 42 + 1337	
			}
		}
		//@ assert true || false
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	func foo(c1, c2 chan int) int {
		for {
			select {
			case c1 <- 0:
				return 42	
			case <-c2:
				return 1337
			default:
				return 42 + 1337	
			}
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
	wantLog := "No check added for assertion 'assert (true || false)' at line 13 that is last statement in non-void function."
	checkLog(buf, wantLog, t)
}

func TestLastStatement_EmptyLine(t *testing.T) {
	input := `package test
	func foo() {
		_ = 42
	
		//@ assert false
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		_ = 42
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 5, Specification 'assert false': %v", err))
				}
			}()
			if !false {
				panic("Assertion 'false' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestAllSpecificationConstructs(t *testing.T) {
	input := `package test
	//@ requires n >= 0
	//@ ensures res == n * (n + 1) / 2
	func sum(n int) (res int) {
		res = 0 // not a specification comment
		i := 0
	
		/*@
		invariant i <= n + 1
		invariant res == i * (i - 1) / 2
		@*/
		for i <= n {
			res += i
			i++
		}
	
		//@ assert i == n
		//@ assume i >= 0
	
		return
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func sum(n int) (res int) {
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 3, Specification 'ensures (res == ((n * (n + 1)) / 2))': %v", err))
					}
				}()
				if !(res == n*(n+1)/2) {
					panic("Postcondition '(res == ((n * (n + 1)) / 2))' violated.")
				}
			}()
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (n >= 0)': %v", err))
				}
			}()
			if !(n >= 0) {
				panic("Precondition '(n >= 0)' violated.")
			}
		}()
		res = 0
		i := 0
		{
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 12, Specification 'invariant (i <= (n + 1))': %v", err))
					}
				}()
				if !(i <= n+1) {
					panic("Invariant '(i <= (n + 1))' violated before loop execution.")
				}
			}()
			{
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 12, Specification 'invariant (res == ((i * (i - 1)) / 2))': %v", err))
						}
					}()
					if !(res == i*(i-1)/2) {
						panic("Invariant '(res == ((i * (i - 1)) / 2))' violated before loop execution.")
					}
				}()
				for i <= n {
					func() {
						defer func() {
							if err := recover(); err != nil {
								panic(fmt.Sprintf("Line 12, Specification 'invariant (res == ((i * (i - 1)) / 2))': %v", err))
							}
						}()
						if !(res == i*(i-1)/2) {
							panic("Invariant '(res == ((i * (i - 1)) / 2))' violated during loop execution.")
						}
					}()
					func() {
						defer func() {
							if err := recover(); err != nil {
								panic(fmt.Sprintf("Line 12, Specification 'invariant (i <= (n + 1))': %v", err))
							}
						}()
						if !(i <= n+1) {
							panic("Invariant '(i <= (n + 1))' violated during loop execution.")
						}
					}()
					res += i
					i++
				}
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 12, Specification 'invariant (res == ((i * (i - 1)) / 2))': %v", err))
						}
					}()
					if !(res == i*(i-1)/2) {
						panic("Invariant '(res == ((i * (i - 1)) / 2))' violated after loop execution.")
					}
				}()
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 12, Specification 'invariant (i <= (n + 1))': %v", err))
					}
				}()
				if !(i <= n+1) {
					panic("Invariant '(i <= (n + 1))' violated after loop execution.")
				}
			}()
		}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 17, Specification 'assert (i == n)': %v", err))
				}
			}()
			if !(i == n) {
				panic("Assertion '(i == n)' violated.")
			}
		}()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 18, Specification 'assume (i >= 0)': %v", err))
				}
			}()
			if !(i >= 0) {
				panic("Assumption '(i >= 0)' violated.")
			}
		}()
		return
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestTypeChecking_NonBooleCondition(t *testing.T) {
	wantPanic := "Specification condition 'assert bar' at line 5 is not boolean."
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
		bar := 42
		//@ assert bar
		fmt.Println(bar)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestTypeChecking_WrongOperandType(t *testing.T) {
	wantPanic := "Specification 'assert (b2 || (i1 == b1))' at line 7 throws typing error: -: cannot compare i1 == b1 (mismatched types int and bool)"
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
		b1 := true
		b2 := false
		i1 := 42
		//@ assert b2 || i1 == b1
		fmt.Println(b1, b2, i1)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestTypeChecking_UndefinedVariable(t *testing.T) {
	wantPanic := "At line 5 identifier 'x' undefined or not in scope."
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
		bar := 42
		//@ assert x == 1337 
		fmt.Println(bar)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestTypeChecking_DereferencingNonPointer(t *testing.T) {
	wantPanic := "Dereferenced expression 'c' at line 7 must have a pointer type, has type 'int'"
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
		a := 42
		b := &a
		c := 1337
		//@ assert *b < *c
		fmt.Println(a, b, c)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestTypeChecking_InvalidPointerComparison(t *testing.T) {
	wantPanic := "Specification 'assert ((*b) != (*d))' at line 8 throws typing error: -: cannot compare *b != *d (mismatched types int and bool)"
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
		a := 42
		b := &a
		c := true
		d := &c
		//@ assert *b != *d
		fmt.Println(a, b, c, d)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestTypeChecking_NonExistingStructField(t *testing.T) {
	wantPanic := "At line 8 field access 'a.x' has no field or method with name 'x'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	import "fmt"
	type bar struct {
		val int
	}
	func foo() {
		a := bar{42} 
		//@ assert a.val == 42 && a.x != 42
		fmt.Println(a)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestTypeChecking_ArrayOutOfBounds(t *testing.T) {
	wantPanic := "Specification 'assert (a[3] == 4)' at line 5 throws typing error: -: index 3 (constant of type int) is out of bounds"
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
		a := [3]int{1,2,3}
		//@ assert a[3] == 4 
		fmt.Println(a)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestNodeAssociation_Precondition(t *testing.T) {
	wantPanic := "Precondition 'requires true' at line 4 needs to be associated to a function."
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
		//@ requires true 
		fmt.Println(42)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestNodeAssociation_Postcondition(t *testing.T) {
	wantPanic := "Postcondition 'ensures true' at line 4 needs to be associated to a function."
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
		//@ ensures true 
		fmt.Println(42)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestNodeAssociation_Invariant(t *testing.T) {
	wantPanic := "Invariant 'invariant true' at line 4 needs to be associated to a loop."
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
		//@ invariant true 
		fmt.Println(42)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestNodeAssociation_Assertion(t *testing.T) {
	wantPanic := "Assertion 'assert true' at line 3 cannot be outside of a function scope."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	import "fmt"
	//@ assert true 
	func foo() {
		fmt.Println(42)
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

// If this test fails, check whether you are running performance with the correct Go version.
// Please see the README.md for further information.
func TestEmptyBody_Function(t *testing.T) {
	input := `package test
	func foo() {
		//@ assert true
	}

	// spec from inside empty function foo should not associate to function bar
	func bar() int {
		return 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert true': %v", err))
				}
			}()
			if !true {
				panic("Assertion 'true' violated.")
			}
		}()
	}
	func bar() int {
		return 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

// If this test fails, check whether you are running performance with the correct Go version.
// Please see the README.md for further information.
func TestEmptyBody_Loop(t *testing.T) {
	input := `package test
	func foo() int {
		i := 0

		for i < 10 {
			//@ assert true
		}

		// spec from inside empty loop should not associate to return statement
		return i
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() int {
		i := 0
	
		for i < 10 {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 6, Specification 'assert true': %v", err))
					}
				}()
				if !true {
					panic("Assertion 'true' violated.")
				}
			}()
	
		}
	
		return i
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

// If this test fails, check whether you are running performance with the correct Go version.
// Please see the README.md for further information.
func TestEmptyBody_If(t *testing.T) {
	input := `package test
	func foo() int {
		i := 0

		if i < 10 {
			//@ assert true
		}

		// spec from inside empty loop should not associate to return statement
		return i
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() int {
		i := 0
	
		if i < 10 {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 6, Specification 'assert true': %v", err))
					}
				}()
				if !true {
					panic("Assertion 'true' violated.")
				}
			}()
	
		}
	
		return i
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestSpecVariablesScope_Invariant(t *testing.T) {
	wantPanic := "Specification 'invariant ((i > 0) && (j == 42))' at line 4 throws typing error: -: undeclared name: j"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	import "fmt"
	func main() {
		//@ invariant i > 0 && j == 42
		for i := 1; i < 2; i++ {
			j := 42
			fmt.Println(j)
		}
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestSpecVariablesScope_Contracts(t *testing.T) {
	wantPanic := "At line 2 identifier 'z' undefined or not in scope."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	//@ ensures y == x + 2 && z == x + 1
	func foo(x int) (y int) {
		z := x + 1
		y = z + 1
		return y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestAssertionOutsideFunction(t *testing.T) {
	wantPanic := "Assertion 'assert (x == 42)' at line 3 cannot be outside of a function scope."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", clean(gotPanic.(string)), clean(wantPanic))
			}
		}
	}()
	input := `package test
	var x = 42
	//@ assert x == 42`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestFmtImport_None(t *testing.T) {
	input := `package test
	func main() {
		//@ assert true
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func main() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert true': %v", err))
				}
			}()
			if !true {
				panic("Assertion 'true' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestFmtImport_Existent(t *testing.T) {
	input := `package test
	import (
		"fmt"
	)
	func main() {
		fmt.Println("foo")
		//@ assert true
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import (
		"fmt"
	)
	func main() {
		fmt.Println("foo")
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'assert true': %v", err))
				}
			}()
			if !true {
				panic("Assertion 'true' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestFmtImport_ExistentOther(t *testing.T) {
	input := `package test
	import (
		"fmt"
		"math/rand"
	)
	func main() {
		fmt.Println(rand.Int())
		//@ assert true
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import (
		"fmt"
		"math/rand"
	)
	func main() {
		fmt.Println(rand.Int())
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 8, Specification 'assert true': %v", err))
				}
			}()
			if !true {
				panic("Assertion 'true' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestFmtImport_Other(t *testing.T) {
	input := `package test
	import "math/rand"
	func main() {
		rand.Int()	
		//@ assert true
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import (
		"math/rand"
		"fmt"
	)
	func main() {
		rand.Int()
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 5, Specification 'assert true': %v", err))
				}
			}()
			if !true {
				panic("Assertion 'true' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Assertion_Numeric_LessLess(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: 42 < x < 1337 ==> x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: 42 < x < 1337 ==> (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 42 + 1; x < 1337; x++ {
					if !(x > 0) {
						return false
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: 42 < x < 1337 ==> (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Assertion_Numeric_LessLessEqual(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: 42 < x <= 1337 ==> x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: 42 < x <= 1337 ==> (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 42 + 1; x <= 1337; x++ {
					if !(x > 0) {
						return false
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: 42 < x <= 1337 ==> (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Assertion_Numeric_LessEqualLess(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: 42 <= x < 1337 ==> x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: 42 <= x < 1337 ==> (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 42; x < 1337; x++ {
					if !(x > 0) {
						return false
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: 42 <= x < 1337 ==> (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Assertion_Numeric_LessEqualLessEqual(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: 42 <= x <= 1337 ==> x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: 42 <= x <= 1337 ==> (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 42; x <= 1337; x++ {
					if !(x > 0) {
						return false
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: 42 <= x <= 1337 ==> (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Assertion_DataStructure_Key(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: x in range a ==> x >= 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: x in range a ==> (x >= 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := range a {
					if !(x >= 0) {
						return false
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: x in range a ==> (x >= 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Assertion_DataStructure_Value(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: (_, x) in range a ==> x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: (_, x) in range a ==> (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for _, x := range a {
					if !(x > 0) {
						return false
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: (_, x) in range a ==> (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Assertion_DataStructure_KeyAndValue(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x, y int :: (x, y) in range a ==> x + y > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int, y int :: (x, y) in range a ==> ((x + y) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x, y := range a {
					if !(x+y > 0) {
						return false
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int :: (x, y) in range a ==> ((x + y) > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Assertion_Numeric_LessLess(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int :: 42 < x < 1337 && x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: 42 < x < 1337 && (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 42 + 1; x < 1337; x++ {
					if x > 0 {
						return true
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: 42 < x < 1337 && (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Assertion_Numeric_LessLessEqual(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int :: 42 < x <= 1337 && x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: 42 < x <= 1337 && (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 42 + 1; x <= 1337; x++ {
					if x > 0 {
						return true
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: 42 < x <= 1337 && (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Assertion_Numeric_LessEqualLess(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int :: 42 <= x < 1337 && x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: 42 <= x < 1337 && (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 42; x < 1337; x++ {
					if x > 0 {
						return true
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: 42 <= x < 1337 && (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Assertion_Numeric_LessEqualLessEqual(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int :: 42 <= x <= 1337 && x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: 42 <= x <= 1337 && (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 42; x <= 1337; x++ {
					if x > 0 {
						return true
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: 42 <= x <= 1337 && (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Assertion_DataStructure_Key(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int :: x in range a && x >= 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: x in range a && (x >= 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := range a {
					if x >= 0 {
						return true
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: x in range a && (x >= 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Assertion_DataStructure_Value(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int :: (_, x) in range a && x > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: (_, x) in range a && (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for _, x := range a {
					if x > 0 {
						return true
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: (_, x) in range a && (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Assertion_DataStructure_KeyAndValue(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x, y int :: (x, y) in range a && x + y > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, y int :: (x, y) in range a && ((x + y) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x, y := range a {
					if x+y > 0 {
						return true
					}
				}
				return false 
			}() {
				panic("Assertion '(exists x int, y int :: (x, y) in range a && ((x + y) > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Conjunction_NestedTwo_DifferentVars(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x, y int :: 0 <= x < 3 && 1 < y <= 4 ==> x + y > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int, y int :: (0 <= x < 3 && 1 < y <= 4) ==> ((x + y) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0; x < 3; x++ {
					for y := 1 + 1; y <= 4; y++ {
						if !(x+y > 0) {
							return false
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int :: (0 <= x < 3 && 1 < y <= 4) ==> ((x + y) > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Conjunction_NestedThree_DifferentVars(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x, y, z int :: 0 <= x < 3 && 1 < y <= 4 && -2 < z < 1 ==> x + y + z > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int, y int, z int :: ((0 <= x < 3 && 1 < y <= 4) && -2 < z < 1) ==> (((x + y) + z) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0; x < 3; x++ {
					for y := 1 + 1; y <= 4; y++ {
						for z := -2 + 1; z < 1; z++ {
							if !(x+y+z > 0) {
								return false
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int, z int :: ((0 <= x < 3 && 1 < y <= 4) && -2 < z < 1) ==> (((x + y) + z) > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Disjunction_SameVariableTwice(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: 0 < x <= 3 || 1 <= x < 4 ==> x > 0 && x < 4
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: (0 < x <= 3 || 1 <= x < 4) ==> ((x > 0) && (x < 4)))': %v", err))
				}
			}()
			if !func() bool {
				{
					for x := 0 + 1; x <= 3; x++ {
						if !(x > 0 && x < 4) {
							return false
						}
					}
					for x := 1; x < 4; x++ {
						if !(x > 0 && x < 4) {
							return false
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: (0 < x <= 3 || 1 <= x < 4) ==> ((x > 0) && (x < 4)))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_Disjunction_SameVariableThrice(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: 0 < x <= 3 || 1 <= x < 4 || 2 < x < 5 ==> x > 0 && x < 5
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: ((0 < x <= 3 || 1 <= x < 4) || 2 < x < 5) ==> ((x > 0) && (x < 5)))': %v", err))
				}
			}()
			if !func() bool {
				{
					{
						for x := 0 + 1; x <= 3; x++ {
							if !(x > 0 && x < 5) {
								return false
							}
						}
						for x := 1; x < 4; x++ {
							if !(x > 0 && x < 5) {
								return false
							}
						}
					}
					for x := 2 + 1; x < 5; x++ {
						if !(x > 0 && x < 5) {
							return false
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: ((0 < x <= 3 || 1 <= x < 4) || 2 < x < 5) ==> ((x > 0) && (x < 5)))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Conjunction_NestedTwo(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x, y int :: 0 <= x < 3 && 1 < y <= 4 && x + y > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, y int :: (0 <= x < 3 && 1 < y <= 4) && ((x + y) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0; x < 3; x++ {
					for y := 1 + 1; y <= 4; y++ {
						if x+y > 0 {
							return true
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, y int :: (0 <= x < 3 && 1 < y <= 4) && ((x + y) > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Conjunction_NestedThree(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x, y int :: 0 <= x < 3 && 1 < y <= 4 && -2 < x < 1 && x + y > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, y int :: ((0 <= x < 3 && 1 < y <= 4) && -2 < x < 1) && ((x + y) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0; x < 3; x++ {
					for y := 1 + 1; y <= 4; y++ {
						if -2 < x && x < 1 {
							if x+y > 0 {
								return true
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, y int :: ((0 <= x < 3 && 1 < y <= 4) && -2 < x < 1) && ((x + y) > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Disjunction_SameVariableTwice(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int :: 0 < x <= 3 || 1 <= x < 4 && x > 0 && x < 4
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: (0 < x <= 3 || 1 <= x < 4) && ((x > 0) && (x < 4)))': %v", err))
				}
			}()
			if !func() bool {
				{
					for x := 0 + 1; x <= 3; x++ {
						if x > 0 && x < 4 {
							return true
						}
					}
					for x := 1; x < 4; x++ {
						if x > 0 && x < 4 {
							return true
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: (0 < x <= 3 || 1 <= x < 4) && ((x > 0) && (x < 4)))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_Disjunction_SameVariableThrice(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int :: 0 < x <= 3 || 1 <= x < 4 || 2 < x < 5 && x > 0 && x < 5
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: ((0 < x <= 3 || 1 <= x < 4) || 2 < x < 5) && ((x > 0) && (x < 5)))': %v", err))
				}
			}()
			if !func() bool {
				{
					{
						for x := 0 + 1; x <= 3; x++ {
							if x > 0 && x < 5 {
								return true
							}
						}
						for x := 1; x < 4; x++ {
							if x > 0 && x < 5 {
								return true
							}
						}
					}
					for x := 2 + 1; x < 5; x++ {
						if x > 0 && x < 5 {
							return true
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: ((0 < x <= 3 || 1 <= x < 4) || 2 < x < 5) && ((x > 0) && (x < 5)))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_NestedDomain_UpperOr(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x, y int :: (x in range a && 0 < y <= 42) || ((_, y) in range a && -42 <= x < 0) ==> x != y
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int, y int :: ((x in range a && 0 < y <= 42) || ((_, y) in range a && -42 <= x < 0)) ==> (x != y))': %v", err))
				}
			}()
			if !func() bool {
				{
					for x := range a {
						for y := 0 + 1; y <= 42; y++ {
							if !(x != y) {
								return false
							}
						}
					}
					for _, y := range a {
						for x := -42; x < 0; x++ {
							if !(x != y) {
								return false
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int :: ((x in range a && 0 < y <= 42) || ((_, y) in range a && -42 <= x < 0)) ==> (x != y))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_NestedDomain_UpperAnd(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x, y int :: (x in range a || 0 < x <= 42) && ((_, y) in range a || -42 <= y < 0) ==> x != y
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int, y int :: ((x in range a || 0 < x <= 42) && ((_, y) in range a || -42 <= y < 0)) ==> (x != y))': %v", err))
				}
			}()
			if !func() bool {
				{
					for x := range a {
						{
							for _, y := range a {
								if !(x != y) {
									return false
								}
							}
							for y := -42; y < 0; y++ {
								if !(x != y) {
									return false
								}
							}
						}
					}
					for x := 0 + 1; x <= 42; x++ {
						{
							for _, y := range a {
								if !(x != y) {
									return false
								}
							}
							for y := -42; y < 0; y++ {
								if !(x != y) {
									return false
								}
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int :: ((x in range a || 0 < x <= 42) && ((_, y) in range a || -42 <= y < 0)) ==> (x != y))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_NestedDomain_UpperAnd_DeeperLeft(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x, y int :: (x in range a || 0 < x <= 42) && (_, y) in range a && x != y
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, y int :: ((x in range a || 0 < x <= 42) && (_, y) in range a) && (x != y))': %v", err))
				}
			}()
			if !func() bool {
				{
					for x := range a {
						for _, y := range a {
							if x != y {
								return true
							}
						}
					}
					for x := 0 + 1; x <= 42; x++ {
						for _, y := range a {
							if x != y {
								return true
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, y int :: ((x in range a || 0 < x <= 42) && (_, y) in range a) && (x != y))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_NestedDomain_UpperAnd_DeeperRight(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x, y int :: x in range a  && ((_, y) in range a || 0 < y <= 42) && x != y
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, y int :: (x in range a && ((_, y) in range a || 0 < y <= 42)) && (x != y))': %v", err))
				}
			}()
			if !func() bool {
				for x := range a {
					{
						for _, y := range a {
							if x != y {
								return true
							}
						}
						for y := 0 + 1; y <= 42; y++ {
							if x != y {
								return true
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, y int :: (x in range a && ((_, y) in range a || 0 < y <= 42)) && (x != y))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_SameVariableConstraints_OneVar(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: (_, x) in range a  && 0 < x < 3 && x in range a ==> x > 0 
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: (((_, x) in range a && 0 < x < 3) && x in range a) ==> (x > 0))': %v", err))
				}
			}()
			if !func() bool {
				for _, x := range a {
					if 0 < x && x < 3 {
						if x >= 0 && x <= len(a) {
							if !(x > 0) {
								return false
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: (((_, x) in range a && 0 < x < 3) && x in range a) ==> (x > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_SameVariableConstraints_OneVar_Nested(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int, y int :: (_, y) in range a  && 0 < x < 3 && y in range a ==> x + y > 0 
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int, y int :: (((_, y) in range a && 0 < x < 3) && y in range a) ==> ((x + y) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for _, y := range a {
					for x := 0 + 1; x < 3; x++ {
						if y >= 0 && y <= len(a) {
							if !(x+y > 0) {
								return false
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int :: (((_, y) in range a && 0 < x < 3) && y in range a) ==> ((x + y) > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_SameVariableConstraints_TwoVars(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x, y int :: (x, y) in range a  && ((_, y) in range a || 0 < x <= 42) && x != y
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, y int :: ((x, y) in range a && ((_, y) in range a || 0 < x <= 42)) && (x != y))': %v", err))
				}
			}()
			if !func() bool {
				for x, y := range a {
					{
						for _, y81 := range a {
							if y81 == y {
								if x != y {
									return true
								}
							}
						}
						if 0 < x && x <= 42 {
							if x != y {
								return true
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, y int :: ((x, y) in range a && ((_, y) in range a || 0 < x <= 42)) && (x != y))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_BooleanVars(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int, b, c bool :: x in range a ==> x > 0 && (b || c)
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int, b bool, c bool :: x in range a ==> ((x > 0) && (b || c)))': %v", err))
				}
			}()
			if !func() bool {
				for x := range a {
					for _, c := range [2]bool{true, false} {
						for _, b := range [2]bool{true, false} {
							if !(x > 0 && (b || c)) {
								return false
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, b bool, c bool :: x in range a ==> ((x > 0) && (b || c)))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_BooleanVars(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x int, b, c bool :: x in range a && x > 0 && (b || c)
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, b bool, c bool :: x in range a && ((x > 0) && (b || c)))': %v", err))
				}
			}()
			if !func() bool {
				for x := range a {
					for _, c := range [2]bool{true, false} {
						for _, b := range [2]bool{true, false} {
							if x > 0 && (b || c) {
								return true
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, b bool, c bool :: x in range a && ((x > 0) && (b || c)))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_BooleanVarHasDomain(t *testing.T) {
	input := `package test
	func foo() []bool {
		a := []bool{true, false, true}
		//@ assert exists x int, b, c bool :: 0 < x < 42 &&  (_, b) in range a && x > 0 || (b && !c)
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []bool {
		a := []bool{true, false, true}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, b bool, c bool :: (0 < x < 42 && (_, b) in range a) && ((x > 0) || (b && !c)))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0 + 1; x < 42; x++ {
					for _, b := range a {
						for _, c := range [2]bool{true, false} {
							if x > 0 || b && !c {
								return true
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, b bool, c bool :: (0 < x < 42 && (_, b) in range a) && ((x > 0) || (b && !c)))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestUniversalQuantifier_OnlyBooleanVars(t *testing.T) {
	input := `package test
	func foo() {
		//@ assert forall a, b, c bool :: (a && b && c)
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert (forall a bool, b bool, c bool :: ((a && b) && c))': %v", err))
				}
			}()
			if !func() bool {
				for _, c := range [2]bool{true, false} {
					for _, b := range [2]bool{true, false} {
						for _, a := range [2]bool{true, false} {
							if !(a && b && c) {
								return false
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall a bool, b bool, c bool :: ((a && b) && c))' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestExistentialQuantifier_OnlyBooleanVars(t *testing.T) {
	input := `package test
	func foo() {
		//@ assert exists a, b, c bool :: (a && b && c)
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert (exists a bool, b bool, c bool :: ((a && b) && c))': %v", err))
				}
			}()
			if !func() bool {
				for _, c := range [2]bool{true, false} {
					for _, b := range [2]bool{true, false} {
						for _, a := range [2]bool{true, false} {
							if a && b && c {
								return true
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists a bool, b bool, c bool :: ((a && b) && c))' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_NestedBooleanVars(t *testing.T) {
	input := `package test
	func foo() {
		//@ assert exists x, y int, a bool :: 0 < y < 3 && 0 < x < 42 || 0 < x < 3 && 0 < y < 1337 && (a || x + y > 0)
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert (exists x int, y int, a bool :: ((0 < y < 3 && 0 < x < 42) || (0 < x < 3 && 0 < y < 1337)) && (a || ((x + y) > 0)))': %v", err))
				}
			}()
			if !func() bool {
				{
					for y := 0 + 1; y < 3; y++ {
						for x := 0 + 1; x < 42; x++ {
							for _, a := range [2]bool{true, false} {
								if a || x+y > 0 {
									return true
								}
							}
						}
					}
					for x := 0 + 1; x < 3; x++ {
						for y := 0 + 1; y < 1337; y++ {
							for _, a := range [2]bool{true, false} {
								if a || x+y > 0 {
									return true
								}
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, y int, a bool :: ((0 < y < 3 && 0 < x < 42) || (0 < x < 3 && 0 < y < 1337)) && (a || ((x + y) > 0)))' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestNestedQuantifiers1(t *testing.T) {
	input := `package test
	//@ requires x > 0 && (forall y int :: (_, y) in range a ==> x + y > 0) || false
	func foo(x int, a []int) int {
		return x + 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int, a []int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (((x > 0) && (forall y int :: (_, y) in range a ==> ((x + y) > 0))) || false)': %v", err))
				}
			}()
			if !(x > 0 && func() bool {
				for _, y := range a {
					if !(x+y > 0) {
						return false
					}
				}
				return true
			}() || false) {
				panic("Precondition '(((x > 0) && (forall y int :: (_, y) in range a ==> ((x + y) > 0))) || false)' violated.")
			}
		}()
		return x + 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestNestedQuantifiers2(t *testing.T) {
	input := `package test
	//@ requires forall y int :: y in range a ==> exists z int :: (_, z) in range a && z == a[y]
	func foo(x int, a []int) int {
		return x + 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int, a []int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (forall y int :: y in range a ==> (exists z int :: (_, z) in range a && (z == a[y])))': %v", err))
				}
			}()
			if !func() bool {
				for y := range a {
					if !func() bool {
						for _, z := range a {
							if z == a[y] {
								return true
							}
						}
						return false
					}() {
						return false
					}
				}
				return true
			}() {
				panic("Precondition '(forall y int :: y in range a ==> (exists z int :: (_, z) in range a && (z == a[y])))' violated.")
			}
		}()
		return x + 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestNestedQuantifiers3(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall y int :: y in range a ==> exists z int :: (y, z) in range a && y + z == 42
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall y int :: y in range a ==> (exists z int :: (y, z) in range a && ((y + z) == 42)))': %v", err))
				}
			}()
			if !func() bool {
				for y := range a {
					if !func() bool {
						for y81, z := range a {
							if y81 == y {
								if y+z == 42 {
									return true
								}
							}
						}
						return false
					}() {
						return false
					}
				}
				return true
			}() {
				panic("Assertion '(forall y int :: y in range a ==> (exists z int :: (y, z) in range a && ((y + z) == 42)))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifiers_Ordering(t *testing.T) {
	input := `package test
	func foo() {
		//@ assert exists x, y int :: 0 < y < x && 0 < x < 42 && x + y > 0
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert (exists x int, y int :: (0 < y < x && 0 < x < 42) && ((x + y) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0 + 1; x < 42; x++ {
					for y := 0 + 1; y < x; y++ {
						if x+y > 0 {
							return true
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, y int :: (0 < y < x && 0 < x < 42) && ((x + y) > 0))' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifiers_Ordering_Nested(t *testing.T) {
	input := `package test
	type bar struct {
		val int
	}
	func foo() []bar {
		a := []bar{}
		//@ assert forall x, y int, z bar :: 0 < y < z.val && (0 < x < 42 ||  0 < x < z.val) && (_, z) in range a ==> x + y > 0
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type bar struct {
		val int
	}
	func foo() []bar {
		a := []bar{}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 7, Specification 'assert (forall x int, y int, z bar :: ((0 < y < z.val && (0 < x < 42 || 0 < x < z.val)) && (_, z) in range a) ==> ((x + y) > 0))': %v", err))
				}
			}()
			if !func() bool {
				for _, z := range a {
					for y := 0 + 1; y < z.val; y++ {
						{
							for x := 0 + 1; x < 42; x++ {
								if !(x+y > 0) {
									return false
								}
							}
							for x := 0 + 1; x < z.val; x++ {
								if !(x+y > 0) {
									return false
								}
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int, z bar :: ((0 < y < z.val && (0 < x < 42 || 0 < x < z.val)) && (_, z) in range a) ==> ((x + y) > 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifier_Ordering_Cyclic(t *testing.T) {
	wantPanic := "Domain (0 < x <= y && 1 <= y < x) of quantifier (forall x int,y int :: (0 < x <= y && 1 <= y < x) ==> ((x + y) > 0)) uses identifers y and x in a cycling dependency between bounds and quantified variables"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo() {
		//@ assert forall x, y int :: 0 < x <= y && 1 <= y < x ==> x + y > 0 
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestQuantifiers_Ordering_Cyclic_Nested(t *testing.T) {
	wantPanic := "Domain ((z in range a && 0 < y < x) && (0 < x < 42 || 0 < x < z.val)) of quantifier (forall x int,y int,z cmd/gorac.bar :: ((z in range a && 0 < y < x) && (0 < x < 42 || 0 < x < z.val)) ==> ((x + y) > 0)) uses identifers x and z in a cycling dependency between bounds and quantified variables"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	type bar struct {
		val int
	}
	func foo() []bar {
		a := []bar{}
		//@ assert forall x, y int, z bar :: z in range a && 0 < y < x && (0 < x < 42 ||  0 < x < z.val) ==> x + y > 0
		return a
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestExistentialQuantifier_Disjunction_DifferentVariables(t *testing.T) {
	wantPanic := "Quantifier '(exists x int,y int :: (0 < x <= 3 || 1 <= y < 4) && ((x + y) > 0))' from specification 'assert (exists x int, y int :: (0 < x <= 3 || 1 <= y < 4) && ((x + y) > 0))' at line 4 needs bound for variable 'x'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert exists x, y int :: 0 < x <= 3 || 1 <= y < 4 && x + y > 0 
		return a
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestQuantifiers_MapOptimizations_Key(t *testing.T) {
	input := `package test
	func foo() map[int]int {
		m := map[int]int{1:1, 2:2, 3:3,} 
		//@ assert exists x int :: 0 < x < 42 && x in range m && m[x] == x 
		return m
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() map[int]int {
		m := map[int]int{1: 1, 2: 2, 3: 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int :: (0 < x < 42 && x in range m) && (m[x] == x))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0 + 1; x < 42; x++ {
					if _, ok87 := m[x]; ok87 {
						if m[x] == x {
							return true
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int :: (0 < x < 42 && x in range m) && (m[x] == x))' violated.")
			}
		}()
		return m
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifiers_ArraySliceOptimizations_Key(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x int :: 0 < x < 42 && x in range a ==> x >= 0 
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int :: (0 < x < 42 && x in range a) ==> (x >= 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0 + 1; x < 42; x++ {
					if x >= 0 && x <= len(a) {
						if !(x >= 0) {
							return false
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int :: (0 < x < 42 && x in range a) ==> (x >= 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifiers_MapOptimizations_KeyValue(t *testing.T) {
	input := `package test
	func foo() map[int]int {
		m := map[int]int{1:1, 2:2, 3:3,} 
		//@ assert exists x, y int :: 0 < x < 42 && 0 < y < 1337 && x, y in range m && m[x] == y
		return m
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() map[int]int {
		m := map[int]int{1: 1, 2: 2, 3: 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (exists x int, y int :: ((0 < x < 42 && 0 < y < 1337) && (x, y) in range m) && (m[x] == y))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0 + 1; x < 42; x++ {
					for y := 0 + 1; y < 1337; y++ {
						if y87, ok47 := m[x]; ok47 && y == y87 {
							if m[x] == y {
								return true
							}
						}
					}
				}
				return false
			}() {
				panic("Assertion '(exists x int, y int :: ((0 < x < 42 && 0 < y < 1337) && (x, y) in range m) && (m[x] == y))' violated.")
			}
		}()
		return m
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifiers_ArraySliceOptimizations_KeyValue(t *testing.T) {
	input := `package test
	func foo() []int {
		a := []int{1, 2, 3}
		//@ assert forall x, y int :: 0 < x < 42 && 0 < y < 1337 && x, y in range a ==> x + y >= 0 
		return a
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() []int {
		a := []int{1, 2, 3}
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert (forall x int, y int :: ((0 < x < 42 && 0 < y < 1337) && (x, y) in range a) ==> ((x + y) >= 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0 + 1; x < 42; x++ {
					for y := 0 + 1; y < 1337; y++ {
						if x >= 0 && x <= len(a) && a[x] == y {
							if !(x+y >= 0) {
								return false
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int :: ((0 < x < 42 && 0 < y < 1337) && (x, y) in range a) ==> ((x + y) >= 0))' violated.")
			}
		}()
		return a
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestQuantifiers_NumericDomainOptimization(t *testing.T) {
	input := `package test
	func foo() {
		//@ assert forall x, y int :: 0 < x < 42 && 0 < x <= 1337 && -42 <= y < 0 && -1337 <= y <= 0 ==> x + y >= 0 
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo() {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert (forall x int, y int :: (((0 < x < 42 && 0 < x <= 1337) && -42 <= y < 0) && -1337 <= y <= 0) ==> ((x + y) >= 0))': %v", err))
				}
			}()
			if !func() bool {
				for x := 0 + 1; x < 42; x++ {
					if 0 < x && x <= 1337 {
						for y := -42; y < 0; y++ {
							if -1337 <= y && y <= 0 {
								if !(x+y >= 0) {
									return false
								}
							}
						}
					}
				}
				return true
			}() {
				panic("Assertion '(forall x int, y int :: (((0 < x < 42 && 0 < x <= 1337) && -42 <= y < 0) && -1337 <= y <= 0) ==> ((x + y) >= 0))' violated.")
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestAccessPermission_StructPointer_Implicit(t *testing.T) {
	input := `package test
	type s struct {
		val int
	}
	//@ requires acc(x.val)
	func foo(x *s) {
		x.val = 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type s struct {
		val int
	}
	func foo(x *s) {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 5, Specification 'requires acc(x.val)': %v", err))
				}
			}()
			if !(x != nil) {
				panic("Precondition 'acc(x.val)' violated.")
			}
		}()
		x.val = 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestAccessPermission_StructPointer_ImplicitDouble(t *testing.T) {
	input := `package test
	type s struct {
		tStruct *t
	}
	type t struct {
		val int
	}
	//@ requires acc(x.tStruct.val)
	func foo(x *s) {
		x.tStruct.val = 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type s struct {
		tStruct *t	
	}
	type t struct {
		val int
	}
	func foo(x *s) {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 8, Specification 'requires acc(x.tStruct.val)': %v", err))
				}
			}()
			if !((*x).tStruct != nil) {
				panic("Precondition 'acc(x.tStruct.val)' violated.")
			}
		}()
		x.tStruct.val = 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestAccessPermission_StructPointer_Explicit(t *testing.T) {
	input := `package test
	type s struct {
		val int
	}
	//@ requires acc((*x).val)
	func foo(x *s) {
		x.val = 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type s struct {
		val int
	}
	func foo(x *s) {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 5, Specification 'requires acc((*x).val)': %v", err))
				}
			}()
			if !(x != nil) {
				panic("Precondition 'acc((*x).val)' violated.")
			}
		}()
		x.val = 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestAccessPermission_StructPointer_ExplicitDouble(t *testing.T) {
	input := `package test
	type s struct {
		tStruct *t
	}
	type t struct {
		val int
	}
	//@ requires acc((*(*x).tStruct).val)
	func foo(x *s) {
		x.tStruct.val = 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type s struct {
		tStruct *t	
	}
	type t struct {
		val int
	}
	func foo(x *s) {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 8, Specification 'requires acc((*(*x).tStruct).val)': %v", err))
				}
			}()
			if !((*x).tStruct != nil) {
				panic("Precondition 'acc((*(*x).tStruct).val)' violated.")
			}
		}()
		x.tStruct.val = 42
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestAccessPermission_Pointer(t *testing.T) {
	input := `package test
	//@ requires acc(x)
	func foo(x *int) int{
		return *x	
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x *int) int{
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires acc(x)': %v", err))
				}
			}()
			if !(x != nil) {
				panic("Precondition 'acc(x)' violated.")
			}
		}()
		return *x
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestAccessPermission_Reference(t *testing.T) {
	input := `package test
	//@ requires acc(&x)
	func foo(x int) int {
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires acc(&x)': %v", err))
				}
			}()
			if !(&x != nil) {
				panic("Precondition 'acc(&x)' violated.")
			}
		}()
		return x
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestPredicate_OneParameter(t *testing.T) {
	input := `package test
	//@ predicate Positive(x int) { x > 0 }
	func foo(x int) int {
		//@ assert Positive(x)
		return x
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 4, Specification 'assert Positive(x)': %v", err))
				}
			}()
			if !PositivePredicate81(x) {
				panic("Assertion 'Positive(x)' violated.")
			}
		}()
		return x
	}
	func PositivePredicate81(x int) bool {
		return x > 0
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestPredicate_MultipleParameters(t *testing.T) {
	input := `package test
	type foo struct {}
	type bar struct {}
	func randomFunc(x, y int) int {
		//@ predicate Random(x, y int, z bool, f foo, b bar) { x > y && z && f == foo{} && b != bar{} }
		//@ assert Random(x, y, x >= y, foo{}, bar{})
		return x + y
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type foo struct{}
	type bar struct{}
	func randomFunc(x, y int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 6, Specification 'assert Random(x, y, (x >= y), foo{}, bar{})': %v", err))
				}
			}()
			if !RandomPredicate81(x, y, x >= y, foo{}, bar{}) {
				panic("Assertion 'Random(x, y, (x >= y), foo{}, bar{})' violated.")
			}
		}()
		return x + y
	}
	func RandomPredicate81(x int, y int, z bool, f foo, b bar) bool {
		return x > y && z && f == foo{} && b != bar{}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestPredicate_WrongSingleValue(t *testing.T) {
	wantPanic := "Cannot use type 'bool' of value '(x > y)' as type 'int' for parameter 'x' in predicate call 'Positive((x > y))' at line 4"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	//@ predicate Positive(x int) { x > 0 }
	func foo(x, y int) int {
		//@ assert Positive(x > y)
		return x + y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPredicate_NonUniqueName(t *testing.T) {
	wantPanic := "Predicate name 'foo' at line 2 must be unique, collides with object 'func cmd/gorac.foo(x int, y int) int'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	//@ predicate foo(x int) { x > 0 }
	func foo(x, y int) int {
		//@ assert foo(x)
		return x + y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPredicate_WrongMultipleValues(t *testing.T) {
	wantPanic := "Cannot use type 'cmd/gorac.bar' of value 'bar{}' as type 'cmd/gorac.foo' for parameter 'f' in predicate call 'Random(x, y, (x >= y), bar{}, foo{})' at line 8"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	type foo struct {}
	type bar struct {}
	func randomFunc(x, y int) int {
		//@ predicate Random(x, y int, z bool, f foo, b bar) { 
		//@ 			x > y && z && f == foo{} && b != bar{} 
		//@ }
		//@ assert Random(x, y, x >= y, bar{}, foo{})
		return x + y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPredicate_InScopePrecondition(t *testing.T) {
	input := `package test
	//@ requires Positive(x) && Positive(y)
	func foo(x, y int) int {
		return x + y
		//@ predicate Positive(x int) { 
		//@ 		x > 0 
		//@ }	
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x, y int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 2, Specification 'requires (Positive(x) && Positive(y))': %v", err))
				}
			}()
			if !(PositivePredicate81(x) && PositivePredicate81(y)) {
				panic("Precondition '(Positive(x) && Positive(y))' violated.")
			}
		}()
		return x + y
	}
	func PositivePredicate81(x int) bool {
		return x > 0
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestPredicate_OutOfScope(t *testing.T) {
	wantPanic := "Predicate call 'Positive(x)' at line 3 out of scope of predicate declaration 'predicate Positive(x int) { (x > 0) }' at line 7"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo(x, y int) int {
		//@ assert Positive(x) && Positive(y)
		return x + y
	}
	func bar() {
		//@ predicate Positive(x int) { x > 0 }	
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPredicate_DeclaredTwice(t *testing.T) {
	wantPanic := "Predicate 'Positive' declared twice: at line 4 and line 5"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo(x, y int) int {
		//@ assert Positive(x) || Positive(y)
		//@ predicate Positive(x int) { x > 0 }	
		//@ predicate Positive(x int) { x > 0 }	
		return x + y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPredicate_ContainsOldExpression(t *testing.T) {
	wantPanic := "Predicate 'predicate Positive(x int) { (old(x) > 0) }' at line 3 is not allowed to contain old expressions."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo(x, y int) int {
		//@ assert Positive(x) || Positive(y)
		//@ predicate Positive(x int) { old(x) > 0 }	
		return x + y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestImplication(t *testing.T) {
	input := `package test
	func foo(x, y int) int {
		//@ assert x > y ==> x > 0
		return x + y
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x, y int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert ((x > y) ==> (x > 0))': %v", err))
				}
			}()
			if !(!(x > y) || x > 0) {
				panic("Assertion '((x > y) ==> (x > 0))' violated.")
			}
		}()
		return x + y
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestPredicateImplication(t *testing.T) {
	input := `package test
	/*@ 
		predicate Zero(x int) {
			!(x > 0 || x < 0) ==> x == 0
		}
     	predicate Negative(x int) { x < 0 }
	@*/
	func foo(x, y int) int {
		//@ assert (y < x && Zero(x)) ==> Negative(y)
		return x + y
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x, y int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 9, Specification 'assert (((y < x) && Zero(x)) ==> Negative(y))': %v", err))
				}
			}()
			if !(!(y < x && ZeroPredicate81(x)) || NegativePredicate87(y)) {
				panic("Assertion '(((y < x) && Zero(x)) ==> Negative(y))' violated.")
			}
		}()
		return x + y
	}
	func ZeroPredicate81(x int) bool {
		return !(!(x > 0 || x < 0) || x == 0)
	}
	func NegativePredicate87(x int) bool {
		return x < 0
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestTernaryOperator_Boolean(t *testing.T) {
	input := `package test
	func foo(x, y int) int {
		//@ assert x > y ? x == 42 : y == 1337 
		return x + y
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x, y int) int {
		func() {
			defer func() {
				if err := recover(); err != nil {
					panic(fmt.Sprintf("Line 3, Specification 'assert ((x > y) ? (x == 42) : (y == 1337))': %v", err))
				}
			}()
			if !func() bool {
				if x > y {
					return x == 42
				} else {
					return y == 1337
				}
			}() {
				panic("Assertion '((x > y) ? (x == 42) : (y == 1337))' violated.")
			}
		}()
		return x + y
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestTernary_NonBooleanCondition(t *testing.T) {
	wantPanic := "Condition '(x + 1)' of ternary operator '((x + 1) ? (x == 42) : (y == 1337))' at line 3 needs to be boolean"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo(x, y int) int {
		//@ assert x + 1 ? x == 42 : y == 1337 
		return x + y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestTernary_NonBooleanPositiveBranch(t *testing.T) {
	wantPanic := "Branch '(x + 1)' of ternary operator '((x > y) ? (x + 1) : (y == 1337))' at line 3 needs to be boolean"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo(x, y int) int {
		//@ assert x > y ? x + 1 : y == 1337 
		return x + y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestTernary_NonBooleanNegativeBranch(t *testing.T) {
	wantPanic := "Branch '(y + 1)' of ternary operator '((x > y) ? (x == 42) : (y + 1))' at line 3 needs to be boolean"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo(x, y int) int {
		//@ assert x > y ? x == 42 : (y + 1)
		return x + y
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestPredicateTernaryOperator(t *testing.T) {
	input := `package test
	/*@ 
		predicate isMaximum(max, other int) {
			max >= other ? true : false
		}
     	predicate oneEqualFortyTwo(x, y int) { x == 42 ? true : y == 42 }
	@*/
	//@ ensures isMaximum(x, y) && oneEqualFortyTwo(x, y)
	func foo(x, y int) int {
		return x + y
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func foo(x, y int) int {
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 6, Specification 'ensures (isMaximum(x, y) && oneEqualFortyTwo(x, y))': %v", err))
					}
				}()
				if !(isMaximumPredicate81(x, y) && oneEqualFortyTwoPredicate87(x, y)) {
					panic("Postcondition '(isMaximum(x, y) && oneEqualFortyTwo(x, y))' violated.")
				}
			}()
		}()
		return x + y
	}
	func isMaximumPredicate81(max int, other int) bool {
		return func() bool {
			if max >= other {
				return true
			} else {
				return false
			}
		}()
	}
	func oneEqualFortyTwoPredicate87(x int, y int) bool {
		return func() bool {
			if x == 42 {
				return true
			} else {
				return y == 42
			}
		}()
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestRecursivePredicate_ImplicitStructPointer(t *testing.T) {
	input := `package test
	type Foo struct {
		A *Foo
		B int
	}
	/*@ 
	predicate pred(x *Foo) {
  		x != nil ==> acc(x.B) && acc(x.A) && pred(x.A)
	}
	ensures pred(fooObj)
	@*/
	func foo(fooObj *Foo) int {
		return 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	type Foo struct {
		A *Foo
		B int
	}
	func foo(fooObj *Foo) int {
		defer func() {
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 10, Specification 'ensures pred(fooObj)': %v", err))
					}
				}()
				if !predPredicate81(fooObj) {
					panic("Postcondition 'pred(fooObj)' violated.")
				}
			}()
		}()
		return 42
	}
	func predPredicate81(x *Foo) bool {
		return !(x != nil) || x != nil && x != nil && predPredicate81((*x).A)
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestNamedReturnParameters(t *testing.T) {
	input := `package test
	func foo() (x int) {
		return 42
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	func foo() (x int) {
		{
			x = 42
		}
		return x
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestNamedReturnParameters_FunctionCall(t *testing.T) {
	input := `package test
	func bar() (int, int) {
		return 42, 1337
	}
	func foo() (x, y int) {
		return bar()
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	func bar() (int, int) {
		return 42, 1337
	}
	func foo() (x, y int) {
		{
			x, y = bar()
		}
		return x, y
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}
