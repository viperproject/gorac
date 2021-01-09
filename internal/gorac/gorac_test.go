// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"flag"
	"reflect"
	"strings"
	"testing"
)

func TestParseFlags(t *testing.T) {
	var tests = []struct {
		args []string
		conf Config
	}{
		{[]string{"-file=foo.go"},
			Config{inputFile: "foo.go", outputFile: "foo_rac.go", printInputFile: false, printInputAST: false,
				printOutputFile: false, printOutputAST: false, writeOutputFile: false, generateAssertionChecks: true,
				generatePrePostChecks: true, generateInvariantsChecks: true}},
		{[]string{"-file=foo.go", "-outputFile=bar.go"},
			Config{inputFile: "foo.go", outputFile: "bar.go", printInputFile: false, printInputAST: false,
				printOutputFile: false, printOutputAST: false, writeOutputFile: false, generateAssertionChecks: true,
				generatePrePostChecks: true, generateInvariantsChecks: true}},
		{[]string{"-file=foo.go", "-outputFile=bar.go", "-printInputAST", "-printOutputFile"},
			Config{inputFile: "foo.go", outputFile: "bar.go", printInputFile: false, printInputAST: true,
				printOutputFile: true, printOutputAST: false, writeOutputFile: false, generateAssertionChecks: true,
				generatePrePostChecks: true, generateInvariantsChecks: true}},
	}
	for _, tt := range tests {
		t.Run(strings.Join(tt.args, " "), func(t *testing.T) {
			conf, output, err := ParseFlags("gorac", tt.args)
			if err != nil {
				t.Errorf("err got %v, want nil", err)
			}
			if output != "" {
				t.Errorf("output got %q, want empty", output)
			}
			if !reflect.DeepEqual(*conf, tt.conf) {
				t.Errorf("conf got %+v, want %+v", *conf, tt.conf)
			}
		})
	}
}

func TestParseFlags_Usage(t *testing.T) {
	var usageArgs = []string{"-help", "-h", "--help"}
	for _, arg := range usageArgs {
		t.Run(arg, func(t *testing.T) {
			conf, output, err := ParseFlags("gorac", []string{arg})
			if err != flag.ErrHelp {
				t.Errorf("err got %v, want ErrHelp", err)
			}
			if conf != nil {
				t.Errorf("conf got %v, want nil", conf)
			}
			if strings.Index(output, "Usage of") < 0 {
				t.Errorf("output can't find \"Usage of\": %q", output)
			}
		})
	}
}

func TestParseFlags_Error(t *testing.T) {
	var tests = []struct {
		args   []string
		errstr string
	}{
		{[]string{"-foo"}, "flag provided but not defined"},
	}

	for _, tt := range tests {
		t.Run(strings.Join(tt.args, " "), func(t *testing.T) {
			conf, output, err := ParseFlags("gorac", tt.args)
			if conf != nil {
				t.Errorf("conf got %v, want nil", conf)
			}
			if err != nil && strings.Index(err.Error(), tt.errstr) < 0 {
				t.Errorf("err got %q, want to find %q", err.Error(), tt.errstr)
			}
			if strings.Index(output, "Usage of gorac") < 0 {
				t.Errorf("output got %q", output)
			}
		})
	}
}

func TestRACGenerationConfiguration_NoAssertions(t *testing.T) {
	config := &Config{
		inputFile:                "",
		outputFile:               "",
		printInputFile:           false,
		printInputAST:            false,
		printOutputFile:          false,
		printOutputAST:           false,
		writeOutputFile:          false,
		generateAssertionChecks:  false,
		generatePrePostChecks:    true,
		generateInvariantsChecks: true,
	}
	input := `package test
	//@ requires true
	//@ ensures false
	func main() {
		//@ assert true
		//@ invariant false
		for {}
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
						panic(fmt.Sprintf("Line 3, Specification 'ensures false': %v", err))
					}
				}()
				if !false {
					panic("Postcondition 'false' violated.")
				}
			}()
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
		{
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 7, Specification 'invariant false': %v", err))
					}
				}()
				if !false {
					panic("Invariant 'false' violated before loop execution.")
				}
			}()
			for {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 7, Specification 'invariant false': %v", err))
						}
					}()
					if !false {
						panic("Invariant 'false' violated during loop execution.")
					}
				}()
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 7, Specification 'invariant false': %v", err))
					}
				}()
				if !false {
					panic("Invariant 'false' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}

func TestRACGenerationConfiguration_NoCodeContracts(t *testing.T) {
	config := &Config{
		inputFile:                "",
		outputFile:               "",
		printInputFile:           false,
		printInputAST:            false,
		printOutputFile:          false,
		printOutputAST:           false,
		writeOutputFile:          false,
		generateAssertionChecks:  true,
		generatePrePostChecks:    false,
		generateInvariantsChecks: true,
	}
	input := `package test
	//@ requires true
	//@ ensures false
	func main() {
		//@ assert true
		//@ invariant false
		for {}
	}`
	fset, _, n := ComputeRuntimeAssertionChecks(config, input)
	got := getTestOutput(fset, n)
	want := `package test
	import "fmt"
	func main() {
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
		{
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 7, Specification 'invariant false': %v", err))
					}
				}()
				if !false {
					panic("Invariant 'false' violated before loop execution.")
				}
			}()
			for {
				func() {
					defer func() {
						if err := recover(); err != nil {
							panic(fmt.Sprintf("Line 7, Specification 'invariant false': %v", err))
						}
					}()
					if !false {
						panic("Invariant 'false' violated during loop execution.")
					}
				}()
			}
			func() {
				defer func() {
					if err := recover(); err != nil {
						panic(fmt.Sprintf("Line 7, Specification 'invariant false': %v", err))
					}
				}()
				if !false {
					panic("Invariant 'false' violated after loop execution.")
				}
			}()
		}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}
func TestRACGenerationConfiguration_NoInvariants(t *testing.T) {
	config := &Config{
		inputFile:                "",
		outputFile:               "",
		printInputFile:           false,
		printInputAST:            false,
		printOutputFile:          false,
		printOutputAST:           false,
		writeOutputFile:          false,
		generateAssertionChecks:  true,
		generatePrePostChecks:    true,
		generateInvariantsChecks: false,
	}
	input := `package test
	//@ requires true
	//@ ensures false
	func main() {
		//@ assert true
		//@ invariant false
		for {}
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
						panic(fmt.Sprintf("Line 3, Specification 'ensures false': %v", err))
					}
				}()
				if !false {
					panic("Postcondition 'false' violated.")
				}
			}()
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
					panic(fmt.Sprintf("Line 5, Specification 'assert true': %v", err))
				}
			}()
			if !true {
				panic("Assertion 'true' violated.")
			}
		}()
		for {}
	}`
	if clean(got) != clean(want) {
		t.Errorf("got:\n %v want:\n %s", clean(got), clean(want))
	}
}
