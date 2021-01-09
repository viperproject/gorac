// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package gorac

import (
	"testing"
)

// Unit tests for quantifierchecker.go

func TestQuantifierChecker_Ok(t *testing.T) {
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			t.Errorf("got panic:\n %v want no panic", gotPanic.(string))
		}
	}()
	input := `package test
		func foo() {
			//@ assert forall x int :: 0 < x < 3 ==> x > 0 
		}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestQuantifierChecker_MissingDomain(t *testing.T) {
	wantPanic := "Quantifier '(forall x int :: (x > 42))' from specification 'assert (forall x int :: (x > 42))' at line 3 needs bound for variable 'x'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	func foo() { 
		//@ assert forall x int :: x > 42	
	}`
	ComputeRuntimeAssertionChecks(config, input)
}

func TestQuantifierChecker_MultipleMissingDomains(t *testing.T) {
	wantPanic := "Quantifier '(forall x int,y int,b bool,z cmd/gorac.foo :: (0 < x < 3 && z in range [3]cmd/gorac.foo{}) ==> ((((x + y) + z.bar) == 1337) || b))' from specification 'assert (forall x int, y int, b bool, z foo :: (0 < x < 3 && z in range [3]foo{}) ==> ((((x + y) + z.bar) == 1337) || b))' at line 6 needs bound for variable 'y'"
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if clean(gotPanic.(string)) != clean(wantPanic) {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `package test
	type foo struct {
		bar int
	}
	func f() { 
		//@ assert forall x, y int, b bool, z foo :: 0 < x < 3 && z in range [3]foo{} ==> x + y + z.bar == 1337 || b
	}`
	ComputeRuntimeAssertionChecks(config, input)
}
