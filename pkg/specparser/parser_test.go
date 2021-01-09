// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package specparser

import (
	"testing"
)

func TestTrue(t *testing.T) {
	input := "assert true"
	got := Parse(input)
	want := "assert true"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestFalse(t *testing.T) {
	input := "assert false"
	got := Parse(input)
	want := "assert false"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestVariable(t *testing.T) {
	input := "assert booleanVar"
	got := Parse(input)
	want := "assert booleanVar"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestDigit(t *testing.T) {
	input := "assert a == 42"
	got := Parse(input)
	want := "assert (a == 42)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestNil(t *testing.T) {
	input := "assert a != nil"
	got := Parse(input)
	want := "assert (a != nil)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}
func TestUnaryPlus(t *testing.T) {
	input := "assert a == +42"
	got := Parse(input)
	want := "assert (a == +42)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUnaryMinus(t *testing.T) {
	input := "assert a == -42"
	got := Parse(input)
	want := "assert (a == -42)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUnaryNot(t *testing.T) {
	input := "assert !false || !(b && !c)"
	got := Parse(input)
	want := "assert (!false || !(b && !c))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestBinaryLogical(t *testing.T) {
	input := "assert a || b && c"
	got := Parse(input)
	want := "assert (a || (b && c))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestBinaryArithmetic(t *testing.T) {
	input := "assert 1 + 2 - 3 * 4 % 5 == 1"
	got := Parse(input)
	want := "assert (((1 + 2) - ((3 * 4) % 5)) == 1)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestBinaryRelational(t *testing.T) {
	input := "assert 1 < 2 && 3 > 4 && 5 <= 6 && 7 >= 8 && 9 == 10 && 11 != 12"
	got := Parse(input)
	want := "assert ((((((1 < 2) && (3 > 4)) && (5 <= 6)) && (7 >= 8)) && (9 == 10)) && (11 != 12))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestSquareBracket(t *testing.T) {
	input := "assert a[42] == 1337 && b[1][2][3] != 4 && c[d[5]] < 6"
	got := Parse(input)
	want := "assert (((a[42] == 1337) && (b[1][2][3] != 4)) && (c[d[5]] < 6))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestDotNotation(t *testing.T) {
	input := "assert a.b == 42 && c.d.e.f == 1337"
	got := Parse(input)
	want := "assert ((a.b == 42) && (c.d.e.f == 1337))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestArrayLiteral(t *testing.T) {
	input := "assert a == [42]int{1,2,3} && b == [1337]bool{} && c == []*int{}"
	got := Parse(input)
	want := "assert (((a == [42]int{1, 2, 3}) && (b == [1337]bool{})) && (c == [](*int){}))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestStructLiteral(t *testing.T) {
	input := "assert a == mystruct{42} && b == mystruct{val: 42} && c == mystruct{a: 1, b: 2} && d == mystruct{}"
	got := Parse(input)
	want := "assert ((((a == mystruct{42}) && (b == mystruct{val:42})) && (c == mystruct{a:1, b:2})) && (d == mystruct{}))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPrecedenceLogical(t *testing.T) {
	input := "assert ! a && b || c"
	got := Parse(input)
	want := "assert ((!a && b) || c)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPrecedenceArithmetic(t *testing.T) {
	input := "assert a + b * c - d % e / f"
	got := Parse(input)
	want := "assert ((a + (b * c)) - ((d % e) / f))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPrecedenceMixed(t *testing.T) {
	input := "assert a * b == c && d + e % f < g == h || i"
	got := Parse(input)
	want := "assert ((((a * b) == c) && (((d + (e % f)) < g) == h)) || i)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestAssert(t *testing.T) {
	input := "assert foo == 42"
	got := Parse(input)
	want := "assert (foo == 42)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestAssume(t *testing.T) {
	input := "assume foo == 42"
	got := Parse(input)
	want := "assume (foo == 42)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPrecondition(t *testing.T) {
	input := "requires foo == 42"
	got := Parse(input)
	want := "requires (foo == 42)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPostcondition(t *testing.T) {
	input := "ensures foo == 42"
	got := Parse(input)
	want := "ensures (foo == 42)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestInvariant(t *testing.T) {
	input := "invariant foo == 42"
	got := Parse(input)
	want := "invariant (foo == 42)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestSkipWhitespace(t *testing.T) {
	input := "assert     a    < b+              	c"
	got := Parse(input)
	want := "assert (a < (b + c))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestSkipComments(t *testing.T) {
	input := "//@ assert a < /*@ b + c @*/"
	got := Parse(input)
	want := "assert (a < (b + c))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestMultilineComments(t *testing.T) {
	input := "requires a < b 	\n requires b && !c 	ensures a != 0"
	got := Parse(input)
	want := []string{"requires (a < b)", "requires (b && !c)", "ensures (a != 0)"}
	for i, node := range got {
		if node.String() != want[i] {
			t.Errorf("at position %d - got: %v, want: %s", i, got[i].String(), want[i])
		}
	}
}

func TestComplex1(t *testing.T) {
	input := "assert a == [3]int{mystruct{},[42]string{},[]int{},otherstruct{key:val,otherkey:otherval}}"
	got := Parse(input)
	want := "assert (a == [3]int{mystruct{}, [42]string{}, []int{}, otherstruct{key:val, otherkey:otherval}})"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestComplex2(t *testing.T) {
	input := "assert !(42 && !true == 13 + -c.d[3] || *b) >= foo[3]"
	got := Parse(input)
	want := "assert (!((42 && (!true == (13 + -c.d[3]))) || (*b)) >= foo[3])"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPurity(t *testing.T) {
	input := "pure"
	got := Parse(input)
	want := "pure"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUnlabelledOld(t *testing.T) {
	input := "assert old(a[42]) != a[42]"
	got := Parse(input)
	want := "assert (old(a[42]) != a[42])"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestLabelledOld(t *testing.T) {
	input := "assert old[theLabel](a[42]) != a[42]"
	got := Parse(input)
	want := "assert (old[theLabel](a[42]) != a[42])"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestLabel(t *testing.T) {
	input := "label:"
	got := Parse(input)
	want := "label:"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUniversalQuantifier_SingleVariable_Numeric(t *testing.T) {
	input := "requires forall x int, :: 41 <= x <= 43 ==> (x == 42)"
	got := Parse(input)
	want := "requires (forall x int :: 41 <= x <= 43 ==> (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUniversalQuantifier_SingleVariable_DataStructure_Key(t *testing.T) {
	input := "requires forall x int :: x in range y ==> x == 42"
	got := Parse(input)
	want := "requires (forall x int :: x in range y ==> (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUniversalQuantifier_SingleVariable_DataStructure_Value(t *testing.T) {
	input := "requires forall x int :: (_, x) in range y.bar ==> x == 42"
	got := Parse(input)
	want := "requires (forall x int :: (_, x) in range y.bar ==> (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUniversalQuantifier_SingleVariable_DataStructure_KeyAndValue(t *testing.T) {
	input := "requires forall x int, z int:: (z, x) in range y.bar ==> x == 42"
	got := Parse(input)
	want := "requires (forall x int, z int :: (z, x) in range y.bar ==> (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_SingleVariable_Numeric(t *testing.T) {
	input := "requires exists x int :: 41 < x < 43 && x == 42"
	got := Parse(input)
	want := "requires (exists x int :: 41 < x < 43 && (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_SingleVariable_DataStructure_Key(t *testing.T) {
	input := "requires exists x int :: x in range y && x == 42"
	got := Parse(input)
	want := "requires (exists x int :: x in range y && (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_SingleVariable_DataStructure_Value(t *testing.T) {
	input := "requires exists x int :: (_, x) in range y.bar && x == 42"
	got := Parse(input)
	want := "requires (exists x int :: (_, x) in range y.bar && (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_SingleVariable_DataStructure_Value_WithoutBrackets(t *testing.T) {
	input := "requires exists x int :: _, x in range y.bar && x == 42"
	got := Parse(input)
	want := "requires (exists x int :: (_, x) in range y.bar && (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_SingleVariable_DataStructure_KeyAndValue(t *testing.T) {
	input := "requires exists x int, z int:: (z, x) in range y.bar && x == 42"
	got := Parse(input)
	want := "requires (exists x int, z int :: (z, x) in range y.bar && (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_SingleVariable_DataStructure_KeyAndValue_WithoutBrackets(t *testing.T) {
	input := "requires exists x int, z int:: z, x in range y.bar && x == 42"
	got := Parse(input)
	want := "requires (exists x int, z int :: (z, x) in range y.bar && (x == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUniversalQuantifier_MultipleVariables_NumericAndDataStructure(t *testing.T) {
	input := "requires forall x int, y float, w, z foo :: (0 < x < 1337 && 0 < y < 10 && z in range map.bar) ==> x + y + w.bar + z.bar == 42"
	got := Parse(input)
	want := "requires (forall x int, y float, w foo, z foo :: ((0 < x < 1337 && 0 < y < 10) && z in range map.bar) ==> ((((x + y) + w.bar) + z.bar) == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_MultipleVariables(t *testing.T) {
	input := "requires exists x int, y float, w, z foo :: (0 < x < 1337 && 0 < y < 10 || z in range map.bar) && x + y + w.bar + z.bar == 42"
	got := Parse(input)
	want := "requires (exists x int, y float, w foo, z foo :: ((0 < x < 1337 && 0 < y < 10) || z in range map.bar) && ((((x + y) + w.bar) + z.bar) == 42))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_MultipleVariablesSameType(t *testing.T) {
	input := "requires exists a, b int :: 0 < a < c && d.bar <= b <= f[42] && (x || y || z && a + b == 42)"
	got := Parse(input)
	want := "requires (exists a int, b int :: (0 < a < c && d.bar <= b <= f[42]) && ((x || y) || (z && ((a + b) == 42))))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUniversalQuantifier_MultipleVariablesSameType(t *testing.T) {
	input := "requires forall a, b int :: 0 < a < c && d.bar <= b <= f[42] ==> (x || y || z && a + b == 42)"
	got := Parse(input)
	want := "requires (forall a int, b int :: (0 < a < c && d.bar <= b <= f[42]) ==> ((x || y) || (z && ((a + b) == 42))))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUniversalQuantifier_MultipleVariables_Boolean(t *testing.T) {
	input := "requires forall x, y, z bool, a, b int :: 0 < a < b && 0 < b < a ==>(x || y || z && a + b == 42)"
	got := Parse(input)
	want := "requires (forall x bool, y bool, z bool, a int, b int :: (0 < a < b && 0 < b < a) ==> ((x || y) || (z && ((a + b) == 42))))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestUniversalQuantifier_Boolean(t *testing.T) {
	input := "requires forall x, y, z bool :: (x || z && y)"
	got := Parse(input)
	want := "requires (forall x bool, y bool, z bool :: (x || (z && y)))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_Boolean(t *testing.T) {
	input := "requires exists x, y, z bool :: (x || z && y)"
	got := Parse(input)
	want := "requires (exists x bool, y bool, z bool :: (x || (z && y)))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestNestedQuantifiers_ForallAndExists(t *testing.T) {
	input := "requires forall x int :: x in range z ==> exists y float :: (_, y) in range w && x == y"
	got := Parse(input)
	want := "requires (forall x int :: x in range z ==> (exists y float :: (_, y) in range w && (x == y)))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestNestedQuantifiers_TwoForall(t *testing.T) {
	input := "requires forall x int :: x in range z ==> forall y float :: (_, y) in range w ==> x == y"
	got := Parse(input)
	want := "requires (forall x int :: x in range z ==> (forall y float :: (_, y) in range w ==> (x == y)))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestMultipleQuantifiers_ForallAndExists(t *testing.T) {
	input := "requires forall x int :: x in range z ==> x == 42 && exists y float :: (_, y) in range w && x == y"
	got := Parse(input)
	want := "requires ((forall x int :: x in range z ==> (x == 42)) && (exists y float :: (_, y) in range w && (x == y)))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestMultipleQuantifiers_TwoForall(t *testing.T) {
	input := "requires forall x int :: x in range z ==> x == 42 && forall y float :: (_, y) in range w ==> x == y"
	got := Parse(input)
	want := "requires ((forall x int :: x in range z ==> (x == 42)) && (forall y float :: (_, y) in range w ==> (x == y)))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExistentialQuantifier_LongConjunction(t *testing.T) {
	input := "requires exists x, y int :: x in range z && 0 < y < 1 && y < 1337 && x == 42 && exists y float :: (_, y) in range w && x == y"
	got := Parse(input)
	want := "requires ((exists x int, y int :: (x in range z && 0 < y < 1) && ((y < 1337) && (x == 42))) && (exists y float :: (_, y) in range w && (x == y)))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPanic(t *testing.T) {
	wantPanic := "Error parsing specification. Error displayed above."
	defer func() {
		if gotPanic := recover(); gotPanic != nil {
			if gotPanic.(string) != wantPanic {
				t.Errorf("got panic:\n %v want panic:\n %s", gotPanic.(string), wantPanic)
			}
		}
	}()
	input := `^#$%#%@#$humbug`
	Parse(input)
}

func TestAccessPermission_Single(t *testing.T) {
	input := "requires acc(x.val)"
	got := Parse(input)
	want := "requires acc(x.val)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestAccessPermission_Multi(t *testing.T) {
	input := "requires acc(x.val) && acc(y.z.val) && x.val == y.z.val && acc(&foo)"
	got := Parse(input)
	want := "requires ((acc(x.val) && acc(y.z.val)) && ((x.val == y.z.val) && acc(&foo)))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestFunctionCall_Parameters(t *testing.T) {
	input := "assert f(a, b, c) == a + b + c"
	got := Parse(input)
	want := "assert (f(a, b, c) == ((a + b) + c))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestFunctionCall_Empty(t *testing.T) {
	input := "assert foo() < a[42]"
	got := Parse(input)
	want := "assert (foo() < a[42])"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestFunctionCall_Complex(t *testing.T) {
	input := "assert x.f([1]int{1}, g(), a[42](1337)) <= h(c < d) + foo{bar: 2*2}.function()"
	got := Parse(input)
	want := "assert (x.f([1]int{1}, g(), a[42](1337)) <= (h((c < d)) + foo{bar:(2 * 2)}.function()))"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestShared_SingleVariable(t *testing.T) {
	input := "shared: a"
	got := Parse(input)
	want := "shared: a"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExclusive_SingleVariable(t *testing.T) {
	input := " exclusive :   a"
	got := Parse(input)
	want := "exclusive: a"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestShared_MultipleVariables(t *testing.T) {
	input := "shared : a, b,  c, d"
	got := Parse(input)
	want := "shared: a, b, c, d"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestExclusive_MultipleVariables(t *testing.T) {
	input := "exclusive: a, b, c, d"
	got := Parse(input)
	want := "exclusive: a, b, c, d"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPredicate_SingleParameter(t *testing.T) {
	input := "predicate P(x int) { x > 0 }"
	got := Parse(input)
	want := "predicate P(x int) { (x > 0) }"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPredicate_NoParameter(t *testing.T) {
	input := "predicate P() { 42 > 0 }"
	got := Parse(input)
	want := "predicate P() { (42 > 0) }"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPredicate_MultipleParameter(t *testing.T) {
	input := "predicate P(x, y int, b bool) { x + y > 0 && b }"
	got := Parse(input)
	want := "predicate P(x int, y int, b bool) { (((x + y) > 0) && b) }"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestImplication(t *testing.T) {
	input := "assert a ==> b"
	got := Parse(input)
	want := "assert (a ==> b)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPredicateImplication(t *testing.T) {
	input := "predicate P(x int) { x != 42 } assert x == 42 ==> !P(x)"
	got := Parse(input)
	want := []string{"predicate P(x int) { (x != 42) }", "assert ((x == 42) ==> !P(x))"}
	for i, node := range got {
		if node.String() != want[i] {
			t.Errorf("at position %d - got: %v, want: %s", i, got[i].String(), want[i])
		}
	}
}

func TestTernaryOperator(t *testing.T) {
	input := "assert a ? b : c"
	got := Parse(input)
	want := "assert (a ? b : c)"
	if len(got) != 1 || got[0].String() != want {
		t.Errorf("got: %v, want: %s", got, want)
	}
}

func TestPredicateTernaryOperator(t *testing.T) {
	input := "predicate Positive(x int) { x > 0 } predicate Negative(x int) { x < 0 } assert (x > 0 && x != 0) ? Positive(x) : Negative(x)"
	got := Parse(input)
	want := []string{"predicate Positive(x int) { (x > 0) }", "predicate Negative(x int) { (x < 0) }", "assert (((x > 0) && (x != 0)) ? Positive(x) : Negative(x))"}
	for i, node := range got {
		if node.String() != want[i] {
			t.Errorf("at position %d - got: %v, want: %s", i, got[i].String(), want[i])
		}
	}
}
