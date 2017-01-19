package expreduce

import "math/big"

func compareStrings(a string, b string) int64 {
	minchars := Min(len(a), len(b))
	for i := 0; i < minchars; i++ {
		if a[i] > b[i] {
			return -1
		} else if a[i] < b[i] {
			return 1
		}
	}
	if len(a) > len(b) {
		return -1
	} else if len(a) < len(b) {
		return 1
	}
	return 0
}

func ExOrder(a Ex, b Ex) int64 {
	// Support Flt, Integer, Rational, Expression, Symbol

	aAsSymbol, aIsSymbol := a.(*Symbol)
	bAsSymbol, bIsSymbol := b.(*Symbol)
	aAsString, aIsString := a.(*String)
	bAsString, bIsString := b.(*String)
	aAsExp, aIsExp := a.(*Expression)
	bAsExp, bIsExp := b.(*Expression)

	aAsFlt, aIsFlt := a.(*Flt)
	bAsFlt, bIsFlt := b.(*Flt)
	aAsInteger, aIsInteger := a.(*Integer)
	bAsInteger, bIsInteger := b.(*Integer)
	aAsRational, aIsRational := a.(*Rational)
	bAsRational, bIsRational := b.(*Rational)

	// Handle number comparisons
	// Merge Integer and Rational into Flt
	// TODO: possible precision, round off issue here.
	if aIsInteger {
		aAsFlt, aIsFlt = IntegerToFlt(aAsInteger)
	}
	if bIsInteger {
		bAsFlt, bIsFlt = IntegerToFlt(bAsInteger)
	}
	if aIsRational {
		aAsFlt, aIsFlt = RationalToFlt(aAsRational)
	}
	if bIsRational {
		bAsFlt, bIsFlt = RationalToFlt(bAsRational)
	}

	if aIsFlt && bIsFlt {
		initCmp := int64(bAsFlt.Val.Cmp(aAsFlt.Val))
		if initCmp == 0 && (aIsInteger && !bIsInteger) {
			return 1
		}
		if initCmp == 0 && (!aIsInteger && bIsInteger) {
			return -1
		}
		return initCmp
	}

	// Handle expression comparisons
	if aIsExp && bIsExp {
		for i := 0; i < Min(len(aAsExp.Parts), len(bAsExp.Parts)); i++ {
			o := ExOrder(aAsExp.Parts[i], bAsExp.Parts[i])
			if o != 0 {
				return o
			}
		}
		if len(aAsExp.Parts) < len(bAsExp.Parts) {
			return 1
		} else if len(aAsExp.Parts) > len(bAsExp.Parts) {
			return -1
		} else {
			return 0
		}
	}

	// Symbol and string comparisons work in a similar way:
	if aIsSymbol && bIsSymbol {
		return compareStrings(aAsSymbol.Name, bAsSymbol.Name)
	}
	if aIsString && bIsString {
		return compareStrings(aAsString.Val, bAsString.Val)
	}

	// The remaining type combinations simply return -1 or 1:
	// Precedence order: numbers (flt), strings, symbols, expressions
	if aIsFlt && bIsString {
		return 1
	}
	if aIsFlt && bIsSymbol {
		return 1
	}
	if aIsFlt && bIsExp {
		return 1
	}

	if aIsString && bIsFlt {
		return -1
	}
	if aIsString && bIsSymbol {
		return 1
	}
	if aIsString && bIsExp {
		return 1
	}

	if aIsSymbol && bIsFlt {
		return -1
	}
	if aIsSymbol && bIsString {
		return -1
	}
	if aIsSymbol && bIsExp {
		return 1
	}

	if aIsExp && bIsFlt {
		return -1
	}
	if aIsExp && bIsString {
		return -1
	}
	if aIsExp && bIsSymbol {
		return -1
	}

	return -2
}

func GetOrderDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "Order",
		Usage: "`Order[e1, e2]` returns 1 if `e1` should come before `e2` in canonical ordering, -1 if it should come after, and 0 if the two expressions are equal.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			toreturn := ExOrder(this.Parts[1], this.Parts[2])
			return &Integer{big.NewInt(toreturn)}
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Find the relative order of symbols:"},
			&SameTest{"1", "Order[a, b]"},
			&SameTest{"-1", "Order[b, a]"},
			&SameTest{"1", "Order[a, aa]"},
			&TestComment{"Find the relative order of numbers:"},
			&SameTest{"-1", "Order[2, 1.]"},
			&SameTest{"1", "Order[1, 2]"},
			&SameTest{"0", "Order[1, 1]"},
			&TestComment{"Find the relative order of strings:"},
			&SameTest{"1", "Order[\"a\", \"b\"]"},
			&SameTest{"-1", "Order[\"b\", \"a\"]"},
			&TestComment{"Find the relative order of heterogenous types:"},
			&SameTest{"-1", "Order[ab, 1]"},
			&SameTest{"1", "Order[1, ab]"},
			&SameTest{"-1", "Order[y[a], x]"},
			&TestComment{"Find the relative order of rationals:"},
			&SameTest{"1", "Order[Rational[-5, 3], Rational[-4, 6]]"},
			&SameTest{"-1", "Order[Rational[4, 6], .6]"},
			&SameTest{"1", "Order[.6, Rational[4, 6]]"},
			&SameTest{"1", "Order[Rational[4, 6], .7]"},
			&TestComment{"Find the relative order of expressions:"},
			&SameTest{"0", "Order[bar[x, y], bar[x, y]]"},
			&SameTest{"1", "Order[fizz[bar[x, y]], fizz[bar[x, y, a]]]"},
		},
		Tests: []TestInstruction{
			// Symbol ordering
			&SameTest{"0", "Order[a, a]"},
			&SameTest{"1", "Order[a, b]"},
			&SameTest{"-1", "Order[b, a]"},
			&SameTest{"1", "Order[a, aa]"},
			&SameTest{"1", "Order[aa, aab]"},
			&SameTest{"-1", "Order[aab, aa]"},
			&SameTest{"-1", "Order[aa, a]"},
			&SameTest{"-1", "Order[ab, aa]"},

			// Number ordering
			&SameTest{"-1", "Order[2, 1.]"},
			&SameTest{"1", "Order[1, 2]"},
			&SameTest{"0", "Order[1, 1]"},
			&SameTest{"0", "Order[1., 1.]"},
			&SameTest{"1", "Order[1, 1.]"},
			&SameTest{"-1", "Order[1., 1]"},

			// Symbols vs numbers
			&SameTest{"-1", "Order[ab, 1]"},
			&SameTest{"1", "Order[1, ab]"},

			// Sort expressions
			&SameTest{"-1", "Order[foo[x, y], bar[x, y]]"},
			&SameTest{"1", "Order[bar[x, y], foo[x, y]]"},
			&SameTest{"0", "Order[bar[x, y], bar[x, y]]"},
			&SameTest{"1", "Order[bar[x, y], bar[x, y, z]]"},
			&SameTest{"1", "Order[bar[x, y], bar[x, y, a]]"},
			&SameTest{"1", "Order[bar[x, y], bar[y, z]]"},
			&SameTest{"-1", "Order[bar[x, y], bar[w, x]]"},
			&SameTest{"-1", "Order[fizz[foo[x, y]], fizz[bar[x, y]]]"},
			&SameTest{"1", "Order[fizz[bar[x, y]], fizz[foo[x, y]]]"},
			&SameTest{"0", "Order[fizz[bar[x, y]], fizz[bar[x, y]]]"},
			&SameTest{"1", "Order[fizz[bar[x, y]], fizz[bar[x, y, z]]]"},
			&SameTest{"1", "Order[fizz[bar[x, y]], fizz[bar[x, y, a]]]"},
			&SameTest{"1", "Order[fizz[bar[x, y]], fizz[bar[y, z]]]"},
			&SameTest{"-1", "Order[fizz[bar[x, y]], fizz[bar[w, x]]]"},
			&SameTest{"-1", "Order[fizz[foo[x, y]], fizz[bar[a, y]]]"},
			&SameTest{"-1", "Order[fizz[foo[x, y]], fizz[bar[z, y]]]"},

			&SameTest{"1", "Order[1, a[b]]"},
			&SameTest{"1", "Order[1., a[b]]"},
			&SameTest{"-1", "Order[a[b], 1]"},
			&SameTest{"-1", "Order[a[b], 1.]"},
			&SameTest{"1", "Order[x, y[a]]"},
			&SameTest{"1", "Order[x, w[a]]"},
			&SameTest{"-1", "Order[w[a], x]"},
			&SameTest{"-1", "Order[y[a], x]"},
			&SameTest{"-1", "Order[y[], x]"},
			&SameTest{"-1", "Order[y, x]"},
			&SameTest{"-1", "Order[w[], x]"},
			&SameTest{"1", "Order[w, x]"},

			//&SameTest{"{-1, -1., -0.1, 0, 0.1, 0.11, 2, 2, 2., 0.5^x, 2^x, x, 2*x, x^2, x^x, x^(2*x), X, xX, xxx, 2*y}", "Sort[{-1, -1., 0.1, 0.11, 2., -.1, 2, 0, 2, 2*x, 2*y, x, xxx, 2^x, x^2, x^x, x^(2*x), X, xX, .5^x}]"},
			//&SameTest{"{x, 2*x, 2*x^2, y, 2*y, 2*y^2}", "Sort[{x, 2*x, y, 2*y, 2*y^2, 2*x^2}]"},

			// Test Rational ordering
			&SameTest{"0", "Order[Rational[4, 6], Rational[2, 3]]"},
			&SameTest{"1", "Order[Rational[4, 6], Rational[5, 3]]"},
			&SameTest{"-1", "Order[Rational[5, 3], Rational[4, 6]]"},
			&SameTest{"1", "Order[Rational[-5, 3], Rational[-4, 6]]"},
			&SameTest{"-1", "Order[Rational[4, 6], .6]"},
			&SameTest{"1", "Order[.6, Rational[4, 6]]"},
			&SameTest{"1", "Order[Rational[4, 6], .7]"},
			&SameTest{"-1", "Order[.7, Rational[4, 6]]"},
			&SameTest{"-1", "Order[Rational[4, 6], 0]"},
			&SameTest{"1", "Order[Rational[4, 6], 1]"},
			&SameTest{"1", "Order[0, Rational[4, 6]]"},
			&SameTest{"-1", "Order[1, Rational[4, 6]]"},
			&SameTest{"1", "Order[Rational[4, 6], a]"},
			&SameTest{"-1", "Order[a, Rational[4, 6]]"},

			// Test String ordering
			&SameTest{"-1", "Order[\"a\", 5]"},
			&SameTest{"-1", "Order[\"a\", 5.5]"},
			&SameTest{"-1", "Order[\"a\", 5/2]"},
			&SameTest{"1", "Order[\"a\", x]"},
			&SameTest{"1", "Order[\"a\", x^2]"},
			&SameTest{"1", "Order[\"a\", x^2]"},
			&SameTest{"-1", "Order[\"b\", \"a\"]"},
			&SameTest{"1", "Order[\"a\", \"b\"]"},
			&SameTest{"1", "Order[\"a\", \"aa\"]"},
		},
	})
	return
}
