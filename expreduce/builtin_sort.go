package expreduce

import (
	"math/big"
	"sort"
)

func GetSortDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "Sort",
		Usage: "`Sort[list]` sorts the elements in list according to `Order`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			exp, ok := this.Parts[1].(*Expression)
			if ok {
				sort.Sort(exp)
				return exp
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Sort a list of numbers:"},
			&SameTest{"{-5.1, 2, 3.2, 6}", "Sort[{6, 2, 3.2, -5.1}]"},
			&TestComment{"Sort a list of strings:"},
			&SameTest{"{\"a\", \"aa\", \"hello\", \"zzz\"}", "Sort[{\"hello\", \"a\", \"aa\", \"zzz\"}]"},
			&TestComment{"Sort a list of symbols:"},
			&SameTest{"{a, b, c, d}", "Sort[{d, a, b, c}]"},
			&TestComment{"Sort a list of heterogenous expressions:"},
			&SameTest{"{5, h, bar[a^x], foo[y, 2]}", "Sort[{5, h, foo[y, 2], bar[a^x]}]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"The object to sort need not be a list:"},
			&SameTest{"foo[a, b, c, d]", "Sort[foo[d, a, b, c]]"},
		},
	})
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

			// Test polynomial ordering
			&SameTest{"-1", "Order[x^3,4x^2]"},
			&SameTest{"-1", "Order[x^3,4x^2]"},
			&SameTest{"1", "Order[1,4x^2]"},
			&SameTest{"1", "Order[1,4*Sin[x]^2]"},
			&SameTest{"-1", "Order[5x^2,4x^2]"},
			&SameTest{"-1", "Order[4x^3,4x^2]"},
			&SameTest{"1", "Order[x^2,4x^2]"},
			&SameTest{"1", "Order[x^2,foo[x]]"},
			&SameTest{"1", "Order[x^2,x*y]"},
			&SameTest{"-1", "Order[3x^3,4x^2]"},
		},
		KnownFailures: []TestInstruction{
			&SameTest{"{-1, -1., -0.1, 0, 0.1, 0.11, 2, 2, 2., 0.5^x, 2^x, x, 2*x, x^2, x^x, x^(2*x), X, xX, xxx, 2*y}", "Sort[{-1, -1., 0.1, 0.11, 2., -.1, 2, 0, 2, 2*x, 2*y, x, xxx, 2^x, x^2, x^x, x^(2*x), X, xX, .5^x}]"},
			&SameTest{"{x, 2*x, 2*x^2, y, 2*y, 2*y^2}", "Sort[{x, 2*x, y, 2*y, 2*y^2, 2*x^2}]"},

			&SameTest{"1", "Order[x^2*y,x*y^2]"},
			&SameTest{"1", "Order[x^4*y^2,x^2*y^4]"},
			&SameTest{"1", "Order[x^2*y,2*x*y^2]"},
		},
	})
	/*defs = append(defs, Definition{
		// Credit for this function goes to the Mathics contributors.
		Name:  "PatternsOrderedQ",
		Usage: "`PatternsOrderedQ[e1, e2]` returns True if `e1` should come before `e2` in patterns ordering.",
		legacyEvalFn: doubleParamQLogEval(patternsOrderedQ),
		SimpleExamples: []TestInstruction{
			&TestComment{"Find the relative order of patterns:"},
			&SameTest{"False", "PatternsOrderedQ[x__, x_]"},
			&SameTest{"True", "PatternsOrderedQ[x_, x__]"},
			&SameTest{"True", "PatternsOrderedQ[b, a]"},
		},
	})*/
	return
}
