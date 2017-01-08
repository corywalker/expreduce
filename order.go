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
	// Support Flt, Integer, Expression, Symbol
	// Merge Integer into Flt
	// Need to support the following combinations
	// ff,fs,fe,sf,ss,se,ef,es,ee

	aAsSymbol, aIsSymbol := a.(*Symbol)
	bAsSymbol, bIsSymbol := b.(*Symbol)

	aAsFlt, aIsFlt := a.(*Flt)
	bAsFlt, bIsFlt := b.(*Flt)
	aAsInteger, aIsInteger := a.(*Integer)
	bAsInteger, bIsInteger := b.(*Integer)
	if aIsInteger {
		aAsFlt, aIsFlt = IntegerToFlt(aAsInteger)
	}
	if bIsInteger {
		bAsFlt, bIsFlt = IntegerToFlt(bAsInteger)
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

	if aIsFlt && bIsSymbol {
		return 1
	} else if aIsSymbol && bIsFlt {
		return -1
	}

	if aIsSymbol && bIsSymbol {
		return compareStrings(aAsSymbol.Name, bAsSymbol.Name)
	}

	aAsExp, aIsExp := a.(*Expression)
	bAsExp, bIsExp := b.(*Expression)
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

	if aIsFlt && bIsExp {
		return 1
	} else if aIsExp && bIsFlt {
		return -1
	}
	if aIsSymbol && bIsExp {
		return 1
	} else if aIsExp && bIsSymbol {
		return -1
	}

	// Do not support strings. Any comparison with these will go here.
	return -2
}

func GetOrderDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "Order",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			toreturn := ExOrder(this.Parts[1], this.Parts[2])
			return &Integer{big.NewInt(toreturn)}
		},
		tests: []TestInstruction{
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
		},
	})
	return
}
