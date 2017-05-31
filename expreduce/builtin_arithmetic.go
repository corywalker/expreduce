package expreduce

import "math/big"

func ExArrayContainsFloat(a []Ex) bool {
	res := false
	for _, e := range a {
		_, isfloat := e.(*Flt)
		res = res || isfloat
	}
	return res
}

func RationalAssertion(num Ex, den Ex) (r *Rational, isR bool) {
	numInt, numIsInt := num.(*Integer)
	denPow, denIsPow := HeadAssertion(den, "Power")
	if !numIsInt || !denIsPow {
		return nil, false
	}
	powInt, powIsInt := denPow.Parts[2].(*Integer)
	if !powIsInt {
		return nil, false
	}
	if powInt.Val.Cmp(big.NewInt(-1)) != 0 {
		return nil, false
	}
	denInt, denIsInt := denPow.Parts[1].(*Integer)
	if !denIsInt {
		return nil, false
	}
	return &Rational{numInt.Val, denInt.Val}, true
}

func getArithmeticDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "Plus",
		Usage:      "`(e1 + e2 + ...)` computes the sum of all expressions in the function.",
		Attributes: []string{"Flat", "Listable", "NumericFunction", "OneIdentity", "Orderless"},
		Rules: []Rule{
			{"Plus[a_, -a_, rest___]", "Plus[rest]"},
			{"Plus[c1_Integer*a__, c2_Integer*a__, rest___]", "((c1+c2)*a + rest)"},
			{"Plus[c1_Rational*a__, c2_Rational*a__, rest___]", "((c1+c2)*a + rest)"},
			// For some reason, this messes up the Infinity - Infinity rule
			{"Plus[c1_Integer*a_, a_, rest___]", "(c1+1)*a+rest"},
			{"Plus[a_, a_, rest___]", "2*a + rest"},
			//{"Plus[Repeated[a_, {2}], rest___]", "2*a + rest"},
			////"((c1_Integer*a_) + a_)": "(c1+1)*a",
			{"Plus[c1_Real*a_, c2_Integer*a_, rest___]", "(c1+c2)*a + rest"},
			// I have a feeling that these can be combined into a more general
			// definition. TODO
			{"Plus[c_Real*a_, a_, rest___]", "(c+1)*a + rest"},
		},
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfix(this.Parts[1:], " + ", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// Calls without argument receive identity values
			if len(this.Parts) == 1 {
				return &Integer{big.NewInt(0)}
			}

			addends := this.Parts[1:len(this.Parts)]
			// If this expression contains any floats, convert everything possible to
			// a float
			if ExArrayContainsFloat(addends) {
				for i, e := range addends {
					subint, isint := e.(*Integer)
					subrat, israt := e.(*Rational)
					if isint {
						newfloat := big.NewFloat(0)
						newfloat.SetInt(subint.Val)
						addends[i] = &Flt{newfloat}
					} else if israt {
						num := big.NewFloat(0)
						den := big.NewFloat(0)
						newquo := big.NewFloat(0)
						num.SetInt(subrat.Num)
						den.SetInt(subrat.Den)
						newquo.Quo(num, den)
						addends[i] = &Flt{newquo}
					}
				}
			}

			// Accumulate floating point values towards the end of the expression
			var lastf *Flt = nil
			for _, e := range addends {
				f, ok := e.(*Flt)
				if ok {
					if lastf != nil {
						f.Val.Add(f.Val, lastf.Val)
						lastf.Val = big.NewFloat(0)
					}
					lastf = f
				}
			}

			if len(addends) == 1 {
				f, fOk := addends[0].(*Flt)
				if fOk {
					if f.Val.Cmp(big.NewFloat(0)) == 0 {
						return f
					}
				}
				i, iOk := addends[0].(*Integer)
				if iOk {
					if i.Val.Cmp(big.NewInt(0)) == 0 {
						return i
					}
				}
			}

			// Remove zero Floats
			for i := len(addends) - 1; i >= 0; i-- {
				f, ok := addends[i].(*Flt)
				if ok && f.Val.Cmp(big.NewFloat(0)) == 0 && len(addends) > 1 {
					addends[i] = addends[len(addends)-1]
					addends[len(addends)-1] = nil
					addends = addends[:len(addends)-1]
				}
			}

			// Accumulate integer values towards the end of the expression
			var lasti *Integer = nil
			for _, e := range addends {
				i, ok := e.(*Integer)
				if ok {
					if lasti != nil {
						i.Val.Add(i.Val, lasti.Val)
						lasti.Val = big.NewInt(0)
					}
					lasti = i
				}
			}

			// Accumulate rational values towards the end of the expression
			var lastr *Rational = nil
			for _, e := range addends {
				therat, ok := e.(*Rational)
				if ok {
					if lastr != nil {
						tmp := big.NewInt(0)
						// lastrNum/lastrDen + theratNum/theratDen // Together
						tmp.Mul(therat.Den, lastr.Num)
						therat.Den.Mul(therat.Den, lastr.Den)
						therat.Num.Mul(therat.Num, lastr.Den)
						therat.Num.Add(therat.Num, tmp)
						lastr.Num = big.NewInt(0)
						lastr.Den = big.NewInt(1)
					}
					lastr = therat
				}
			}

			// If there is one Integer and one Rational left, merge the Integer into
			// the Rational
			if lasti != nil && lastr != nil {
				lasti.Val.Mul(lasti.Val, lastr.Den)
				lastr.Num.Add(lastr.Num, lasti.Val)
				lasti.Val = big.NewInt(0)
			}

			// Remove zero Integers and Rationals
			for i := len(addends) - 1; i >= 0; i-- {
				toRemove := false
				theint, isInt := addends[i].(*Integer)
				if isInt {
					toRemove = theint.Val.Cmp(big.NewInt(0)) == 0
				}
				therat, isRat := addends[i].(*Rational)
				if isRat {
					toRemove = therat.Num.Cmp(big.NewInt(0)) == 0 && therat.Den.Cmp(big.NewInt(1)) == 0
				}
				if toRemove && len(addends) > 1 {
					addends[i] = addends[len(addends)-1]
					addends[len(addends)-1] = nil
					addends = addends[:len(addends)-1]
				}
			}

			// If one expression remains, replace this Plus with the expression
			if len(addends) == 1 {
				return addends[0]
			}

			this.Parts = this.Parts[0:1]
			this.Parts = append(this.Parts, addends...)
			return this
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"2", "1 + 1"},
			&TestComment{"If Reals are present, other Integers are demoted to Reals:"},
			&SameTest{"0.", "(5.2 - .2) - 5"},
			&TestComment{"Plus automatically combines like terms:"},
			&SameTest{"a+6*b^2", "a + b^2 + 5*b^2"},
			&SameTest{"((5 * c^a) + (3 * d))", "(a+b)-(a+b)+c-c+2*c^a+2*d+5*d+d-5*d+3*c^a"},
			&SameTest{"-3 a b c d e f", "4*a*b*c*d*e*f + -7*a*b*c*d*e*f"},
		},
		Tests: []TestInstruction{
			// Test automatic expansion
			&StringTest{"(a + b)", "1*(a + b)"},
			&StringTest{"(1. * (a + b))", "1.*(a + b)"},
			&StringTest{"(2. * (a + b))", "2.*(a + b)"},
			&StringTest{"(a + b)", "(a + b)/1"},
			&StringTest{"(1. * (a + b))", "(a + b)/1."},
			&StringTest{"(2 * (a + b))", "2*(a + b)"},
			&StringTest{"(a * (b + c))", "a*(b + c)"},
			&StringTest{"((-1 * a) + (-1 * b))", "-1*(a + b)"},
			&StringTest{"((-1 * a) + (-1 * b))", "-(a + b)"},
			&StringTest{"(-1. * (a + b))", "-1.*(a + b)"},
			&StringTest{"((-1 * a) + (-1 * b))", "(a + b)/-1"},
			&StringTest{"(-1. * (a + b))", "(a + b)/-1."},

			// Test that we do not delete all the addends
			&SameTest{"0.", "(5.2 - .2) - 5"},
			&SameTest{"0", "0 + 0"},

			// Test empty Plus expressions
			&SameTest{"0", "Plus[]"},

			// Test proper accumulation of Rationals
			&StringTest{"(47/6 + sym)", "Rational[5, 2] + Rational[7, 3] + 3 + sym"},
			&StringTest{"(17/6 + sym)", "Rational[5, -2] + Rational[7, 3] + 3 + sym"},
			&StringTest{"(-19/6 + sym)", "Rational[5, -2] + Rational[7, 3] - 3 + sym"},
			&StringTest{"(-47/6 + sym)", "Rational[5, -2] + Rational[-7, 3] - 3 + sym"},

			// Test combining monomials of degree 1
			&SameTest{"a+7*b", "a + 2*b + 5*b"},

			// Test a more general version
			&SameTest{"a+7*b", "a + 2*b + 5*b"},
			&DiffTest{"a+7*b", "a + 2*b^2 + 5*b^2"},
			&SameTest{"a+7*b^2", "a + 2*b^2 + 5*b^2"},
			&SameTest{"a+3*b^2", "a - 2*b^2 + 5*b^2"},

			// Test using terms without a coefficient
			&SameTest{"a+6*b^2", "a + b^2 + 5*b^2"},

			// Test additive identity
			&SameTest{"a", "a+0"},
			&SameTest{"a+b", "(a+b)+0"},

			// Test additive inverse
			&SameTest{"0", "a-a"},
			&SameTest{"0", "-a + a"},
			&SameTest{"0", "(a+b)-(a+b)"},
			&SameTest{"0", "-(a+b)+(a+b)"},
			&SameTest{"0", "(a+b)-(a+b)"},
			&SameTest{"0", "-(a+b)+(a+b)"},

			// Test basic simplifications
			&SameTest{"d", "(a+b)-(a+b)+c-c+d"},
			&SameTest{"((5 * c^a) + (3 * d))", "(a+b)-(a+b)+c-c+2*c^a+2*d+5*d+d-5*d+3*c^a"},
			&SameTest{"87.5 + 3 * x", "((x + 80. + 3. + x) + 2. + x + 2.5)"},
			&SameTest{"87.5 + (7. * x)", "((x + 80. + 3. + x) + 2. + (x * 2. * 2.) + (0. * 3. * x) + x + 2.5)"},

			// More complicated term combining
			&SameTest{"-3 * m - 10 * n", "-9 * n - n - 3 * m"},
			&SameTest{"50*a", "a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a"},

			&SameTest{"7*a * b - 2*a * c", "3*a*b - 2*a*c + 4*a*b"},
			&SameTest{"-3*a - 2*b + 3*a*b", "2*a - 4*b + 3*a*b - 5*a + 2*b"},
			&SameTest{"7*x - 11*y + x*y", "8*x - 9*y - 3*x*y - 2*y - x + 4*x*y"},
			&SameTest{"-3*a*b*c*d*e*f", "4*a*b*c*d*e*f + -7*a*b*c*d*e*f"},
			&SameTest{"-3*a*b*c*d*e*f", "a*b*c*4*d*e*f + -a*b*c*d*e*f*7"},
			&SameTest{"-3*a*b*c*d*e*f", "a*b*2*c*2*d*e*f + -a*b*c*d*e*f*7"},
			&SameTest{"2 r + 2 t", "2 r - 3 s - t + 3 t + 3 s"},
			&SameTest{"3 (x - 2 y) - 4 x y + 2 (-1 + x y)", "2 (x*y - 1) + 3 (x - 2 y) - 4 x*y"},
			&SameTest{"-4 s + 4 r s - 3 (1 + r s)", "4 r*s - 2 s - 3 (r*s + 1) - 2 s"},
			&SameTest{"7 y - z + 3 y z", "8 y - 2 z - (y - z) + 3 y*z"},
		},
	})
	defs = append(defs, Definition{
		Name: "Sum",
		Usage: "`Sum[expr, n]` returns the sum of `n` copies of `expr`.\n\n" +
			"`Sum[expr, {sym, n}]` returns the sum of `expr` evaluated with `sym` = 1 to `n`.\n\n" +
			"`Sum[expr, {sym, m, n}]` returns the sum of `expr` evaluated with `sym` = `m` to `n`.",
		Attributes: []string{"HoldAll", "ReadProtected"},
		Rules: []Rule{
			{"Sum[i_Symbol, {i_Symbol, 0, n_Integer}]", "1/2*n*(1 + n)"},
			{"Sum[i_Symbol, {i_Symbol, 1, n_Integer}]", "1/2*n*(1 + n)"},
			{"Sum[i_Symbol, {i_Symbol, n_Integer}]", "1/2*n*(1 + n)"},
			{"Sum[i_Symbol, {i_Symbol, 0, n_Symbol}]", "1/2*n*(1 + n)"},
			{"Sum[i_Symbol, {i_Symbol, 1, n_Symbol}]", "1/2*n*(1 + n)"},
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			return this.evalIterationFunc(es, &Integer{big.NewInt(0)}, "Plus")
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"45", "Sum[i, {i, 5, 10}]"},
			&SameTest{"55", "Sum[i, {i, 1, 10}]"},
			&SameTest{"55", "Sum[i, {i, 0, 10}]"},
			&SameTest{"450015000", "Sum[i, {i, 1, 30000}]"},
			&SameTest{"450015000", "Sum[i, {i, 0, 30000}]"},
			&SameTest{"1/2*n*(1 + n)", "Sum[i, {i, 0, n}]"},
			&SameTest{"1/2*n*(1 + n)", "Sum[i, {i, 1, n}]"},
			&SameTest{"30", "Sum[a + b, {a, 0, 2}, {b, 0, 3}]"},
			&SameTest{"b+c+d+e", "Sum[a, {a, {b, c, d, e}}]"},
			&SameTest{"b g + c g + d g + e g + b h + c h + d h + e h", "Sum[a*f, {a, {b, c, d, e}}, {f, {g, h}}]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Times",
		Usage:      "`(e1 * e2 * ...)` computes the product of all expressions in the function.",
		Attributes: []string{"Flat", "Listable", "NumericFunction", "OneIdentity", "Orderless"},
		Rules: []Rule{
			{"Times[a_, a_, rest___]", "a^2 * rest"},
			{"Times[a_^n_, a_, rest___]", "a^(n+1) * rest"},
			{"Times[a_^n_, a_^m_, rest___]", "a^(n+m) * rest"},
			{"Times[den_Integer^-1, num_Integer, rest___]", "Rational[num,den] * rest"},
			{"Times[a_, a_^-1, rest___]", "rest"},
			{"Times[a_^b_, a_^-1, rest___]", "a^(b-1) * rest"},
			//"Times[a_^b_, Power[a_^c_, -1], rest___]": "a^(b-c) * rest",
			//"Times[a_^b_, Power[a_, Power[c_, -1]], rest___]": "a^(b-c) * rest",
			{"(1/Infinity)", "0"},
			{"Times[ComplexInfinity, (_?(Function[AtomQ[#] == False]))|(_Symbol), rest___]", "ComplexInfinity * rest"},
		},
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfix(this.Parts[1:], " * ", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// Calls without argument receive identity values
			if len(this.Parts) == 1 {
				return &Integer{big.NewInt(1)}
			}

			multiplicands := this.Parts[1:len(this.Parts)]
			// If this expression contains any floats, convert everything possible to
			// a float
			if ExArrayContainsFloat(multiplicands) {
				for i, e := range multiplicands {
					subint, isint := e.(*Integer)
					subrat, israt := e.(*Rational)
					if isint {
						newfloat := big.NewFloat(0)
						newfloat.SetInt(subint.Val)
						multiplicands[i] = &Flt{newfloat}
					} else if israt {
						num := big.NewFloat(0)
						den := big.NewFloat(0)
						newquo := big.NewFloat(0)
						num.SetInt(subrat.Num)
						den.SetInt(subrat.Den)
						newquo.Quo(num, den)
						multiplicands[i] = &Flt{newquo}
					}
				}
			}

			// If there is a zero in the expression, return zero, except under
			// special circumstances.
			containsInfinity := MemberQ(multiplicands, NewExpression([]Ex{
				&Symbol{"Alternatives"},
				&Symbol{"Infinity"},
				&Symbol{"ComplexInfinity"},
			}),

				&es.defined, &es.CASLogger)
			for _, e := range multiplicands {
				float, isFlt := e.(*Flt)
				if isFlt {
					if float.Val.Cmp(big.NewFloat(0)) == 0 {
						if containsInfinity {
							return &Symbol{"Indeterminate"}
						}
						return &Flt{big.NewFloat(0)}
					}
				}
				integer, isInteger := e.(*Integer)
				if isInteger {
					if integer.Val.Cmp(big.NewInt(0)) == 0 {
						if containsInfinity {
							return &Symbol{"Indeterminate"}
						}
						return &Integer{big.NewInt(0)}
					}
				}
			}

			// Geometrically accumulate floating point values towards the end of the expression
			//es.Debugf("Before accumulating floats: %s", m)
			origLen := len(multiplicands)
			offset := 0
			var lastf *Flt = nil
			var lastfj int = 0
			for i := 0; i < origLen; i++ {
				j := i - offset
				e := multiplicands[j]
				f, ok := e.(*Flt)
				if ok {
					if lastf != nil {
						es.Debugf("Encountered float. i=%d, j=%d, lastf=%s, lastfj=%d", i, j, lastf, lastfj)
						f.Val.Mul(f.Val, lastf.Val)
						//lastf.Val = big.NewFloat(1)
						multiplicands = append(multiplicands[:lastfj], multiplicands[lastfj+1:]...)
						offset++
						es.Debugf("After deleting: %s", this)
					}
					lastf = f
					lastfj = i - offset
				}
			}
			//es.Debugf(es.Pre() +"After accumulating floats: %s", m)

			if len(multiplicands) == 1 {
				f, fOk := multiplicands[0].(*Flt)
				if fOk {
					if f.Val.Cmp(big.NewFloat(0)) == 1 {
						return f
					}
				}
				i, iOk := multiplicands[0].(*Integer)
				if iOk {
					if i.Val.Cmp(big.NewInt(0)) == 1 {
						return i
					}
				}
			}

			// Remove one Floats
			/*
				for i := len(multiplicands) - 1; i >= 0; i-- {
					f, ok := multiplicands[i].(*Flt)
					if ok && f.Val.Cmp(big.NewFloat(1)) == 0 {
						multiplicands[i] = multiplicands[len(multiplicands)-1]
						multiplicands[len(multiplicands)-1] = nil
						multiplicands = multiplicands[:len(multiplicands)-1]
					}
				}
			*/

			// Geometrically accumulate integer values towards the end of the expression
			var lasti *Integer = nil
			for _, e := range multiplicands {
				theint, ok := e.(*Integer)
				if ok {
					if lasti != nil {
						theint.Val.Mul(theint.Val, lasti.Val)
						lasti.Val = big.NewInt(1)
					}
					lasti = theint
				}
			}

			// Geometrically accumulate rational values towards the end of the expression
			var lastr *Rational = nil
			for _, e := range multiplicands {
				therat, ok := e.(*Rational)
				if ok {
					if lastr != nil {
						therat.Num.Mul(therat.Num, lastr.Num)
						therat.Den.Mul(therat.Den, lastr.Den)
						lastr.Num = big.NewInt(1)
						lastr.Den = big.NewInt(1)
					}
					lastr = therat
				}
			}

			// If there is one Integer and one Rational left, merge the Integer into
			// the Rational
			if lasti != nil && lastr != nil {
				lastr.Num.Mul(lastr.Num, lasti.Val)
				// This will get cleaned up in the next step
				lasti.Val = big.NewInt(1)
			}

			// Remove one Integers and Rationals
			for i := len(multiplicands) - 1; i >= 0; i-- {
				toRemove := false
				theint, isInt := multiplicands[i].(*Integer)
				if isInt {
					toRemove = theint.Val.Cmp(big.NewInt(1)) == 0
				}
				therat, isRat := multiplicands[i].(*Rational)
				if isRat {
					toRemove = therat.Num.Cmp(big.NewInt(1)) == 0 && therat.Den.Cmp(big.NewInt(1)) == 0
				}
				if toRemove && len(multiplicands) > 1 {
					multiplicands[i] = multiplicands[len(multiplicands)-1]
					multiplicands[len(multiplicands)-1] = nil
					multiplicands = multiplicands[:len(multiplicands)-1]
				}
			}

			// If one expression remains, replace this Times with the expression
			if len(multiplicands) == 1 {
				return multiplicands[0]
			}

			// Automatically Expand negations (*-1), not (*-1.) of a Plus expression
			if len(multiplicands) == 2 {
				leftint, leftintok := multiplicands[0].(*Integer)
				rightint, rightintok := multiplicands[1].(*Integer)
				leftplus, leftplusok := HeadAssertion(multiplicands[0], "Plus")
				rightplus, rightplusok := HeadAssertion(multiplicands[1], "Plus")
				var theInt *Integer = nil
				var thePlus *Expression = nil
				if leftintok {
					theInt = leftint
				}
				if rightintok {
					theInt = rightint
				}
				if leftplusok {
					thePlus = leftplus
				}
				if rightplusok {
					thePlus = rightplus
				}
				if theInt != nil && thePlus != nil {
					if theInt.Val.Cmp(big.NewInt(-1)) == 0 {
						toreturn := NewExpression([]Ex{&Symbol{"Plus"}})
						addends := thePlus.Parts[1:len(thePlus.Parts)]
						for i := range addends {
							toAppend := NewExpression([]Ex{
								&Symbol{"Times"},
								addends[i],
								&Integer{big.NewInt(-1)},
							})

							toreturn.Parts = append(toreturn.Parts, toAppend)
						}
						return toreturn.Eval(es)
					}
				}
			}

			if len(multiplicands) == 2 {
				rational, isRational := RationalAssertion(multiplicands[0], multiplicands[1])
				if isRational {
					return rational.Eval(es)
				}
				rational, isRational = RationalAssertion(multiplicands[1], multiplicands[0])
				if isRational {
					return rational.Eval(es)
				}
			}

			this.Parts = this.Parts[0:1]
			this.Parts = append(this.Parts, multiplicands...)
			return this
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Simplification rules apply automatically:"},
			&SameTest{"3/2", "(3 + (x^2 * 0)) * 2^-1"},
			&SameTest{"a^(2+c)", "a^2*a^c"},
			&SameTest{"a/(b*c*d)", "a/b/c/d"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"Rational numbers are suppported (explicit rational declaration added for clarity):"},
			&StringTest{"-2/3", "Rational[1, -2]*Rational[-2, 3]*-2"},
			&TestComment{"The product of nothing is defined to be one:"},
			&SameTest{"1", "Times[]"},
		},
		Tests: []TestInstruction{
			// Test that we do not delete all the multiplicands
			&SameTest{"1", "1*1"},
			&SameTest{"1", "5*1/5*1"},

			// Test empty Times expressions
			&SameTest{"1", "Times[]"},

			// Test fraction simplification
			&SameTest{"25", "50/2"},
			&SameTest{"50", "100/2"},
			&SameTest{"50", "1/2*100"},
			&SameTest{"5/4", "1/2*5/2"},
			&SameTest{"1/4", "1/2*1/2"},
			&SameTest{"a/(b*c*d)", "a/b/c/d"},

			// Test Rational detection
			&StringTest{"10", "40/2^2"},
			&StringTest{"10", "40/4"},
			&StringTest{"40/3", "40/3"},
			&StringTest{"20/3", "40/6"},
			&StringTest{"10", "1/4*40"},
			&StringTest{"10", "1/(2^2)*40"},

			// Test proper accumulation of Rationals
			&StringTest{"(2 * sym)", "sym*Rational[1,2]*Rational[2,3]*6"},
			&StringTest{"-2/3", "Rational[1, -2]*Rational[-2, 3]*-2"},
			&StringTest{"Rational", "Rational[1, -2]*Rational[-2, 3]*-2 // Head"},

			// Test multiplicative identity
			&StringTest{"5", "5*1"},
			&StringTest{"a", "1*a"},
			&StringTest{"(1. * a)", "1.*a"},

			// Test multiplicative inverse
			&StringTest{"1", "8*1/8"},
			&StringTest{"1", "a*1/a"},
			&StringTest{"1", "1/a*a"},

			// Test multiplicative property of zero
			&SameTest{"3/2", "(3 + (x^2 * 0)) * 2^-1"},

			// Simplifications with Power
			&SameTest{"a^(2+c)", "a^2*a^c"},
			&SameTest{"a^(2-c)", "a^2/a^c"},
			&SameTest{"m^2", "m*m"},
			&SameTest{"1", "m/m"},
			&SameTest{"1", "m^2/m^2"},
		},
	})
	defs = append(defs, Definition{
		Name: "Product",
		Usage: "`Product[expr, n]` returns the product of `n` copies of `expr`.\n\n" +
			"`Product[expr, {sym, n}]` returns the product of `expr` evaluated with `sym` = 1 to `n`.\n\n" +
			"`Product[expr, {sym, m, n}]` returns the product of `expr` evaluated with `sym` = `m` to `n`.",
		Attributes: []string{"HoldAll", "ReadProtected"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			return this.evalIterationFunc(es, &Integer{big.NewInt(1)}, "Times")
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"120", "Product[a, {a, 1, 5}]"},
			&SameTest{"f[1] * f[2] * f[3] * f[4] * f[5]", "Product[f[a], {a, 1, 5}]"},
			&SameTest{"576", "Product[a^2, {a, 4}]"},
			&SameTest{"1440", "Product[a + b, {a, 1, 2}, {b, 1, 3}]"},
		},
	})
	return
}
