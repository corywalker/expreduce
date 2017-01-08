package expreduce

import "math/big"

func GetPlusDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "Plus",
		attributes: []string{"Flat", "Listable", "NumericFunction", "OneIdentity", "Orderless"},
		rules: []Rule{
			{"Plus[a_, -a_, rest___]", "Plus[rest]"},
			{"Plus[c1_Integer*a_, c2_Integer*a_, rest___]", "((c1+c2)*a + rest)"},
			// For some reason, this messes up the Infinity - Infinity rule
			{"Plus[c1_Integer*a_, a_, rest___]", "(c1+1)*a+rest"},
			{"Plus[a_, a_, rest___]", "2*a + rest"},
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
		tests: []TestInstruction{
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
			//&SameTest{"7*a * b - 2*a * c", "3*a*b - 2*a*c + 4*a*b"},
			// For the next two, currently having trouble combining 3ab+4ab, etc
			//&SameTest{"-3*a - 2*b + 3*a*b", "2*a - 4*b + 3*a*b - 5*a + 2*b"},
			//&SameTest{"7*x - 11*y + x*y", "8*x - 9*y - 3*x*y - 2*y - x + 4*x*y"},
			//&SameTest{"-3*a*b*c*d*e*f", "4*a*b*c*d*e*f + -7*a*b*c*d*e*f"},
			//&SameTest{"-3*a*b*c*d*e*f", "a*b*c*4*d*e*f + -a*b*c*d*e*f*7"},
			//&SameTest{"-3*a*b*c*d*e*f", "a*b*2*c*2*d*e*f + -a*b*c*d*e*f*7"},

			//&SameTest{"2 r + 2 t", "2 r - 3 s - t + 3 t + 3 s"},
			//&SameTest{"3 (x - 2 y) - 4 x y + 2 (-1 + x y)", "2 (x*y - 1) + 3 (x - 2 y) - 4 x*y"},
			//&SameTest{"-2 + x (3 - 2 y) - 6 y", "2 (x*y - 1) + 3 (x - 2 y) - 4 x*y // BasicSimplify"},
			//&SameTest{"-4 s + 4 r s - 3 (1 + r s)", "4 r*s - 2 s - 3 (r*s + 1) - 2 s"},
			//&SameTest{"-3 + (-4 + r) s", "4 r*s - 2 s - 3 (r*s + 1) - 2 s // BasicSimplify"},
			//&SameTest{"7 y - z + 3 y z", "8 y - 2 z - (y - z) + 3 y*z"},
			//&SameTest{"-z + y (7 + 3 z)", "8 y - 2 z - (y - z) + 3 y*z // BasicSimplify"},
		},
	})
	defs = append(defs, Definition{
		name: "Infinity",
		attributes: []string{"ReadProtected"},
		rules: []Rule{
			{"Plus[Infinity, _Integer, rest___]", "Infinity + rest"},
			{"Plus[Infinity, _Real, rest___]", "Infinity + rest"},
			{"Plus[-Infinity, _Integer, rest___]", "-Infinity + rest"},
			{"Plus[-Infinity, _Real, rest___]", "-Infinity + rest"},
			{"Plus[Infinity, -Infinity, rest___]", "Indeterminate + rest"},
		},
		tests: []TestInstruction{
			&SameTest{"Infinity", "Infinity - 1"},
			&SameTest{"Infinity", "Infinity - 990999999"},
			&SameTest{"Infinity", "Infinity - 990999999."},
			&SameTest{"Indeterminate", "Infinity - Infinity"},
			// I can't simplify this type of infinity until I have ;/ rules
			//&SameTest{"Infinity", "Infinity*2"},
			&SameTest{"-Infinity", "Infinity*-1"},
			&SameTest{"-Infinity", "-Infinity + 1"},
			&SameTest{"-Infinity", "-Infinity + 999"},
			&SameTest{"Infinity", "-Infinity*-1"},
			&SameTest{"0", "1/Infinity"},
		},
	})
	defs = append(defs, Definition{
		name: "ComplexInfinity",
	})
	defs = append(defs, Definition{
		name: "Indeterminate",
	})
	return
}
