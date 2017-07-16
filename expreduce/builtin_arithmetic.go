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
	return NewRational(numInt.Val, denInt.Val), true
}

type FoldFn int

const (
	FoldFnAdd FoldFn = iota
	FoldFnMul
)

func typedRealPart(fn FoldFn, i *Integer, r *Rational, f *Flt) Ex {
	if f != nil {
		toReturn := f
		if r != nil {
			if fn == FoldFnAdd {
				toReturn.AddR(r)
			} else if fn == FoldFnMul {
				toReturn.MulR(r)
			}
		}
		if i != nil {
			if fn == FoldFnAdd {
				toReturn.AddI(i)
			} else if fn == FoldFnMul {
				toReturn.MulI(i)
			}
		}
		return toReturn
	}
	if r != nil {
		toReturn := r
		if i != nil {
			if fn == FoldFnAdd {
				toReturn.AddI(i)
			} else if fn == FoldFnMul {
				toReturn.MulI(i)
			}
		}
		return toReturn
	}
	if i != nil {
		return i
	}
	return nil
}

func computeRealPart(fn FoldFn, e *Expression) (Ex, int) {
	var foldedInt *Integer
	var foldedRat *Rational
	var foldedFlt *Flt
	for i := 1; i < len(e.Parts); i++ {
		// TODO: implement short circuiting if we encounter a zero while
		// multiplying.
		asInt, isInt := e.Parts[i].(*Integer)
		if isInt {
			if foldedInt == nil {
				// Try deepcopy if problems. I think this does not cause
				// problems now because we will only modify the value if we end
				// up creating an entirely new expression.
				foldedInt = asInt.DeepCopy().(*Integer)
				continue
			}
			if fn == FoldFnAdd {
				foldedInt.AddI(asInt)
			} else if fn == FoldFnMul {
				foldedInt.MulI(asInt)
			}
			continue
		}
		asRat, isRat := e.Parts[i].(*Rational)
		if isRat {
			if foldedRat == nil {
				foldedRat = asRat.DeepCopy().(*Rational)
				continue
			}
			if fn == FoldFnAdd {
				foldedRat.AddR(asRat)
			} else if fn == FoldFnMul {
				foldedRat.MulR(asRat)
			}
			continue
		}
		asFlt, isFlt := e.Parts[i].(*Flt)
		if isFlt {
			if foldedFlt == nil {
				foldedFlt = asFlt.DeepCopy().(*Flt)
				continue
			}
			if fn == FoldFnAdd {
				foldedFlt.AddF(asFlt)
			} else if fn == FoldFnMul {
				foldedFlt.MulF(asFlt)
			}
			continue
		}
		return typedRealPart(fn, foldedInt, foldedRat, foldedFlt), i
	}
	return typedRealPart(fn, foldedInt, foldedRat, foldedFlt), -1
}

func getArithmeticDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "Plus",
		Usage:      "`(e1 + e2 + ...)` computes the sum of all expressions in the function.",
		Attributes: []string{"Flat", "Listable", "NumericFunction", "OneIdentity", "Orderless"},
		Default:	"0",
		Rules: []Rule{
			{"Verbatim[Plus][beg___, Optional[c1_?NumberQ]*a_, Optional[c2_?NumberQ]*a_, end___]", "beg+(c1+c2)*a+end"},
			// The world is not ready for this madness.
			//{"Verbatim[Plus][beg___, Verbatim[Times][Optional[c1_?NumberQ],a__], Verbatim[Times][Optional[c2_?NumberQ],a__], end___]", "beg+(c1+c2)*a+end"},
		},
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfix(this.Parts[1:], " + ", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// Calls without argument receive identity values
			if len(this.Parts) == 1 {
				return &Integer{big.NewInt(0)}
			}

			res := this
			realPart, symStart := computeRealPart(FoldFnAdd, this)
			if realPart != nil {
				if symStart == -1 {
					return realPart
				}
				res = NewExpression([]Ex{&Symbol{"Plus"}})
				rAsInt, rIsInt := realPart.(*Integer)
				if !(rIsInt && rAsInt.Val.Cmp(big.NewInt(0)) == 0) {
					res.Parts = append(res.Parts, realPart)
				}
				res.Parts = append(res.Parts, this.Parts[symStart:]...)
			}

			// If one expression remains, replace this Plus with the expression
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}

			return res
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
			&SameTest{"50*a", "a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a"},

			// More complicated term combining
			&SameTest{"-3 * m - 10 * n", "-9 * n - n - 3 * m"},

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
		Default:	"1",
		Rules: []Rule{
			{"Times[a_^Optional[m_], a_^Optional[n_], rest___]", "a^(m+n)*rest"},
			{"Times[den_Integer^-1, num_Integer, rest___]", "Rational[num,den] * rest"},
			{"(1/Infinity)", "0"},
			{"Times[ComplexInfinity, rest___]", "ComplexInfinity"},
		},
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringInfix(this.Parts[1:], " * ", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// Calls without argument receive identity values
			if len(this.Parts) == 1 {
				return &Integer{big.NewInt(1)}
			}

			res := this
			realPart, symStart := computeRealPart(FoldFnMul, this)
			if realPart != nil {
				if symStart == -1 {
					return realPart
				}
				res = NewExpression([]Ex{&Symbol{"Times"}})
				rAsInt, rIsInt := realPart.(*Integer)
				if rIsInt && rAsInt.Val.Cmp(big.NewInt(0)) == 0 {
					containsInfinity := MemberQ(this.Parts[symStart:], NewExpression([]Ex{
						&Symbol{"Alternatives"},
						&Symbol{"Infinity"},
						&Symbol{"ComplexInfinity"},
					}), es)
					if containsInfinity {
						return &Symbol{"Indeterminate"}
					}
					return &Integer{big.NewInt(0)}
				}
				if !(rIsInt && rAsInt.Val.Cmp(big.NewInt(1)) == 0) {
					res.Parts = append(res.Parts, realPart)
				}
				res.Parts = append(res.Parts, this.Parts[symStart:]...)
			}

			// If one expression remains, replace this Times with the expression
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}

			// Automatically Expand negations (*-1), not (*-1.) of a Plus expression
			// Perhaps better implemented as a rule.
			if len(res.Parts) == 3 {
				leftint, leftintok := res.Parts[1].(*Integer)
				rightplus, rightplusok := HeadAssertion(res.Parts[2], "Plus")
				if leftintok && rightplusok {
					if leftint.Val.Cmp(big.NewInt(-1)) == 0 {
						toreturn := NewExpression([]Ex{&Symbol{"Plus"}})
						addends := rightplus.Parts[1:len(rightplus.Parts)]
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

			return res
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
	defs = append(defs, Definition{
		Name: "Abs",
	})
	return
}
