package expreduce

import (
	"fmt"
	"math"
	"math/big"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/corywalker/mathbigext"
)

func bigMathFnOneParam(
	fn func(*big.Float) *big.Float,
	onlyPos bool,
) func(expreduceapi.ExpressionInterface, expreduceapi.EvalStateInterface) expreduceapi.Ex {
	return (func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
		if len(this.GetParts()) != 2 {
			return this
		}

		flt, ok := this.GetParts()[1].(*atoms.Flt)
		if ok {
			if !onlyPos || flt.Val.Cmp(big.NewFloat(0)) == 1 {
				return atoms.NewReal(fn(flt.Val))
			}
		}
		return this
	})
}

// NthRoot calculates the n'th root of x. TODO: move to mathbigext.
func nthRoot(x *big.Int, n *big.Int) *big.Int {
	if x.Cmp(big.NewInt(0)) == 0 {
		return big.NewInt(0)
	}
	// https://en.wikipedia.org/wiki/Nth_root_algorithm -
	// math/big has this implemented for the sqrt case, but not
	// for the nth-root case.
	nMinusOne := big.NewInt(-1)
	nMinusOne.Add(nMinusOne, n)

	z1 := big.NewInt(2)
	z2 := big.NewInt(1)
	z1pow := big.NewInt(1)
	z1mul := big.NewInt(1)
	// Set z1 to a decent guess. Must be ≥ x^(1/n)
	z1.Exp(z1, big.NewInt(int64(x.BitLen())/2+1), nil)
	for {
		// x->A, z1->x_k, z2->x_{k+1}
		z1pow.Exp(z1, nMinusOne, nil)
		z1mul.Mul(z1, nMinusOne)
		z2 = z2.Quo(x, z1pow)
		z2 = z2.Add(z2, z1mul)
		z2 = z2.Div(z2, n)
		if z2.Cmp(z1) >= 0 {
			// z1 might be answer. Check first.
			z2.Exp(z1, n, nil)
			if z2.Cmp(x) == 0 {
				return z1
			}
			return nil
		}
		z1, z2 = z2, z1
	}
}

func extractPower(x *big.Int, r *atoms.Rational) expreduceapi.Ex {
	talliedFactors := primeFactorsTallied(x)
	hasPowerAtLeastTwo := false
	for _, tf := range talliedFactors {
		if tf.power > 1 {
			hasPowerAtLeastTwo = true
			break
		}
	}
	if !hasPowerAtLeastTwo {
		return nil
	}
	bases := make(map[uint64]*big.Int)
	for _, tf := range talliedFactors {
		base, hasVal := bases[tf.power]
		if !hasVal {
			bases[tf.power] = tf.factor
		} else {
			base.Mul(base, tf.factor)
		}
	}
	toReturn := atoms.E(atoms.S("Times"))
	for power, base := range bases {
		bigPower := big.NewInt(0)
		bigPower.SetUint64(power)
		thisR := r.DeepCopy().(*atoms.Rational)
		thisR.MulBigI(bigPower)
		thisR.SetNeedsEval(true)
		toReturn.AppendEx(atoms.E(
			atoms.S("Power"),
			atoms.NewInteger(base),
			thisR,
		))
	}
	return toReturn
}

func radSimp(radicand *big.Int, index *big.Int) (*big.Int, *big.Int) {
	i := big.NewInt(2)
	pow := big.NewInt(0)
	mod := big.NewInt(0)
	div := big.NewInt(0)
	for {
		pow.Exp(i, index, nil)
		mod.Mod(radicand, pow)
		cmpRes := mod.Cmp(big.NewInt(0))
		if cmpRes == 0 {
			div = div.Div(radicand, pow)
			return i, div
		} else if cmpRes > 0 {
			break
		}
	}
	return nil, nil
}

func getPowerDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:    "Power",
		Default: "1",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if this.Len() == 2 {
				if atoms.IsSameQ(
					this.GetPart(2),
					atoms.NewRational(big.NewInt(1), big.NewInt(2)),
				) {
					nextParams := params
					nextParams.PreviousHead = "<TOPLEVEL>"
					if params.Form == "TeXForm" {
						return true, fmt.Sprintf(
							"\\sqrt{%v}",
							this.GetPart(1).StringForm(nextParams),
						)
					}
					if params.Form == "InputForm" {
						return true, fmt.Sprintf(
							"Sqrt[%v]",
							this.GetPart(1).StringForm(nextParams),
						)
					}
				}
				if atoms.IsSameQ(
					this.GetPart(2),
					atoms.NewRational(big.NewInt(-1), big.NewInt(2)),
				) {
					nextParams := params
					nextParams.PreviousHead = "<TOPLEVEL>"
					if params.Form == "TeXForm" {
						return true, fmt.Sprintf(
							"\\frac{1}{\\sqrt{%v}}",
							this.GetPart(1).StringForm(nextParams),
						)
					}
					if params.Form == "InputForm" {
						return true, fmt.Sprintf(
							"(1/Sqrt[%v])",
							this.GetPart(1).StringForm(nextParams),
						)
					}
				}
				if atoms.IsSameQ(this.GetPart(2), atoms.NewInt(-1)) {
					nextParams := params
					nextParams.PreviousHead = "<TOPLEVEL>"
					if params.Form == "TeXForm" {
						return true, fmt.Sprintf(
							"\\frac{1}{%v}",
							this.GetPart(1).StringForm(nextParams),
						)
					}
					if params.Form == "InputForm" {
						return true, fmt.Sprintf(
							"(1/(%v))",
							this.GetPart(1).StringForm(nextParams),
						)
					}
				}
			}
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				"^",
				"System`Power",
				false,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			baseInt, baseIsInt := this.GetParts()[1].(*atoms.Integer)
			powerInt, powerIsInt := this.GetParts()[2].(*atoms.Integer)
			baseFlt, baseIsFlt := this.GetParts()[1].(*atoms.Flt)
			powerFlt, powerIsFlt := this.GetParts()[2].(*atoms.Flt)
			//baseRat, baseIsRat := this.Parts[1].(*Rational)
			powerRat, powerIsRat := this.GetParts()[2].(*atoms.Rational)
			// Anything raised to the 1st power is itself
			if powerIsFlt {
				if powerFlt.Val.Cmp(big.NewFloat(1)) == 0 {
					return this.GetParts()[1]
				}
			} else if powerIsInt {
				if powerInt.Val.Cmp(big.NewInt(1)) == 0 {
					return this.GetParts()[1]
				}
			}
			// Anything raised to the 0th power is 1, with a small exception
			powerPositivity := -2
			if powerIsFlt {
				powerPositivity = powerFlt.Val.Cmp(big.NewFloat(0))
			} else if powerIsInt {
				powerPositivity = powerInt.Val.Cmp(big.NewInt(0))
			}
			basePositivity := -2
			if baseIsFlt {
				basePositivity = baseFlt.Val.Cmp(big.NewFloat(0))
			} else if baseIsInt {
				basePositivity = baseInt.Val.Cmp(big.NewInt(0))
			}
			if powerPositivity == 0 && (baseIsInt || baseIsFlt) {
				if basePositivity == 0 {
					return atoms.NewSymbol("System`Indeterminate")
				}
				return atoms.NewInteger(big.NewInt(1))
			}
			if powerPositivity == 1 && basePositivity == 0 {
				return this.GetParts()[1]
			}
			if basePositivity == -1 && powerIsFlt {
				if powerFlt.Val.Cmp(big.NewFloat(-1)) == 0 {
					if baseIsInt {
						return atoms.NewReal(
							mathbigext.Pow(
								big.NewFloat(0).SetInt(baseInt.Val),
								powerFlt.Val,
							),
						)
					}
					if baseIsFlt {
						return atoms.NewReal(
							mathbigext.Pow(baseFlt.Val, powerFlt.Val),
						)
					}
				}
				// TODO(corywalker): Optimize this logic. There should be no
				// need for Eval-ing expressions. Simply use numerics built-in
				// to Go.
				// a^b
				// coeff := ((a^2)^(b/2))

				// Precompute shared values.
				coeff :=

					es.Eval(atoms.E(
						atoms.S("Power"),
						atoms.E(
							atoms.S("Power"),
							baseFlt.DeepCopy(),
							atoms.NewInt(2),
						),
						atoms.E(
							atoms.S("Times"),
							powerFlt.DeepCopy(),
							atoms.NewRational(big.NewInt(1), big.NewInt(2)),
						),
					)).(*atoms.Flt)
				// inner := b Arg[a]
				inner :=

					es.Eval(atoms.E(
						atoms.S("Times"),
						powerFlt.DeepCopy(),
						atoms.E(
							atoms.S("Arg"),
							baseFlt.DeepCopy(),
						),
					)).(*atoms.Flt)
				re :=

					es.Eval(atoms.E(
						atoms.S("Times"),
						coeff.DeepCopy(),
						atoms.E(
							atoms.S("Cos"),
							inner.DeepCopy(),
						),
					)).(*atoms.Flt)
				// If the exponent has no fractional part, i.e. should be an integer, then we can say there will be no imaginary component to the result.
				// Reduce[Sin[b*Arg[a]] == 0, b, Reals] // FullSimplify
				// C[1] \[Element] Integers && a < 0 && (b == 2 C[1] || b == 1 + 2 C[1])
				if powerFlt.Val.IsInt() {
					// TODO: We may want to decide this earlier. Figure this out.
					return re
				}
				im :=

					es.Eval(atoms.E(
						atoms.S("Times"),
						coeff.DeepCopy(),
						atoms.E(
							atoms.S("Sin"),
							inner.DeepCopy(),
						),
					)).(*atoms.Flt)
				return atoms.NewComplex(re, im)
			}

			//es.Debugf("Power eval. baseIsInt=%v, powerIsInt=%v", baseIsInt, powerIsInt)
			// Fully integer Power expression
			if baseIsInt && powerIsInt {
				cmpres := powerInt.Val.Cmp(big.NewInt(0))
				//es.Debugf("Cmpres: %v", cmpres)
				if cmpres == 1 {
					res := big.NewInt(0)
					res.Exp(baseInt.Val, powerInt.Val, nil)
					return atoms.NewInteger(res)
				} else if cmpres == -1 {
					newbase := big.NewInt(0)
					absPower := big.NewInt(0)
					absPower.Abs(powerInt.Val)
					newbase.Exp(baseInt.Val, absPower, nil)
					if newbase.Cmp(big.NewInt(1)) == 0 {
						return atoms.NewInteger(big.NewInt(1))
					}
					if newbase.Cmp(big.NewInt(-1)) == 0 {
						return atoms.NewInteger(big.NewInt(-1))
					}
					//return NewExpression([]Ex{&Symbol{"System`Power"}, &Integer{newbase}, &Integer{big.NewInt(-1)}})
					return atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`Rational"), atoms.NewInteger(big.NewInt(1)), atoms.NewInteger(newbase)})
				} else {
					return atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`Error"), atoms.NewString("Unexpected zero power in Power evaluation.")})
				}
			}

			if baseIsFlt && powerIsInt {
				return atoms.NewReal(
					mathbigext.Pow(
						baseFlt.Val,
						big.NewFloat(0).SetInt(powerInt.Val),
					),
				)
			}
			if baseIsInt && powerIsFlt {
				return atoms.NewReal(
					mathbigext.Pow(
						big.NewFloat(0).SetInt(baseInt.Val),
						powerFlt.Val,
					),
				)
			}
			if baseIsFlt && powerIsFlt {
				return atoms.NewReal(mathbigext.Pow(baseFlt.Val, powerFlt.Val))
			}
			if baseIsInt && powerIsRat {
				x := baseInt.Val
				n := powerRat.Den
				m := powerRat.Num
				xPositivity := x.Cmp(big.NewInt(0))
				nPositivity := n.Cmp(big.NewInt(0))
				mPositivity := m.Cmp(big.NewInt(0))
				if xPositivity >= 0 &&
					nPositivity == 1 {
					root := nthRoot(x, n)
					if root != nil {
						if m.Cmp(big.NewInt(1)) == 0 {
							return atoms.NewInteger(root)
						}
						return atoms.E(
							atoms.S("Power"),
							atoms.NewInteger(root),
							atoms.NewInteger(m),
						)
					}
					powerExtracted := extractPower(x, powerRat)
					if powerExtracted != nil {
						return powerExtracted
					}
				}
				if nPositivity == 1 {
					absX := big.NewInt(0)
					absX.Abs(x)
					extracted, radicand := radSimp(absX, n)
					if extracted != nil {
						if xPositivity == -1 {
							radicand.Neg(radicand)
						}
						var coeff expreduceapi.Ex = atoms.NewInteger(extracted)
						if mPositivity == -1 {
							coeff = atoms.NewRational(big.NewInt(1), extracted)
						}
						return atoms.E(
							atoms.S("Times"),
							coeff,
							atoms.E(
								atoms.S("Power"),
								atoms.NewInteger(radicand),
								powerRat,
							),
						)
					}
				}
				return this
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "PowerExpand",
		// This function is not implemented to a satisfiable extent. Do not
		// document it yet.
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{Name: "Expand"})
	defs = append(defs, Definition{Name: "ExpandAll"})
	defs = append(defs, Definition{
		Name:         "Log",
		toString:     simpleTeXToString("log"),
		legacyEvalFn: bigMathFnOneParam(mathbigext.Log, true),
	})
	defs = append(defs, Definition{Name: "Sqrt"})
	defs = append(defs, Definition{Name: "I"})
	defs = append(defs, Definition{Name: "PolynomialQ"})
	defs = append(defs, Definition{Name: "Exponent"})
	defs = append(defs, Definition{Name: "Coefficient"})
	defs = append(defs, Definition{Name: "CoefficientList"})
	defs = append(defs, Definition{Name: "PolynomialQuotientRemainder"})
	defs = append(defs, Definition{Name: "PolynomialQuotient"})
	defs = append(defs, Definition{Name: "PolynomialRemainder"})
	defs = append(defs, Definition{Name: "FactorTermsList"})
	defs = append(defs, Definition{Name: "FactorTerms"})
	defs = append(defs, Definition{Name: "ExpreduceFactorConstant"})
	defs = append(defs, Definition{Name: "Variables"})
	defs = append(defs, Definition{Name: "PolynomialGCD"})
	defs = append(defs, Definition{Name: "SquareFreeQ"})
	defs = append(defs, Definition{
		Name:              "PSimplify",
		OmitDocumentation: true,
		expreduceSpecific: true,
	})
	defs = append(defs, Definition{Name: "FactorSquareFree"})
	defs = append(defs, Definition{
		Name:              "Factor",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{Name: "Arg"})
	defs = append(defs, Definition{Name: "ComplexExpand"})
	defs = append(defs, Definition{
		Name:         "Exp",
		legacyEvalFn: mathFnOneParam(math.Exp),
	})
	defs = append(defs, Definition{Name: "Conjugate"})
	return
}
