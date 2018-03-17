package expreduce

import (
	"github.com/corywalker/mathbigext"
	"math/big"
)

func bigMathFnOneParam(fn func(*big.Float) *big.Float, onlyPos bool) func(*Expression, *EvalState) Ex {
	return (func(this *Expression, es *EvalState) Ex {
		if len(this.Parts) != 2 {
			return this
		}

		flt, ok := this.Parts[1].(*Flt)
		if ok {
			if !onlyPos || flt.Val.Cmp(big.NewFloat(0)) == 1 {
				return NewReal(fn(flt.Val))
			}
		}
		return this
	})
}

// TODO: move to mathbigext.
func NthRoot(x *big.Int, n *big.Int) *big.Int {
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

func RadSimp(radicand *big.Int, index *big.Int) (*big.Int, *big.Int) {
	//xPositivity := x.Cmp(big.NewInt(0))
	//nPositivity := n.Cmp(big.NewInt(0))
	i := big.NewInt(2)
	pow := big.NewInt(0)
	mod := big.NewInt(0)
	div := big.NewInt(0)
	for true {
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

func GetPowerDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:    "Power",
		Default: "1",
		toString: func(this *Expression, params ToStringParams) (bool, string) {
			return ToStringInfixAdvanced(this.Parts[1:], "^", "System`Power", false, "", "", params)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			baseInt, baseIsInt := this.Parts[1].(*Integer)
			powerInt, powerIsInt := this.Parts[2].(*Integer)
			baseFlt, baseIsFlt := this.Parts[1].(*Flt)
			powerFlt, powerIsFlt := this.Parts[2].(*Flt)
			//baseRat, baseIsRat := this.Parts[1].(*Rational)
			powerRat, powerIsRat := this.Parts[2].(*Rational)
			// Anything raised to the 1st power is itself
			if powerIsFlt {
				if powerFlt.Val.Cmp(big.NewFloat(1)) == 0 {
					return this.Parts[1]
				}
			} else if powerIsInt {
				if powerInt.Val.Cmp(big.NewInt(1)) == 0 {
					return this.Parts[1]
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
					return NewSymbol("System`Indeterminate")
				}
				return NewInteger(big.NewInt(1))
			}
			if powerPositivity == 1 && basePositivity == 0 {
				return this.Parts[1]
			}
			if basePositivity == -1 && powerIsFlt {
				if powerFlt.Val.Cmp(big.NewFloat(-1)) == 0 {
					if baseIsInt {
						return NewReal(mathbigext.Pow(big.NewFloat(0).SetInt(baseInt.Val), powerFlt.Val))
					}
					if baseIsFlt {
						return NewReal(mathbigext.Pow(baseFlt.Val, powerFlt.Val))
					}
				}
				// Return unevaluated due to lack of complex number support.
				return this
			}

			//es.Debugf("Power eval. baseIsInt=%v, powerIsInt=%v", baseIsInt, powerIsInt)
			// Fully integer Power expression
			if baseIsInt && powerIsInt {
				cmpres := powerInt.Val.Cmp(big.NewInt(0))
				//es.Debugf("Cmpres: %v", cmpres)
				if cmpres == 1 {
					res := big.NewInt(0)
					res.Exp(baseInt.Val, powerInt.Val, nil)
					return NewInteger(res)
				} else if cmpres == -1 {
					newbase := big.NewInt(0)
					absPower := big.NewInt(0)
					absPower.Abs(powerInt.Val)
					newbase.Exp(baseInt.Val, absPower, nil)
					if newbase.Cmp(big.NewInt(1)) == 0 {
						return NewInteger(big.NewInt(1))
					}
					if newbase.Cmp(big.NewInt(-1)) == 0 {
						return NewInteger(big.NewInt(-1))
					}
					//return NewExpression([]Ex{&Symbol{"System`Power"}, &Integer{newbase}, &Integer{big.NewInt(-1)}})
					return NewExpression([]Ex{NewSymbol("System`Rational"), NewInteger(big.NewInt(1)), NewInteger(newbase)})
				} else {
					return NewExpression([]Ex{NewSymbol("System`Error"), NewString("Unexpected zero power in Power evaluation.")})
				}
			}

			if baseIsFlt && powerIsInt {
				return NewReal(mathbigext.Pow(baseFlt.Val, big.NewFloat(0).SetInt(powerInt.Val)))
			}
			if baseIsInt && powerIsFlt {
				return NewReal(mathbigext.Pow(big.NewFloat(0).SetInt(baseInt.Val), powerFlt.Val))
			}
			if baseIsFlt && powerIsFlt {
				return NewReal(mathbigext.Pow(baseFlt.Val, powerFlt.Val))
			}
			if baseIsInt && powerIsRat {
				x := baseInt.Val
				n := powerRat.Den
				m := powerRat.Num
				xPositivity := x.Cmp(big.NewInt(0))
				nPositivity := n.Cmp(big.NewInt(0))
				if xPositivity >= 0 &&
				   nPositivity == 1 {
					root := NthRoot(x, n)
					if root != nil {
						if m.Cmp(big.NewInt(1)) == 0 {
							return NewInteger(root)
						}
						return E(S("Power"), NewInteger(root), NewInteger(m))
					}
				}
				if nPositivity == 1 {
					absX := big.NewInt(0)
					absX.Abs(x)
					extracted, radicand := RadSimp(absX, n)
					if extracted != nil {
						if xPositivity == -1 {
							radicand.Neg(radicand)
						}
						return E(
							S("Times"),
							NewInteger(extracted),
							E(
								S("Power"),
								NewInteger(radicand),
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
		ExpreduceSpecific: true,
	})
	defs = append(defs, Definition{Name: "FactorSquareFree"})
	defs = append(defs, Definition{
		Name:              "Factor",
		OmitDocumentation: true,
	})
	return
}
