package cas

import "math/big"

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

func factorial(n *big.Int) (result *big.Int) {
	result = new(big.Int)

	switch n.Cmp(&big.Int{}) {
	case -1, 0:
		result.SetInt64(1)
	default:
		result.Set(n)
		var one big.Int
		one.SetInt64(1)
		result.Mul(result, factorial(n.Sub(n, &one)))
	}
	return
}

func GetTimesDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "Times",
		toString: func (this *Expression, form string) (bool, string) {
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

			// If there is a zero in the expression, return zero
			for _, e := range multiplicands {
				float, isFlt := e.(*Flt)
				if isFlt {
					if float.Val.Cmp(big.NewFloat(0)) == 0 {
						return &Flt{big.NewFloat(0)}
					}
				}
				integer, isInteger := e.(*Integer)
				if isInteger {
					if integer.Val.Cmp(big.NewInt(0)) == 0 {
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
						toreturn := &Expression{[]Ex{&Symbol{"Plus"}}}
						addends := thePlus.Parts[1:len(thePlus.Parts)]
						for i := range addends {
							toAppend := &Expression{[]Ex{
								&Symbol{"Times"},
								addends[i],
								&Integer{big.NewInt(-1)},
							}}
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
	})
	defs = append(defs, Definition{
		name: "Factorial",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			asInt, isInt := this.Parts[1].(*Integer)
			if isInt {
				if asInt.Val.Cmp(big.NewInt(0)) == -1 {
					return &Symbol{"ComplexInfinity"}
				}
				return &Integer{factorial(asInt.Val)}
			}
			return this
		},
	})
	return
}
