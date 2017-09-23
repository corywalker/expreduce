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
	denPow, denIsPow := HeadAssertion(den, "System`Power")
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

func splitTerm(e Ex) (Ex, Ex, bool) {
	asSym, isSym := e.(*Symbol)
	if isSym {
		return NewInteger(big.NewInt(1)), NewExpression([]Ex{
			NewSymbol("System`Times"),
			asSym,
		}), true
	}
	asTimes, isTimes := HeadAssertion(e, "System`Times")
	if isTimes {
		if len(asTimes.Parts) < 2 {
			return nil, nil, false
		}
		if numberQ(asTimes.Parts[1]) {
			if len(asTimes.Parts) > 2 {
				return asTimes.Parts[1], NewExpression(append([]Ex{NewSymbol("System`Times")}, asTimes.Parts[2:]...)), true
			}
		} else {
			return NewInteger(big.NewInt(1)), NewExpression(append([]Ex{NewSymbol("System`Times")}, asTimes.Parts[1:]...)), true
		}
	}
	asExpr, isExpr := e.(*Expression)
	if isExpr {
		return NewInteger(big.NewInt(1)), NewExpression([]Ex{
			NewSymbol("System`Times"),
			asExpr,
		}), true
	}
	return nil, nil, false
}

func collectedToTerm(coeffs []Ex, vars Ex, fullPart Ex) Ex {
	// Preserve the original expression if there is no need to change it.
	// We can keep all the cached values like the hash.
	if len(coeffs) == 1 {
		return fullPart
	}

	finalC, _ := computeRealPart(FoldFnAdd, NewExpression(append([]Ex{
		NewSymbol("System`Plus")}, coeffs...)))

	toAdd := NewExpression([]Ex{NewSymbol("System`Times")})
	cAsInt, cIsInt := finalC.(*Integer)
	if !(cIsInt && cAsInt.Val.Cmp(big.NewInt(1)) == 0) {
		toAdd.Parts = append(toAdd.Parts, finalC)
	}
	vAsExpr, vIsExpr := HeadAssertion(vars, "System`Times")
	if vIsExpr && len(vAsExpr.Parts) == 2 {
		vars = vAsExpr.Parts[1]
	}
	toAdd.Parts = append(toAdd.Parts, vars)
	if len(toAdd.Parts) == 2 {
		return toAdd.Parts[1]
	}
	return toAdd
}

func collectTerms(e *Expression) *Expression {
	collected := NewExpression([]Ex{NewSymbol("System`Plus")})
	var lastVars Ex
	var lastFullPart Ex
	lastCoeffs := []Ex{}
	for _, part := range e.Parts[1:] {
		coeff, vars, isTerm := splitTerm(part)
		if isTerm {
			if lastVars == nil {
				lastCoeffs = []Ex{coeff}
				lastVars = vars
				lastFullPart = part
			} else {
				if hashEx(vars) == hashEx(lastVars) {
					lastCoeffs = append(lastCoeffs, coeff)
				} else {
					collected.Parts = append(collected.Parts, collectedToTerm(lastCoeffs, lastVars, lastFullPart))

					lastCoeffs = []Ex{coeff}
					lastVars = vars
					lastFullPart = part
				}
			}
		} else {
			collected.Parts = append(collected.Parts, part)
		}
	}
	if lastVars != nil {
		collected.Parts = append(collected.Parts, collectedToTerm(lastCoeffs, lastVars, lastFullPart))
	}
	return collected
}

func getArithmeticDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:    "Plus",
		Default: "0",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			return ToStringInfix(this.Parts[1:], " + ", form, context, contextPath)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// Calls without argument receive identity values
			if len(this.Parts) == 1 {
				return NewInteger(big.NewInt(0))
			}

			res := this
			realPart, symStart := computeRealPart(FoldFnAdd, this)
			if realPart != nil {
				if symStart == -1 {
					return realPart
				}
				res = NewExpression([]Ex{NewSymbol("System`Plus")})
				rAsInt, rIsInt := realPart.(*Integer)
				if !(rIsInt && rAsInt.Val.Cmp(big.NewInt(0)) == 0) {
					res.Parts = append(res.Parts, realPart)
				}
				res.Parts = append(res.Parts, this.Parts[symStart:]...)
			}

			collected := collectTerms(res)
			if hashEx(collected) != hashEx(res) {
				res = collected
			}

			// If one expression remains, replace this Plus with the expression
			if len(res.Parts) == 2 {
				return res.Parts[1]
			}

			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Sum",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			return this.evalIterationFunc(es, NewInteger(big.NewInt(0)), "System`Plus")
		},
	})
	defs = append(defs, Definition{
		Name:    "Times",
		Default: "1",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			return ToStringInfix(this.Parts[1:], " * ", form, context, contextPath)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			// Calls without argument receive identity values
			if len(this.Parts) == 1 {
				return NewInteger(big.NewInt(1))
			}

			res := this
			realPart, symStart := computeRealPart(FoldFnMul, this)
			if realPart != nil {
				if symStart == -1 {
					return realPart
				}
				res = NewExpression([]Ex{NewSymbol("System`Times")})
				rAsInt, rIsInt := realPart.(*Integer)
				if rIsInt && rAsInt.Val.Cmp(big.NewInt(0)) == 0 {
					containsInfinity := MemberQ(this.Parts[symStart:], NewExpression([]Ex{
						NewSymbol("System`Alternatives"),
						NewSymbol("System`Infinity"),
						NewSymbol("System`ComplexInfinity"),
						NewSymbol("System`Indeterminate"),
					}), es)
					if containsInfinity {
						return NewSymbol("System`Indeterminate")
					}
					return NewInteger(big.NewInt(0))
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
				rightplus, rightplusok := HeadAssertion(res.Parts[2], "System`Plus")
				if leftintok && rightplusok {
					if leftint.Val.Cmp(big.NewInt(-1)) == 0 {
						toreturn := NewExpression([]Ex{NewSymbol("System`Plus")})
						addends := rightplus.Parts[1:len(rightplus.Parts)]
						for i := range addends {
							toAppend := NewExpression([]Ex{
								NewSymbol("System`Times"),
								addends[i],
								NewInteger(big.NewInt(-1)),
							})

							toreturn.Parts = append(toreturn.Parts, toAppend)
						}
						return toreturn.Eval(es)
					}
				}
			}

			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Product",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			return this.evalIterationFunc(es, NewInteger(big.NewInt(1)), "System`Times")
		},
	})
	defs = append(defs, Definition{Name: "Abs"})
	defs = append(defs, Definition{Name: "Divide"})
	return
}
