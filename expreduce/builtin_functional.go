package expreduce

import (
	"math/big"
)

func getFunctionalDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Function",
	})
	defs = append(defs, Definition{
		Name: "Slot",
	})
	defs = append(defs, Definition{
		Name: "Apply",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			sym, isSym := this.Parts[1].(*Symbol)
			expr, isExpr := this.Parts[2].(*Expression)
			if isSym && isExpr {
				toReturn := NewExpression([]Ex{sym})
				toReturn.Parts = append(toReturn.Parts, expr.Parts[1:]...)
				return toReturn.Eval(es)
			}
			return this.Parts[2]
		},
	})
	defs = append(defs, Definition{
		Name: "Map",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			expr, isExpr := this.Parts[2].(*Expression)
			if isExpr {
				toReturn := NewExpression([]Ex{expr.Parts[0]})
				for i := 1; i < len(expr.Parts); i++ {
					toReturn.Parts = append(toReturn.Parts, NewExpression([]Ex{
						this.Parts[1],
						expr.Parts[i],
					}))
				}
				return toReturn
			}
			return this.Parts[2]
		},
	})
	defs = append(defs, Definition{
		Name: "FoldList",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 4 {
				return this
			}

			f := this.Parts[1]
			first := this.Parts[2]
			values, nonAtomic := this.Parts[3].(*Expression)

			if !nonAtomic {
				return this
			}

			toReturn := NewExpression([]Ex{values.Parts[0], first})

			if len(values.Parts) < 2 {
				return toReturn
			}

			expr := NewExpression([]Ex{
				f,
				first,
				values.Parts[1],
			})

			toReturn.Parts = append(toReturn.Parts, expr)

			for i := 2; i < len(values.Parts); i++ {
				expr = NewExpression([]Ex{
					f,
					expr,
					values.Parts[i],
				})

				toReturn.Parts = append(toReturn.Parts, expr)
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{Name: "Fold"})
	defs = append(defs, Definition{
		Name: "NestList",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 4 {
				return this
			}

			f := this.Parts[1]
			expr := this.Parts[2]
			nInt, isInteger := this.Parts[3].(*Integer)
			if !isInteger {
				return this
			}
			n := nInt.Val.Int64()
			if n < 0 {
				return this
			}

			toReturn := NewExpression([]Ex{NewSymbol("System`List"), expr})

			for i := int64(1); i <= n; i++ {
				expr = NewExpression([]Ex{
					f,
					expr,
				})

				toReturn.Parts = append(toReturn.Parts, expr)
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{Name: "Nest"})
	defs = append(defs, Definition{
		Name: "NestWhileList",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) < 4 || len(this.Parts) > 7 {
				return this
			}

			f := this.Parts[1]
			expr := this.Parts[2]
			test := this.Parts[3]

			m := int64(1)
			if len(this.Parts) > 4 {
				mInt, isInteger := this.Parts[4].(*Integer)
				mSymbol, isSymbol := this.Parts[4].(*Symbol)
				if isInteger {
					m = mInt.Val.Int64()
					if m < 0 {
						return this
					}
				} else if isSymbol {
					if mSymbol.IsEqual(NewSymbol("System`All"), &es.CASLogger) == "EQUAL_TRUE" {
						m = -1
					} else {
						return this
					}
				} else {
					return this
				}
			}

			max := int64(-1)
			if len(this.Parts) > 5 {
				maxInt, isInteger := this.Parts[5].(*Integer)
				maxSymbol, isSymbol := this.Parts[5].(*Symbol)
				if isInteger {
					max = maxInt.Val.Int64()
					if maxInt.Val.Int64() < 0 {
						return this
					}
				} else if isSymbol {
					if maxSymbol.IsEqual(NewSymbol("System`Infinity"), &es.CASLogger) == "EQUAL_TRUE" {
						max = -1
					} else {
						return this
					}
				} else {
					return this
				}
			}

			n := int64(0)
			if len(this.Parts) > 6 {
				bonusIterationsInt, isInteger := this.Parts[6].(*Integer)
				if isInteger && bonusIterationsInt.Val.Int64() >= int64(0) {
					n = bonusIterationsInt.Val.Int64()
				}
			}

			evaluated := []Ex{expr.DeepCopy().Eval(es)}
			toReturn := NewExpression([]Ex{NewSymbol("System`List"), expr})

			isequal := "EQUAL_TRUE"
			cont := isequal == "EQUAL_TRUE"
			for i := int64(2); cont; i++ {
				expr = NewExpression([]Ex{
					f,
					expr,
				})
				toReturn.Parts = append(toReturn.Parts, expr)
				evaluated = append(evaluated, expr.DeepCopy().Eval(es)) // Could use a stack of length m

				if i >= m {
					testExpression := NewExpression([]Ex{test})
					if m >= 0 {
						testExpression.Parts = append(testExpression.Parts, evaluated[int64(len(evaluated))-m:]...)
					} else {
						testExpression.Parts = append(testExpression.Parts, evaluated...)
					}
					isequal = testExpression.Eval(es).IsEqual(NewSymbol("System`True"), &es.CASLogger)
					cont = isequal == "EQUAL_TRUE"
				}

				if i > max && max != -1 {
					cont = false
				}
			}

			if n > 0 {
				for i := int64(0); i < n; i++ {
					expr = NewExpression([]Ex{
						f,
						expr,
					})
					toReturn.Parts = append(toReturn.Parts, expr)
				}
			} else {
				toReturn.Parts = toReturn.Parts[:int64(len(toReturn.Parts))+n]
			}

			return toReturn
		},
	})
	defs = append(defs, Definition{Name: "NestWhile"})
	defs = append(defs, Definition{Name: "FixedPointList"})
	defs = append(defs, Definition{Name: "FixedPoint"})
	defs = append(defs, Definition{
		Name: "Array",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			nInt, nOk := this.Parts[2].(*Integer)
			if nOk {
				n := nInt.Val.Int64()
				toReturn := NewExpression([]Ex{NewSymbol("System`List")})
				for i := int64(1); i <= n; i++ {
					toReturn.Parts = append(toReturn.Parts, NewExpression([]Ex{
						this.Parts[1],
						NewInteger(big.NewInt(i)),
					}))
				}
				return toReturn
			}
			return this.Parts[2]
		},
	})
	defs = append(defs, Definition{
		Name: "Identity",
	})
	return
}
