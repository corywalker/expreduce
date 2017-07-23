package expreduce

import "math/big"

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
		Name: "Array",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			nInt, nOk := this.Parts[2].(*Integer)
			if nOk {
				n := nInt.Val.Int64()
				toReturn := NewExpression([]Ex{&Symbol{"System`List"}})
				for i := int64(1); i <= n; i++ {
					toReturn.Parts = append(toReturn.Parts, NewExpression([]Ex{
						this.Parts[1],
						&Integer{big.NewInt(i)},
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
