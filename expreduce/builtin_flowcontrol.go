package expreduce

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func applyWithFn(e expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) (expreduceapi.Ex, bool) {
	if len(e.GetParts()) != 3 {
		return nil, false
	}
	vars, isList := HeadAssertion(e.GetParts()[1], "System`List")
	if !isList {
		return nil, false
	}
	rules := []expreduceapi.ExpressionInterface{}
	for _, vDef := range vars.GetParts()[1:] {
		set, isSet := HeadAssertion(vDef, "System`Set")
		setDelayed, isSetDelayed := HeadAssertion(vDef, "System`SetDelayed")
		if !(isSet || isSetDelayed) {
			return nil, false
		}
		var setEx expreduceapi.ExpressionInterface = nil
		ruleHead := ""
		if isSet {
			setEx = set
			ruleHead = "System`Rule"
		} else {
			setEx = setDelayed
			ruleHead = "System`RuleDelayed"
		}
		if len(setEx.GetParts()) != 3 {
			return nil, false
		}
		rules = append(rules, NewExpression([]expreduceapi.Ex{
			NewSymbol(ruleHead),
			setEx.GetParts()[1],
			setEx.GetParts()[2],
		}))
	}
	return rulesReplaceAll(e.GetParts()[2], rules, es), true
}

func isBreak(e expreduceapi.Ex) bool {
	_, isBr := HeadAssertion(e, "System`Break")
	return isBr
}

func GetFlowControlDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "If",
		// WARNING: Watch out for putting rules here. It can interfere with how
		// Return works.
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) > 4 || len(this.GetParts()) < 3 {
				return this
			}
			var falseVal expreduceapi.Ex = NewSymbol("System`Null")
			if len(this.GetParts()) == 4 {
				falseVal = this.GetParts()[3]
			}

			var isequal string = this.GetParts()[1].IsEqual(NewSymbol("System`True"))
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return this.GetParts()[2]
			} else if isequal == "EQUAL_FALSE" {
				return falseVal
			}

			return NewExpression([]expreduceapi.Ex{NewSymbol("System`Error"), NewString("Unexpected equality return value.")})
		},
	})
	defs = append(defs, Definition{
		Name: "While",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			isTrue := IsSameQ(this.GetParts()[1].DeepCopy().Eval(es), NewSymbol("System`True"), es.GetLogger())
			for isTrue {
				tmpRes := this.GetParts()[2].DeepCopy().Eval(es)
				retVal, isReturn := tryReturnValue(tmpRes, nil, es)
				if isReturn {
					return retVal
				}
				if isBreak(tmpRes) {
					return S("Null")
				}
				isTrue = IsSameQ(this.GetParts()[1].DeepCopy().Eval(es), NewSymbol("System`True"), es.GetLogger())
			}

			return NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "CompoundExpression",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			var toReturn expreduceapi.Ex
			for i := 1; i < len(this.GetParts()); i++ {
				toReturn = this.GetParts()[i].Eval(es)
				if es.HasThrown() {
					return es.Thrown()
				}
				if _, isReturn := HeadAssertion(toReturn, "System`Return"); isReturn {
					return toReturn
				}
			}
			return toReturn
		},
	})
	// https://mathematica.stackexchange.com/questions/29353/how-does-return-work
	defs = append(defs, Definition{Name: "Return"})
	defs = append(defs, Definition{
		Name: "Which",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts())%2 != 1 {
				return this
			}
			for i := 1; i < len(this.GetParts()); i += 2 {
				condRes := this.GetParts()[i].Eval(es)
				resSym, resIsSym := condRes.(*Symbol)
				if !resIsSym {
					continue
				}
				if resSym.Name == "System`True" {
					return this.GetParts()[i+1]
				}
			}
			return NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Switch",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) < 4 || len(this.GetParts())%2 != 0 {
				return this
			}
			for i := 2; i < len(this.GetParts()); i += 2 {
				if match, _ := IsMatchQ(this.GetParts()[1], this.GetParts()[i], EmptyPD(), es); match {
					return this.GetParts()[i+1]
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "With",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			res, ok := applyWithFn(this, es)
			if !ok {
				return this
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Do",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) >= 3 {
				mis, isOk := multiIterSpecFromLists(es, this.GetParts()[2:])
				if isOk {
					// Simulate evaluation within Block[]
					mis.takeVarSnapshot(es)
					for mis.cont() {
						mis.defineCurrent(es)
						res := this.GetParts()[1].DeepCopy().Eval(es)
						if es.HasThrown() {
							return es.Thrown()
						}
						if asReturn, isReturn := HeadAssertion(res, "System`Return"); isReturn {
							if len(asReturn.GetParts()) < 2 {
								return NewSymbol("System`Null")
							}
							return asReturn.GetParts()[1]
						}
						mis.next()
					}
					mis.restoreVarSnapshot(es)
					return NewSymbol("System`Null")
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{Name: "For"})
	return
}
