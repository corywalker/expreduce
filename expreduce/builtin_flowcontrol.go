package expreduce

import (
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/iterspec"
	"github.com/corywalker/expreduce/expreduce/matcher"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func applyWithFn(
	e expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
) (expreduceapi.Ex, bool) {
	if len(e.GetParts()) != 3 {
		return nil, false
	}
	vars, isList := atoms.HeadAssertion(e.GetParts()[1], "System`List")
	if !isList {
		return nil, false
	}
	rules := []expreduceapi.ExpressionInterface{}
	for _, vDef := range vars.GetParts()[1:] {
		set, isSet := atoms.HeadAssertion(vDef, "System`Set")
		setDelayed, isSetDelayed := atoms.HeadAssertion(
			vDef,
			"System`SetDelayed",
		)
		if !(isSet || isSetDelayed) {
			return nil, false
		}
		var setEx expreduceapi.ExpressionInterface
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
		rules = append(rules, atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol(ruleHead),
			setEx.GetParts()[1],
			setEx.GetParts()[2],
		}))
	}
	return rulesReplaceAll(e.GetParts()[2], rules, es), true
}

func isBreak(e expreduceapi.Ex) bool {
	_, isBr := atoms.HeadAssertion(e, "System`Break")
	return isBr
}

func getFlowControlDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "If",
		// WARNING: Watch out for putting rules here. It can interfere with how
		// Return works.
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) > 4 || len(this.GetParts()) < 3 {
				return this
			}
			var falseVal expreduceapi.Ex = atoms.NewSymbol("System`Null")
			if len(this.GetParts()) == 4 {
				falseVal = this.GetParts()[3]
			}

			var isequal string = this.GetParts()[1].IsEqual(atoms.NewSymbol("System`True"))
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return this.GetParts()[2]
			} else if isequal == "EQUAL_FALSE" {
				return falseVal
			}

			return atoms.NewExpression(
				[]expreduceapi.Ex{
					atoms.NewSymbol("System`Error"),
					atoms.NewString("Unexpected equality return value."),
				},
			)
		},
	})
	defs = append(defs, Definition{
		Name: "While",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			isTrue := atoms.IsSameQ(
				es.Eval(this.GetParts()[1].DeepCopy()),
				atoms.NewSymbol("System`True"),
			)
			for isTrue {
				tmpRes := es.Eval(this.GetParts()[2].DeepCopy())
				retVal, isReturn := tryReturnValue(tmpRes, nil, es)
				if isReturn {
					return retVal
				}
				if isBreak(tmpRes) {
					return atoms.S("Null")
				}
				isTrue = atoms.IsSameQ(
					es.Eval(this.GetParts()[1].DeepCopy()),
					atoms.NewSymbol("System`True"),
				)
			}

			return atoms.NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "CompoundExpression",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			var toReturn expreduceapi.Ex
			for i := 1; i < len(this.GetParts()); i++ {
				toReturn = es.Eval(this.GetParts()[i])
				if es.HasThrown() {
					return es.Thrown()
				}
				if _, isReturn := atoms.HeadAssertion(toReturn, "System`Return"); isReturn {
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
				condRes := es.Eval(this.GetParts()[i])
				resSym, resIsSym := condRes.(*atoms.Symbol)
				if !resIsSym {
					continue
				}
				if resSym.Name == "System`True" {
					return this.GetParts()[i+1]
				}
			}
			return atoms.NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Switch",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) < 4 || len(this.GetParts())%2 != 0 {
				return this
			}
			for i := 2; i < len(this.GetParts()); i += 2 {
				if match, _ := matcher.IsMatchQ(this.GetParts()[1], this.GetParts()[i], matcher.EmptyPD(), es); match {
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
				mis, isOk := iterspec.MultiSpecFromLists(
					es,
					this.GetParts()[2:],
				)
				if isOk {
					// Simulate evaluation within Block[]
					mis.TakeVarSnapshot(es)
					for mis.Cont() {
						mis.DefineCurrent(es)
						res := es.Eval(this.GetParts()[1].DeepCopy())
						if es.HasThrown() {
							return es.Thrown()
						}
						if asReturn, isReturn := atoms.HeadAssertion(res, "System`Return"); isReturn {
							if len(asReturn.GetParts()) < 2 {
								return atoms.NewSymbol("System`Null")
							}
							return asReturn.GetParts()[1]
						}
						mis.Next()
					}
					mis.RestoreVarSnapshot(es)
					return atoms.NewSymbol("System`Null")
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{Name: "For"})
	return
}
