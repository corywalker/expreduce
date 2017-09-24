package expreduce

func applyWithFn(e *Expression, es *EvalState) (Ex, bool) {
	if len(e.Parts) != 3 {
		return nil, false
	}
	vars, isList := HeadAssertion(e.Parts[1], "System`List")
	if !isList {
		return nil, false
	}
	rules := []*Expression{}
	for _, vDef := range vars.Parts[1:] {
		set, isSet := HeadAssertion(vDef, "System`Set")
		setDelayed, isSetDelayed := HeadAssertion(vDef, "System`SetDelayed")
		if !(isSet || isSetDelayed) {
			return nil, false
		}
		var setEx *Expression = nil
		ruleHead := ""
		if isSet {
			setEx = set
			ruleHead = "System`Rule"
		} else {
			setEx = setDelayed
			ruleHead = "System`RuleDelayed"
		}
		if len(setEx.Parts) != 3 {
			return nil, false
		}
		rules = append(rules, NewExpression([]Ex{
			NewSymbol(ruleHead),
			setEx.Parts[1],
			setEx.Parts[2],
		}))
	}
	return rulesReplaceAll(e.Parts[2], rules, es), true
}

func GetFlowControlDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "If",
		// WARNING: Watch out for putting rules here. It can interfere with how
		// Return works.
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) > 4 || len(this.Parts) < 3 {
				return this
			}
			var falseVal Ex = NewSymbol("System`Null")
			if len(this.Parts) == 4 {
				falseVal = this.Parts[3]
			}

			var isequal string = this.Parts[1].IsEqual(NewSymbol("System`True"), &es.CASLogger)
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return this.Parts[2]
			} else if isequal == "EQUAL_FALSE" {
				return falseVal
			}

			return NewExpression([]Ex{NewSymbol("System`Error"), NewString("Unexpected equality return value.")})
		},
	})
	defs = append(defs, Definition{
		Name: "While",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			isequal := this.Parts[1].DeepCopy().Eval(es).IsEqual(NewSymbol("System`True"), &es.CASLogger)
			cont := isequal == "EQUAL_TRUE"
			for cont {
				tmpRes := this.Parts[2].DeepCopy().Eval(es)
				retVal, isReturn := tryReturnValue(tmpRes, es)
				if isReturn {
					return retVal
				}
				isequal = this.Parts[1].DeepCopy().Eval(es).IsEqual(NewSymbol("System`True"), &es.CASLogger)
				cont = isequal == "EQUAL_TRUE"
			}

			if isequal == "EQUAL_UNK" {
				return NewExpression([]Ex{NewSymbol("System`Error"), NewString("Encountered EQUAL_UNK when evaluating test for the While.")})
			} else if isequal == "EQUAL_TRUE" {
				return NewSymbol("System`Null")
			} else if isequal == "EQUAL_FALSE" {
				return NewSymbol("System`Null")
			}

			return NewExpression([]Ex{NewSymbol("System`Error"), NewString("Unexpected equality return value.")})
		},
	})
	defs = append(defs, Definition{
		Name: "CompoundExpression",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			var toReturn Ex
			for i := 1; i < len(this.Parts); i++ {
				toReturn = this.Parts[i].Eval(es)
				if es.HasThrown() {
					return es.thrown
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
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts)%2 != 1 {
				return this
			}
			for i := 1; i < len(this.Parts); i += 2 {
				condRes := this.Parts[i].Eval(es)
				resSym, resIsSym := condRes.(*Symbol)
				if !resIsSym {
					continue
				}
				if resSym.Name == "System`True" {
					return this.Parts[i+1]
				}
			}
			return NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Switch",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) < 4 || len(this.Parts)%2 != 0 {
				return this
			}
			for i := 2; i < len(this.Parts); i += 2 {
				if match, _ := IsMatchQ(this.Parts[1], this.Parts[i], EmptyPD(), es); match {
					return this.Parts[i+1]
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "With",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			res, ok := applyWithFn(this, es)
			if !ok {
				return this
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Do",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) >= 3 {
				mis, isOk := multiIterSpecFromLists(es, this.Parts[2:])
				if isOk {
					// Simulate evaluation within Block[]
					mis.takeVarSnapshot(es)
					for mis.cont() {
						mis.defineCurrent(es)
						res := this.Parts[1].DeepCopy().Eval(es)
						if es.HasThrown() {
							return es.thrown
						}
						if asReturn, isReturn := HeadAssertion(res, "System`Return"); isReturn {
							if len(asReturn.Parts) < 2 {
								return NewSymbol("System`Null")
							}
							return asReturn.Parts[1]
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
	return
}
