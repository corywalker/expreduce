package expreduce

func GetFlowControlDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "If",
		// WARNING: Watch out for putting rules here. It can interfere with how
		// Return works.
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) > 4 || len(this.Parts) < 3 {
				return this
			}
			var falseVal Ex = &Symbol{"System`Null"}
			if len(this.Parts) == 4 {
				falseVal = this.Parts[3]
			}

			var isequal string = this.Parts[1].IsEqual(&Symbol{"System`True"}, &es.CASLogger)
			if isequal == "EQUAL_UNK" {
				return this
			} else if isequal == "EQUAL_TRUE" {
				return this.Parts[2]
			} else if isequal == "EQUAL_FALSE" {
				return falseVal
			}

			return NewExpression([]Ex{&Symbol{"System`Error"}, &String{"Unexpected equality return value."}})
		},
	})
	defs = append(defs, Definition{
		Name: "While",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			isequal := this.Parts[1].DeepCopy().Eval(es).IsEqual(&Symbol{"System`True"}, &es.CASLogger)
			cont := isequal == "EQUAL_TRUE"
			for cont {
				tmpRes := this.Parts[2].DeepCopy().Eval(es)
				retVal, isReturn := tryReturnValue(tmpRes)
				if isReturn {
					return retVal
				}
				isequal = this.Parts[1].DeepCopy().Eval(es).IsEqual(&Symbol{"System`True"}, &es.CASLogger)
				cont = isequal == "EQUAL_TRUE"
			}

			if isequal == "EQUAL_UNK" {
				return NewExpression([]Ex{&Symbol{"System`Error"}, &String{"Encountered EQUAL_UNK when evaluating test for the While."}})
			} else if isequal == "EQUAL_TRUE" {
				return &Symbol{"System`Null"}
			} else if isequal == "EQUAL_FALSE" {
				return &Symbol{"System`Null"}
			}

			return NewExpression([]Ex{&Symbol{"System`Error"}, &String{"Unexpected equality return value."}})
		},
	})
	defs = append(defs, Definition{
		Name: "CompoundExpression",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			var toReturn Ex
			for i := 1; i < len(this.Parts); i++ {
				toReturn = this.Parts[i].Eval(es)
				if _, isReturn := HeadAssertion(toReturn, "System`Return"); isReturn {
					return toReturn
				}
			}
			return toReturn
		},
	})
	// https://mathematica.stackexchange.com/questions/29353/how-does-return-work
	defs = append(defs, Definition{
		Name: "Return",
	})
	return
}
