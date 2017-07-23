package expreduce

func getValidRules(ruleArg Ex) (rules []*Expression) {
	rulesRule, ok := HeadAssertion(ruleArg, "System`Rule")
	if !ok {
		rulesRule, ok = HeadAssertion(ruleArg, "System`RuleDelayed")
	}
	if ok {
		return []*Expression{rulesRule}
	}

	// Also handle a list of Rules
	asList, isList := HeadAssertion(ruleArg, "System`List")
	if isList {
		for i := 1; i < len(asList.Parts); i++ {
			rulesRule, ok := HeadAssertion(asList.Parts[i], "System`Rule")
			if !ok {
				rulesRule, ok = HeadAssertion(asList.Parts[i], "System`RuleDelayed")
			}
			if ok {
				rules = append(rules, rulesRule)
			}
		}
	}
	return
}

func getReplacementDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "ReplaceAll",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " /. ", true, "", "", form, context, contextPath)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			rules := getValidRules(this.Parts[2])
			if len(rules) == 0 {
				return this
			}
			toReturn := this.Parts[1]
			for _, rule := range rules {
				toReturn = ReplaceAll(toReturn, rule, es, EmptyPD(), "")
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Replace",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			rules := getValidRules(this.Parts[2])
			if len(rules) == 0 {
				return this
			}
			for _, rule := range rules {
				toReturn, replaced := Replace(this.Parts[1], rule, es)
				if replaced {
					return toReturn
				}
			}
			return this.Parts[1]
		},
	})
	defs = append(defs, Definition{
		Name: "ReplaceRepeated",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " //. ", true, "", "", form, context, contextPath)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}
			es.Infof("Starting ReplaceRepeated.")
			isSame := false
			oldEx := this.Parts[1]
			es.Infof("In ReplaceRepeated. Initial expr: %v", oldEx)
			for !isSame {
				newEx := (NewExpression([]Ex{
					&Symbol{"System`ReplaceAll"},
					oldEx,
					this.Parts[2],
				})).Eval(es)
				es.Infof("In ReplaceRepeated. New expr: %v", newEx)

				if IsSameQ(oldEx, newEx, &es.CASLogger) {
					isSame = true
				}
				oldEx = newEx
			}
			return oldEx
		},
	})
	defs = append(defs, Definition{
		Name: "Rule",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " -> ", true, "", "", form, context, contextPath)
		},
	})
	defs = append(defs, Definition{
		Name: "RuleDelayed",
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " :> ", true, "", "", form, context, contextPath)
		},
	})
	return
}
