package expreduce

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func getValidRules(ruleArg expreduceapi.Ex) (rules []*expreduceapi.Expression) {
	rulesRule, ok := HeadAssertion(ruleArg, "System`Rule")
	if !ok {
		rulesRule, ok = HeadAssertion(ruleArg, "System`RuleDelayed")
	}
	if ok {
		return []*expreduceapi.Expression{rulesRule}
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

func rulesReplaceAll(e expreduceapi.Ex, rules []*expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
	// TODO: fix the case where ReplaceAll[{x},{x->y,y->z}] returns incorrectly.
	toReturn := e
	for _, rule := range rules {
		toReturn = ReplaceAll(toReturn, rule, es, EmptyPD(), "")
	}
	return toReturn
}

func rulesReplace(e expreduceapi.Ex, rules []*expreduceapi.Expression, es *expreduceapi.EvalState) (expreduceapi.Ex, bool) {
	for _, rule := range rules {
		res, replaced := Replace(e, rule, es)
		if replaced {
			return res, true
		}
	}
	return e, false
}

func replaceParts(e expreduceapi.Ex, rules []*expreduceapi.Expression, part *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
	expr, isExpr := e.(*expreduceapi.Expression)
	if !isExpr {
		return e
	}
	res := E(expr.Parts[0])
	part.Parts = append(part.Parts, NewInt(0))
	dirty := false
	for i, p := range expr.Parts[1:] {
		part.Parts[len(part.Parts)-1] = NewInt(int64(i + 1))
		repVal, replaced := rulesReplace(part, rules, es)
		if !replaced && len(part.Parts) == 2 {
			repVal, replaced = rulesReplace(part.Parts[1], rules, es)
		}
		if replaced {
			res.Parts = append(res.Parts, repVal)
			dirty = true
		} else {
			newVal := replaceParts(p, rules, part, es)
			res.Parts = append(res.Parts, newVal)
			if newVal != p {
				dirty = true
			}
		}
	}
	part.Parts = part.Parts[:len(part.Parts)-1]
	if !dirty {
		return e
	}
	return res
}

func getReplacementDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "ReplaceAll",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " /. ", "", true, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}

			rules := getValidRules(this.Parts[2])
			if len(rules) == 0 {
				return this
			}
			return rulesReplaceAll(this.Parts[1], rules, es)
		},
	})
	defs = append(defs, Definition{
		Name: "Replace",
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
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
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " //. ", "", true, "", "", params)
		},
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}
			es.Infof("Starting ReplaceRepeated.")
			isSame := false
			oldEx := this.Parts[1]
			es.Infof("In ReplaceRepeated. Initial expr: %v", oldEx)
			for !isSame {
				newEx := (NewExpression([]expreduceapi.Ex{
					NewSymbol("System`ReplaceAll"),
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
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			delim := " -> "
			if params.form == "TeXForm" {
				delim = "\\to "
			}
			return ToStringInfixAdvanced(this.Parts[1:], delim, "System`Rule", false, "", "", params)
		},
	})
	defs = append(defs, Definition{
		Name: "RuleDelayed",
		toString: func(this *expreduceapi.Expression, params ToStringParams) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			delim := " :> "
			if params.form == "TeXForm" {
				delim = ":\\to "
			}
			return ToStringInfixAdvanced(this.Parts[1:], delim, "System`RuleDelayed", false, "", "", params)
		},
	})
	defs = append(defs, Definition{
		Name: "ReplacePart",
		legacyEvalFn: func(this *expreduceapi.Expression, es *expreduceapi.EvalState) expreduceapi.Ex {
			if len(this.Parts) != 3 {
				return this
			}
			rules, isList := HeadAssertion(this.Parts[2], "System`List")
			if !isList {
				return this
			}
			exprRules := [](*expreduceapi.Expression){}
			for _, rulesPart := range rules.Parts[1:] {
				rule, isRule := HeadAssertion(rulesPart, "System`Rule")
				if !isRule {
					return this
				}
				exprRules = append(exprRules, rule)
			}
			return replaceParts(this.Parts[1], exprRules, E(S("List")), es)
		},
	})
	return
}
