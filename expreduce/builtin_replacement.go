package expreduce

import (
	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/matcher"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func getValidRules(
	ruleArg expreduceapi.Ex,
) (rules []expreduceapi.ExpressionInterface) {
	rulesRule, ok := atoms.HeadAssertion(ruleArg, "System`Rule")
	if !ok {
		rulesRule, ok = atoms.HeadAssertion(ruleArg, "System`RuleDelayed")
	}
	if ok {
		return []expreduceapi.ExpressionInterface{rulesRule}
	}

	// Also handle a list of Rules
	asList, isList := atoms.HeadAssertion(ruleArg, "System`List")
	if isList {
		for i := 1; i < len(asList.GetParts()); i++ {
			rulesRule, ok := atoms.HeadAssertion(
				asList.GetParts()[i],
				"System`Rule",
			)
			if !ok {
				rulesRule, ok = atoms.HeadAssertion(
					asList.GetParts()[i],
					"System`RuleDelayed",
				)
			}
			if ok {
				rules = append(rules, rulesRule)
			}
		}
	}
	return
}

func rulesReplaceAll(
	e expreduceapi.Ex,
	rules []expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	// TODO: fix the case where ReplaceAll[{x},{x->y,y->z}] returns incorrectly.
	toReturn := e
	for _, rule := range rules {
		toReturn = replaceAll(toReturn, rule, es, matcher.EmptyPD(), "")
	}
	return toReturn
}

func rulesReplace(
	e expreduceapi.Ex,
	rules []expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
) (expreduceapi.Ex, bool) {
	for _, rule := range rules {
		res, replaced := replace(e, rule, es)
		if replaced {
			return res, true
		}
	}
	return e, false
}

func replaceParts(
	e expreduceapi.Ex,
	rules []expreduceapi.ExpressionInterface,
	part expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	expr, isExpr := e.(expreduceapi.ExpressionInterface)
	if !isExpr {
		return e
	}
	res := atoms.E(expr.GetParts()[0])
	part.AppendEx(atoms.NewInt(0))
	dirty := false
	for i, p := range expr.GetParts()[1:] {
		part.GetParts()[len(part.GetParts())-1] = atoms.NewInt(int64(i + 1))
		repVal, replaced := rulesReplace(part, rules, es)
		if !replaced && len(part.GetParts()) == 2 {
			repVal, replaced = rulesReplace(part.GetParts()[1], rules, es)
		}
		if replaced {
			res.AppendEx(repVal)
			dirty = true
		} else {
			newVal := replaceParts(p, rules, part, es)
			res.AppendEx(newVal)
			if newVal != p {
				dirty = true
			}
		}
	}
	part.SetParts(part.GetParts()[:len(part.GetParts())-1])
	if !dirty {
		return e
	}
	return res
}

func getReplacementDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "ReplaceAll",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 3 {
				return false, ""
			}
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" /. ",
				"",
				true,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			rules := getValidRules(this.GetParts()[2])
			return rulesReplaceAll(this.GetParts()[1], rules, es)
		},
	})
	defs = append(defs, Definition{
		Name: "Replace",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			rules := getValidRules(this.GetParts()[2])
			if len(rules) == 0 {
				return this
			}
			for _, rule := range rules {
				toReturn, replaced := replace(this.GetParts()[1], rule, es)
				if replaced {
					return toReturn
				}
			}
			return this.GetParts()[1]
		},
	})
	defs = append(defs, Definition{
		Name: "ReplaceRepeated",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 3 {
				return false, ""
			}
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" //. ",
				"",
				true,
				"",
				"",
				params,
			)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			es.Infof("Starting ReplaceRepeated.")
			isSame := false
			oldEx := this.GetParts()[1]
			es.Infof("In ReplaceRepeated. Initial expr: %v", oldEx)
			for !isSame {
				newEx :=

					es.Eval((atoms.NewExpression([]expreduceapi.Ex{
						atoms.NewSymbol("System`ReplaceAll"),
						oldEx,
						this.GetParts()[2],
					})))

				es.Infof("In ReplaceRepeated. New expr: %v", newEx)

				if atoms.IsSameQ(oldEx, newEx) {
					isSame = true
				}
				oldEx = newEx
			}
			return oldEx
		},
	})
	defs = append(defs, Definition{
		Name: "Rule",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 3 {
				return false, ""
			}
			delim := " -> "
			if params.Form == "TeXForm" {
				delim = "\\to "
			}
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				delim,
				"System`Rule",
				false,
				"",
				"",
				params,
			)
		},
	})
	defs = append(defs, Definition{
		Name: "RuleDelayed",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 3 {
				return false, ""
			}
			delim := " :> "
			if params.Form == "TeXForm" {
				delim = ":\\to "
			}
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				delim,
				"System`RuleDelayed",
				false,
				"",
				"",
				params,
			)
		},
	})
	defs = append(defs, Definition{
		Name: "ReplacePart",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			rules, isList := atoms.HeadAssertion(
				this.GetParts()[2],
				"System`List",
			)
			if !isList {
				return this
			}
			exprRules := [](expreduceapi.ExpressionInterface){}
			for _, rulesPart := range rules.GetParts()[1:] {
				rule, isRule := atoms.HeadAssertion(rulesPart, "System`Rule")
				if !isRule {
					return this
				}
				exprRules = append(exprRules, rule)
			}
			return replaceParts(
				this.GetParts()[1],
				exprRules,
				atoms.E(atoms.S("List")),
				es,
			)
		},
	})
	return
}
