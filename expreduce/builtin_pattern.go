package expreduce

import (
	"bytes"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/matcher"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func toStringBlankType(
	repr string,
	parts []expreduceapi.Ex,
	params expreduceapi.ToStringParams,
) (bool, string) {
	if params.Form == "FullForm" {
		return false, ""
	}
	if len(parts) == 1 {
		return true, repr
	} else if len(parts) == 2 {
		var buffer bytes.Buffer
		buffer.WriteString(repr)
		buffer.WriteString(parts[1].StringForm(params))
		return true, buffer.String()
	}
	return false, ""
}

func getPatternDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "MatchQ",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			if res, _ := matcher.IsMatchQ(this.GetParts()[1], this.GetParts()[2], matcher.EmptyPD(), es); res {
				return atoms.NewSymbol("System`True")
			}
			return atoms.NewSymbol("System`False")
		},
	})
	defs = append(defs, Definition{
		Name: "Pattern",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 3 {
				return false, ""
			}
			if params.Form != "InputForm" && params.Form != "OutputForm" {
				return false, ""
			}
			var buffer bytes.Buffer
			_, blankOk := atoms.HeadAssertion(
				this.GetParts()[2],
				"System`Blank",
			)
			_, bsOk := atoms.HeadAssertion(
				this.GetParts()[2],
				"System`BlankSequence",
			)
			_, bnsOk := atoms.HeadAssertion(
				this.GetParts()[2],
				"System`BlankNullSequence",
			)
			if blankOk || bsOk || bnsOk {
				buffer.WriteString(this.GetParts()[1].StringForm(params))
				buffer.WriteString(this.GetParts()[2].StringForm(params))
			} else {
				buffer.WriteString("(")
				buffer.WriteString(this.GetParts()[1].StringForm(params))
				buffer.WriteString(") : (")
				buffer.WriteString(this.GetParts()[2].StringForm(params))
				buffer.WriteString(")")
			}
			return true, buffer.String()
		},
	})
	defs = append(defs, Definition{
		Name: "Blank",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringBlankType("_", this.GetParts(), params)
		},
	})
	defs = append(defs, Definition{
		Name: "BlankSequence",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringBlankType("__", this.GetParts(), params)
		},
	})
	defs = append(defs, Definition{
		Name: "BlankNullSequence",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringBlankType("___", this.GetParts(), params)
		},
	})
	defs = append(defs, Definition{
		Name: "Except",
	})
	defs = append(defs, Definition{
		Name: "PatternTest",
	})
	defs = append(defs, Definition{
		Name: "Condition",
	})
	defs = append(defs, Definition{
		Name: "Alternatives",
	})
	defs = append(defs, Definition{
		Name: "FreeQ",
	})
	defs = append(defs, Definition{
		Name: "ReplaceList",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			rule, isRule := atoms.HeadAssertion(
				this.GetParts()[2],
				"System`Rule",
			)
			if !isRule {
				return this
			}
			res := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
			)
			mi, cont := matcher.NewMatchIter(
				this.GetParts()[1],
				rule.GetParts()[1],
				matcher.EmptyPD(),
				es,
			)
			for cont {
				matchq, newPd, done := mi.Next()
				cont = !done
				if matchq {
					res.AppendEx(
						matcher.ReplacePD(rule.GetParts()[2], es, newPd),
					)
				}
			}
			return res
		},
	})
	defs = append(defs, Definition{Name: "Repeated"})
	defs = append(defs, Definition{
		Name: "Optional",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 2 {
				return false, ""
			}
			if params.Form != "InputForm" && params.Form != "OutputForm" {
				return false, ""
			}
			var buffer bytes.Buffer
			buffer.WriteString(this.GetParts()[1].StringForm(params))
			buffer.WriteString(".")
			return true, buffer.String()
		},
	})
	defs = append(defs, Definition{
		Name: "Verbatim",
		// Not fully supported. Don't document
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{Name: "HoldPattern"})
	return
}
