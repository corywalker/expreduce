package expreduce

import (
	"encoding/base64"
	"strings"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func GetStringDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "ToString",
		// For some reason this is fast for StringJoin[Table["x", {k,2000}]/.List->Sequence]
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			formAsSymbol, formIsSymbol := this.GetParts()[2].(*Symbol)
			if !formIsSymbol {
				return this
			}

			// Do not implement FullForm here. It is not officially supported
			if formAsSymbol.Name != "System`InputForm" && formAsSymbol.Name != "System`OutputForm" && formAsSymbol.Name != "System`FullForm" && formAsSymbol.Name != "System`TeXForm" {
				return this
			}

			context, ContextPath := ActualStringFormArgs(es)
			stringParams := expreduceapi.ToStringParams{
				Form:         formAsSymbol.Name[7:],
				Context:      context,
				ContextPath:  ContextPath,
				PreviousHead: "<TOPLEVEL>",
				Esi:          es,
			}
			return NewString(this.GetParts()[1].StringForm(stringParams))
		},
	})
	defs = append(defs, Definition{
		Name: "StringJoin",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return ToStringInfix(this.GetParts()[1:], " <> ", "", params)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			toReturn := ""
			for _, e := range this.GetParts()[1:] {
				asStr, isStr := e.(*String)
				if !isStr {
					return this
				}
				toReturn += asStr.Val
			}
			return NewString(toReturn)
		},
	})
	defs = append(defs, Definition{
		Name:     "Infix",
		toString: ToStringInfixFn,
	})
	defs = append(defs, Definition{
		Name: "StringLength",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			asStr, isStr := this.GetParts()[1].(*String)
			if !isStr {
				return this
			}
			return NewInt(int64(len(asStr.Val)))
		},
	})
	defs = append(defs, Definition{
		Name: "StringTake",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			asStr, isStr := this.GetParts()[1].(*String)
			if !isStr {
				return this
			}
			asList, isList := HeadAssertion(this.GetParts()[2], "System`List")
			if !isList || len(asList.GetParts()) != 3 {
				return this
			}
			sInt, sIsInt := asList.GetParts()[1].(*Integer)
			eInt, eIsInt := asList.GetParts()[2].(*Integer)
			if !sIsInt || !eIsInt {
				return this
			}
			s := int(sInt.Val.Int64() - 1)
			e := int(eInt.Val.Int64() - 1)
			if s < 0 || e >= len(asStr.Val) {
				return this
			}
			if e < s {
				return NewString("")
			}
			return NewString(asStr.Val[s : e+1])
		},
	})
	defs = append(defs, Definition{
		Name: "StringReplace",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			asStr, isStr := this.GetParts()[1].(*String)
			if !isStr {
				return this
			}
			asRule, isRule := HeadAssertion(this.GetParts()[2], "System`Rule")
			if !isRule || len(asRule.GetParts()) != 3 {
				return this
			}
			bStr, bIsStr := asRule.GetParts()[1].(*String)
			aStr, aIsStr := asRule.GetParts()[2].(*String)
			if !bIsStr || !aIsStr {
				return this
			}
			return NewString(strings.Replace(asStr.Val, bStr.Val, aStr.Val, -1))
		},
	})
	defs = append(defs, Definition{
		Name: "ExportString",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			asStr, isStr := this.GetParts()[1].(*String)
			if !isStr {
				return this
			}
			formatAsStr, formatIsStr := this.GetParts()[2].(*String)
			if !formatIsStr {
				return this
			}
			format := strings.ToLower(formatAsStr.Val)
			if format == "base64" {
				encoded := base64.StdEncoding.EncodeToString([]byte(asStr.Val))
				return NewString(encoded + "\n")
			}
			return NewSymbol("System`$Failed")
		},
	})
	return
}
