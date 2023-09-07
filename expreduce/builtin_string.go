package expreduce

import (
	"encoding/base64"
	"fmt"
	"strings"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/graphics"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func getStringDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "ToString",
		// For some reason this is fast for StringJoin[Table["x", {k,2000}]/.List->Sequence]
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			formAsSymbol, formIsSymbol := this.GetParts()[2].(*atoms.Symbol)
			if !formIsSymbol {
				return this
			}

			// Do not implement FullForm here. It is not officially supported
			if formAsSymbol.Name != "System`InputForm" &&
				formAsSymbol.Name != "System`OutputForm" &&
				formAsSymbol.Name != "System`FullForm" &&
				formAsSymbol.Name != "System`TeXForm" {
				return this
			}

			context, contextPath := actualStringFormArgs(es)
			stringParams := expreduceapi.ToStringParams{
				Form:         formAsSymbol.Name[7:],
				Context:      context,
				ContextPath:  contextPath,
				PreviousHead: "<TOPLEVEL>",
				Esi:          es,
			}
			return atoms.NewString(this.GetParts()[1].StringForm(stringParams))
		},
	})
	defs = append(defs, Definition{
		Name: "StringJoin",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			return toStringInfix(this.GetParts()[1:], " <> ", "", params)
		},
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			toReturn := ""
			for _, e := range this.GetParts()[1:] {
				asStr, isStr := e.(*atoms.String)
				if !isStr {
					return this
				}
				toReturn += asStr.Val
			}
			return atoms.NewString(toReturn)
		},
	})
	defs = append(defs, Definition{
		Name:     "Infix",
		toString: toStringInfixFn,
	})
	defs = append(defs, Definition{
		Name: "StringLength",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			asStr, isStr := this.GetParts()[1].(*atoms.String)
			if !isStr {
				return this
			}
			return atoms.NewInt(int64(len(asStr.Val)))
		},
	})
	defs = append(defs, Definition{
		Name: "StringTake",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			asStr, isStr := this.GetParts()[1].(*atoms.String)
			if !isStr {
				return this
			}
			asList, isList := atoms.HeadAssertion(
				this.GetParts()[2],
				"System`List",
			)
			if !isList || len(asList.GetParts()) != 3 {
				return this
			}
			sInt, sIsInt := asList.GetParts()[1].(*atoms.Integer)
			eInt, eIsInt := asList.GetParts()[2].(*atoms.Integer)
			if !sIsInt || !eIsInt {
				return this
			}
			s := int(sInt.Val.Int64() - 1)
			e := int(eInt.Val.Int64() - 1)
			if s < 0 || e >= len(asStr.Val) {
				return this
			}
			if e < s {
				return atoms.NewString("")
			}
			return atoms.NewString(asStr.Val[s : e+1])
		},
	})
	defs = append(defs, Definition{
		Name: "StringReplace",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}
			asStr, isStr := this.GetParts()[1].(*atoms.String)
			if !isStr {
				return this
			}
			asRule, isRule := atoms.HeadAssertion(
				this.GetParts()[2],
				"System`Rule",
			)
			if !isRule || len(asRule.GetParts()) != 3 {
				return this
			}
			bStr, bIsStr := asRule.GetParts()[1].(*atoms.String)
			aStr, aIsStr := asRule.GetParts()[2].(*atoms.String)
			if !bIsStr || !aIsStr {
				return this
			}
			return atoms.NewString(
				strings.Replace(asStr.Val, bStr.Val, aStr.Val, -1),
			)
		},
	})
	defs = append(defs, Definition{
		Name: "ExportString",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 && len(this.GetParts()) != 4 {
				return this
			}
			formatAsStr, formatIsStr := this.GetParts()[2].(*atoms.String)
			if !formatIsStr {
				return this
			}
			format := strings.ToLower(formatAsStr.Val)

			if format == "png" {
				chartAsPNG, err := graphics.RenderAsPNG(this.GetPart(1))
				if err != nil {
					fmt.Printf("Encountered error during PNG render: %v\n", err)
					return atoms.NewSymbol("System`$Failed")
				}
				return atoms.NewString(chartAsPNG)
			}

			asStr, isStr := this.GetParts()[1].(*atoms.String)
			if !isStr {
				return this
			}
			if format == "base64" {
				encoded := base64.StdEncoding.EncodeToString([]byte(asStr.Val))
				return atoms.NewString(encoded + "\n")
			}
			return atoms.NewSymbol("System`$Failed")
		},
	})
	return
}
