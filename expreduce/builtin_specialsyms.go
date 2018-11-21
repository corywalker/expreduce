package expreduce

import (
	"fmt"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func getSpecialSymsDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "Infinity",
	})
	defs = append(defs, Definition{
		Name: "ComplexInfinity",
	})
	defs = append(defs, Definition{
		Name: "Indeterminate",
	})
	defs = append(defs, Definition{
		Name: "Pi",
	})
	defs = append(defs, Definition{
		Name: "E",
	})
	defs = append(defs, Definition{
		Name: "Subscript",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if this.Len() == 2 {
				nextParams := params
				nextParams.PreviousHead = "<TOPLEVEL>"
				if params.Form == "TeXForm" {
					return true, fmt.Sprintf(
						"{%v}_{%v}",
						this.GetPart(1).StringForm(nextParams),
						this.GetPart(2).StringForm(nextParams),
					)
				}
			}
			return false, ""
		},
	})
	return
}
