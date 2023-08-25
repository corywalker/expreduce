package expreduce

import (
	"strings"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func stringForm(
	def *expreduceapi.Def,
	defSym *atoms.Symbol,
	params expreduceapi.ToStringParams,
) string {
	var buffer []string

	attrs := atoms.AttrsToStrings(&def.Attributes)
	if len(attrs) > 0 {
		e := atoms.E(
			atoms.S("Set"),
			atoms.E(
				atoms.S("Attributes"),
				defSym,
			),
			atoms.AttrsToSymList(&def.Attributes),
		)
		buffer = append(buffer, e.StringForm(params))
	}

	for _, dv := range def.Downvalues {
		e := atoms.E(
			atoms.S("SetDelayed"),
			dv.Rule.GetParts()[1].(expreduceapi.ExpressionInterface).GetParts()[1],
			dv.Rule.GetParts()[2],
		)
		buffer = append(buffer, e.StringForm(params))
	}

	if def.DefaultExpr != nil {
		e := atoms.E(
			atoms.S("Set"),
			atoms.E(
				atoms.S("Default"),
				defSym,
			),
			def.DefaultExpr,
		)
		buffer = append(buffer, e.StringForm(params))
	}
	return strings.Join(buffer[:], "\n\n")
}
