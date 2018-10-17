package expreduce

import (
	"strings"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func StringForm(def *expreduceapi.Def, defSym *Symbol, params expreduceapi.ToStringParams) string {
	var buffer []string

	attrs := def.attributes.toStrings()
	if len(attrs) > 0 {
		e := E(
			S("Set"),
			E(
				S("Attributes"),
				defSym,
			),
			def.attributes.toSymList(),
		)
		buffer = append(buffer, e.StringForm(params))
	}

	for _, dv := range def.Downvalues {
		e := E(
			S("SetDelayed"),
			dv.Rule.GetParts()[1].(expreduceapi.ExpressionInterface).GetParts()[1],
			dv.Rule.GetParts()[2],
		)
		buffer = append(buffer, e.StringForm(params))
	}

	if def.defaultExpr != nil {
		e := E(
			S("Set"),
			E(
				S("Default"),
				defSym,
			),
			def.defaultExpr,
		)
		buffer = append(buffer, e.StringForm(params))
	}
	return strings.Join(buffer[:], "\n\n")
}
