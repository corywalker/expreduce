package expreduce

import (
	"strings"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func (def *expreduceapi.Def) StringForm(defSym *Symbol, params expreduceapi.ToStringParams) string {
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

	for _, dv := range def.downvalues {
		e := E(
			S("SetDelayed"),
			dv.rule.Parts[1].(*expreduceapi.Expression).Parts[1],
			dv.rule.Parts[2],
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
