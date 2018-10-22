package expreduce

import (
	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func EasyRun(in string, es expreduceapi.EvalStateInterface) string {
	context, contextPath := actualStringFormArgs(es)
	stringParams := expreduceapi.ToStringParams{
		Form:        "InputForm",
		Context:     context,
		ContextPath: contextPath,
		Esi:         es,
	}
	return parser.EvalInterp(in, es).StringForm(stringParams)
}
