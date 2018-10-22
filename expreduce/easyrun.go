package expreduce

import (
	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func EasyRun(in string, es expreduceapi.EvalStateInterface) string {
	context, ContextPath := ActualStringFormArgs(es)
	stringParams := expreduceapi.ToStringParams{
		Form:        "InputForm",
		Context:     context,
		ContextPath: ContextPath,
		Esi:         es,
	}
	return parser.EvalInterp(in, es).StringForm(stringParams)
}
