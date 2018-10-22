package atoms

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func defaultStringFormArgs() (*String, expreduceapi.ExpressionInterface) {
	return NewString("Global`"), NewExpression([]expreduceapi.Ex{
		NewSymbol("System`List"),
		NewString("System`"),
	})
}
