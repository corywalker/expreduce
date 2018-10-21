package atoms

import "github.com/corywalker/expreduce/pkg/expreduceapi"

func DefaultStringFormArgs() (*String, expreduceapi.ExpressionInterface) {
	return NewString("Global`"), NewExpression([]expreduceapi.Ex{
		NewSymbol("System`List"),
		NewString("System`"),
	})
}
