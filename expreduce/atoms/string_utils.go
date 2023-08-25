package atoms

import "github.com/corywalker/expreduce/pkg/expreduceapi"

type fakeEvalState struct{}

func (fes fakeEvalState) GetStringFn(
	headStr string,
) (expreduceapi.ToStringFnType, bool) {
	return nil, false
}

func (fes fakeEvalState) GetDefined(name string) (expreduceapi.Def, bool) {
	return expreduceapi.Def{}, false
}

func defaultStringParams() expreduceapi.ToStringParams {
	context := NewString("Global`")
	contextPath := NewExpression([]expreduceapi.Ex{
		NewSymbol("System`List"),
		NewString("System`"),
	})
	return expreduceapi.ToStringParams{
		Form:        "InputForm",
		Context:     context,
		ContextPath: contextPath,
		Esi:         fakeEvalState{},
	}
}
