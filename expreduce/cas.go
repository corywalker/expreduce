//go:generate go-bindata -pkg expreduce -o resources.go resources/...

package expreduce

type ToStringFnType (func(*Expression, ToStringParams) (bool, string))

// The interface that fundamental types must implement.
type Ex interface {
	Eval(es *EvalState) Ex
	// TODO(corywalker): Deprecate this function. All stringification should go
	// through StringForm.
	String(es EvalStateInterface) string
	StringForm(params ToStringParams) string
	IsEqual(b Ex) string
	DeepCopy() Ex
	Copy() Ex
	NeedsEval() bool
	Hash() uint64
}

type EvalStateInterface interface {
	GetDefined(name string) (Def, bool)
	GetStringFn(headStr string) (ToStringFnType, bool)
}
