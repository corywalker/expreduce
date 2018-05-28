//go:generate go-bindata -pkg expreduce -o resources.go resources/...

package expreduce

type ToStringFnType (func(*Expression, ToStringParams) (bool, string))

// A nasty global to keep track of ToString functions. TODO: Fix this.
var toStringFns = make(map[string]ToStringFnType)

// The interface that fundamental types must implement.
type Ex interface {
	Eval(es *EvalState) Ex
	// TODO(corywalker): Deprecate this function. All stringification should go
	// through StringForm.
	String() string
	StringForm(params ToStringParams) string
	IsEqual(b Ex, cl *CASLogger) string
	DeepCopy() Ex
	Copy() Ex
	NeedsEval() bool
	Hash() uint64
}
