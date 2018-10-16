//go:generate go-bindata -pkg expreduce -o resources.go resources/...

package expreduce

import "github.com/corywalker/expreduce/expreduce/logging"

type ToStringFnType (func(*Expression, ToStringParams) (bool, string))

// The interface that fundamental types must implement.
type Ex interface {
	Eval(es *EvalState) Ex
	// TODO(corywalker): Deprecate this function. All stringification should go
	// through StringForm.
	String(es *EvalState) string
	StringForm(params ToStringParams) string
	IsEqual(b Ex, cl *logging.CASLogger) string
	DeepCopy() Ex
	Copy() Ex
	NeedsEval() bool
	Hash() uint64
}
