//go:generate goyacc -p Calc -fs -o interp.go interp.y
//go:generate golex -o tokenizer.go tokenizer.l
//go:generate go-bindata -pkg expreduce -o resources.go resources/...

package expreduce

type ToStringFnType (func(*Expression, string, *String, *Expression) (bool, string))

// A nasty global to keep track of ToString functions. TODO: Fix this.
var toStringFns = make(map[string]ToStringFnType)

// The interface that fundamental types must implement.
type Ex interface {
	Eval(es *EvalState) Ex
	String() string
	StringForm(form string, context *String, contextPath *Expression) string
	IsEqual(b Ex, cl *CASLogger) string
	DeepCopy() Ex
	NeedsEval() bool
	Hash() uint64
}
