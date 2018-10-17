//go:generate go-bindata -pkg expreduce -o resources.go resources/...

package expreduceapi

type ToStringFnType (func(ExpressionInterface, ToStringParams) (bool, string))
type ToStringParams struct {
	form         string
	context      StringInterface
	contextPath  ExpressionInterface
	previousHead string
	// Used by Definition[]
	esi EvalStateInterface
}

// The interface that fundamental types must implement.
type Ex interface {
	Eval(es EvalStateInterface) Ex
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

type ExpressionInterface interface {
	Ex

	GetParts() []Ex
}

type StringInterface interface {
	Ex
}

type DefinitionMap interface {
	Set(key string, value Def)
	Get(key string) (Def, bool)
	GetDef(key string) Def
	LockKey(key string)
	UnlockKey(key string)
	CopyDefs() DefinitionMap
}

type DownValue struct {
	rule        ExpressionInterface
	specificity int
}

type Def struct {
	downvalues  []DownValue
	attributes  Attributes
	defaultExpr Ex

	// A function defined here will override downvalues.
	legacyEvalFn (func(ExpressionInterface, EvalStateInterface) Ex)
}

// Functions for working with the attributes of symbols:
type Attributes struct {
	Orderless       bool
	Flat            bool
	OneIdentity     bool
	Listable        bool
	Constant        bool
	NumericFunction bool
	Protected       bool
	Locked          bool
	ReadProtected   bool
	HoldFirst       bool
	HoldRest        bool
	HoldAll         bool
	HoldAllComplete bool
	NHoldFirst      bool
	NHoldRest       bool
	NHoldAll        bool
	SequenceHold    bool
	Temporary       bool
	Stub            bool
}
