//go:generate go-bindata -pkg expreduce -o resources.go resources/...

package expreduceapi

import (
	"github.com/corywalker/expreduce/expreduce/logging"
	"github.com/corywalker/expreduce/expreduce/timecounter"
	"github.com/orcaman/concurrent-map"
)

type ToStringFnType (func(*Expression, ToStringParams) (bool, string))
type ToStringParams struct {
	form         string
	context      *String
	contextPath  *Expression
	previousHead string
	// Used by Definition[]
	esi EvalStateInterface
}

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

type EvalState struct {
	// Embedded type for logging
	logging.CASLogger

	defined     definitionMap
	trace       *Expression
	NoInit      bool
	timeCounter timecounter.Group
	freeze      bool
	thrown      *Expression
	reapSown    *Expression
	interrupted bool
	toStringFns map[string]ToStringFnType
}

type EvalStateInterface interface {
	GetDefined(name string) (Def, bool)
	GetStringFn(headStr string) (ToStringFnType, bool)
}

type Expression struct {
	Parts                 []Ex
	needsEval             bool
	correctlyInstantiated bool
	evaledHash            uint64
	cachedHash            uint64
}

type String struct {
	Val string
}

type definitionMap struct {
	internalMap cmap.ConcurrentMap
}

type DownValue struct {
	rule        *Expression
	specificity int
}

type Def struct {
	downvalues  []DownValue
	attributes  Attributes
	defaultExpr Ex

	// A function defined here will override downvalues.
	legacyEvalFn (func(*Expression, *EvalState) Ex)
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

