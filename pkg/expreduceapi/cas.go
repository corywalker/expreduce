//go:generate go-bindata -pkg expreduce -o resources.go resources/...

package expreduceapi

import (
	gologging "github.com/op/go-logging"
)

type ToStringFnType (func(ExpressionInterface, ToStringParams) (bool, string))
type ToStringParams struct {
	form         string
	context      StringInterface
	ContextPath  ExpressionInterface
	PreviousHead string
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

type LoggingInterface interface {
	Debugf(fmt string, args ...interface{})
	Infof(fmt string, args ...interface{})
	Errorf(fmt string, args ...interface{})
	DebugOn(level gologging.Level)
	DebugOff()
	SetDebugState(newState bool)
	IsProfiling() bool
	SetProfiling(profiling bool)
	SetUpLogging()
}

type EvalStateInterface interface {
	LoggingInterface

	GetDefined(name string) (Def, bool)
	GetStringFn(headStr string) (ToStringFnType, bool)
	Init(loadAllDefs bool)
	IsDef(name string) bool
	GetDef(name string, lhs Ex) (Ex, bool, ExpressionInterface)
	GetSymDef(name string) (Ex, bool)
	MarkSeen(name string)
	Define(lhs Ex, rhs Ex)
	ClearAll()
	Clear(name string)
	GetDefinedSnapshot() DefinitionMap
	IsFrozen() bool
	SetFrozen(frozen bool)
	GetStringDef(name string, defaultVal string) string
	GetListDef(name string) ExpressionInterface
	Throw(e ExpressionInterface)
	HasThrown() bool
	ProcessTopLevelResult(in Ex, out Ex) Ex
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
	Rule        ExpressionInterface
	Specificity int
}

type Def struct {
	Downvalues  []DownValue
	attributes  Attributes
	DefaultExpr Ex

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
