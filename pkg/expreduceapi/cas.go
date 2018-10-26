//go:generate go-bindata -pkg expreduce -o resources.go resources/...

package expreduceapi

import (
	"github.com/corywalker/expreduce/expreduce/timecounter"
	gologging "github.com/op/go-logging"
)

type evalStateForStringer interface {
	GetStringFn(headStr string) (ToStringFnType, bool)
	// Used by Definition[]
	GetDefined(name string) (Def, bool)
}

type ToStringFnType (func(ExpressionInterface, ToStringParams) (bool, string))
type ToStringParams struct {
	Form         string
	Context      StringInterface
	ContextPath  ExpressionInterface
	PreviousHead string
	Esi          evalStateForStringer
}

// Ex is the interface that fundamental types must implement.
type Ex interface {
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

	Eval(expr Ex) Ex

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
	IsInterrupted() bool
	GetStringDef(name string, defaultVal string) string
	GetListDef(name string) ExpressionInterface
	Throw(e ExpressionInterface)
	HasThrown() bool
	Thrown() ExpressionInterface
	ProcessTopLevelResult(in Ex, out Ex) Ex

	GetLogger() LoggingInterface
	GetTrace() ExpressionInterface
	SetTrace(newTrace ExpressionInterface)
	GetDefinedMap() DefinitionMap
	GetReapSown() ExpressionInterface
	SetReapSown(ex ExpressionInterface)

	GetTimeCounter() *timecounter.Group
}

type ExpressionInterface interface {
	Ex

	GetParts() []Ex
	SetParts(newParts []Ex)
	ClearHashes()

	Len() int
	Less(i, j int) bool
	Swap(i, j int)
	AppendEx(e Ex)
	AppendExArray(e []Ex)
	HeadStr() string
}

type StringInterface interface {
	Ex

	GetValue() string
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

type EvalFnType (func(ExpressionInterface, EvalStateInterface) Ex)
type Def struct {
	Downvalues  []DownValue
	Attributes  Attributes
	DefaultExpr Ex

	// A function defined here will override downvalues.
	LegacyEvalFn EvalFnType
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
