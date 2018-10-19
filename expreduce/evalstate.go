package expreduce

import (
	"fmt"
	"log"
	"os"
	"os/signal"
	"strings"
	"time"

	"github.com/corywalker/expreduce/expreduce/logging"
	"github.com/corywalker/expreduce/expreduce/timecounter"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type EvalState struct {
	// Embedded type for logging
	logging.CASLogger

	defined     expreduceapi.DefinitionMap
	trace       expreduceapi.ExpressionInterface
	NoInit      bool
	timeCounter timecounter.Group
	freeze      bool
	thrown      expreduceapi.ExpressionInterface
	reapSown    expreduceapi.ExpressionInterface
	interrupted bool
	toStringFns map[string]expreduceapi.ToStringFnType
}

func (es *EvalState) GetDefined(name string) (expreduceapi.Def, bool) {
	return es.GetDefinedMap().Get(name)
}

func (es *EvalState) GetStringFn(headStr string) (expreduceapi.ToStringFnType, bool) {
	fn, ok := es.toStringFns[headStr]
	return fn, ok
}

func (this *EvalState) Load(def Definition) {
	// TODO: deprecate most of this. We should be using .m files now.
	def.Name = this.GetStringDef("System`$Context", "") + def.Name
	this.MarkSeen(def.Name)
	EvalInterp("$Context = \"Private`\"", this)

	if len(def.Usage) > 0 {
		(NewExpression([]expreduceapi.Ex{
			NewSymbol("System`SetDelayed"),
			NewExpression([]expreduceapi.Ex{
				NewSymbol("System`MessageName"),
				NewSymbol(def.Name),
				NewString("usage"),
			}),

			NewString(def.Usage),
		})).Eval(this)
	}

	newDef, foundDef := this.defined.Get(def.Name)
	if !foundDef {
		newDef = expreduceapi.Def{}
	}

	if def.LegacyEvalFn != nil {
		newDef.LegacyEvalFn = def.LegacyEvalFn
	}
	protectedAttrs := append(def.Attributes, "Protected")
	newDef.Attributes = stringsToAttributes(protectedAttrs)
	if def.Default != "" {
		newDef.DefaultExpr = Interp(def.Default, this)
	}
	if def.toString != nil {
		this.toStringFns[def.Name] = def.toString
	}
	this.defined.Set(def.Name, newDef)
	EvalInterp("$Context = \"System`\"", this)
}

func (es *EvalState) Init(loadAllDefs bool) {
	es.defined = newDefinitionMap()
	es.toStringFns = make(map[string]expreduceapi.ToStringFnType)
	// These are fundamental symbols that affect even the parsing of
	// expressions. We must define them before even the bootstrap definitions.
	es.Define(NewSymbol("System`$Context"), NewString("System`"))
	es.Define(NewSymbol("System`$ContextPath"), NewExpression([]expreduceapi.Ex{
		NewSymbol("System`List"),
		NewString("System`"),
	}))
	es.timeCounter.Init()

	es.NoInit = !loadAllDefs
	if !es.NoInit {
		// Init modules
		// Mark all core builtins as seen in the System Context:
		es.MarkSeen("System`Symbol")
		es.MarkSeen("System`Integer")
		es.MarkSeen("System`Rational")
		es.MarkSeen("System`String")
		es.MarkSeen("System`True")
		es.MarkSeen("System`False")

		es.MarkSeen("System`InputForm")
		es.MarkSeen("System`TeXForm")
		es.MarkSeen("System`OutputForm")
		es.MarkSeen("System`FullForm")
		es.MarkSeen("System`TraditionalForm")
		es.MarkSeen("System`StandardForm")

		es.MarkSeen("System`ESimpleExamples")
		es.MarkSeen("System`EFurtherExamples")
		es.MarkSeen("System`ETests")
		es.MarkSeen("System`EKnownFailures")
		es.MarkSeen("System`EKnownDangerous")
		es.MarkSeen("System`ESameTest")
		es.MarkSeen("System`EStringTest")
		es.MarkSeen("System`EExampleOnlyInstruction")
		es.MarkSeen("System`EComment")
		es.MarkSeen("System`EResetState")
		es.MarkSeen("System`ExpreduceNonConditional")
		es.MarkSeen("System`Debug")
		es.MarkSeen("System`Info")
		es.MarkSeen("System`Notice")
		es.MarkSeen("System`Echo")
		es.MarkSeen("System`Row")

		es.MarkSeen("System`Attributes")
		es.MarkSeen("System`Orderless")
		es.MarkSeen("System`Flat")
		es.MarkSeen("System`OneIdentity")
		es.MarkSeen("System`Listable")
		es.MarkSeen("System`Constant")
		es.MarkSeen("System`NumericFunction")
		es.MarkSeen("System`Protected")
		es.MarkSeen("System`Locked")
		es.MarkSeen("System`ReadProtected")
		es.MarkSeen("System`HoldFirst")
		es.MarkSeen("System`HoldRest")
		es.MarkSeen("System`HoldAll")
		es.MarkSeen("System`HoldAllComplete")
		es.MarkSeen("System`NHoldFirst")
		es.MarkSeen("System`NHoldRest")
		es.MarkSeen("System`NHoldAll")
		es.MarkSeen("System`SequenceHold")
		es.MarkSeen("System`Temporary")
		es.MarkSeen("System`Stub")
		es.MarkSeen("System`$Failed")
		es.MarkSeen("System`$Line")
		es.MarkSeen("System`$PrePrint")
		es.MarkSeen("System`Null")
		es.MarkSeen("System`C")
		es.MarkSeen("System`Complex")
		es.MarkSeen("System`Integers")
		es.MarkSeen("System`Break")
		es.MarkSeen("System`LongForm")
		es.MarkSeen("System`In")
		es.MarkSeen("System`Out")

		es.MarkSeen("System`Exp")
		es.MarkSeen("System`AppellF1")
		es.MarkSeen("System`Hypergeometric2F1")
		es.MarkSeen("System`Erf")
		es.MarkSeen("System`Erfi")
		es.MarkSeen("System`Erfc")
		es.MarkSeen("System`SinIntegral")
		es.MarkSeen("System`CosIntegral")
		es.MarkSeen("System`EllipticE")
		es.MarkSeen("System`EllipticF")
		es.MarkSeen("System`ProductLog")

		es.MarkSeen("System`Cosh")
		es.MarkSeen("System`Sinh")
		es.MarkSeen("System`Tanh")

		es.MarkSeen("System`Sec")
		es.MarkSeen("System`Sech")
		es.MarkSeen("System`Csc")
		es.MarkSeen("System`Csch")
		es.MarkSeen("System`Cot")
		es.MarkSeen("System`Coth")
		es.MarkSeen("System`ArcSin")
		es.MarkSeen("System`ArcSinh")
		es.MarkSeen("System`ArcCos")
		es.MarkSeen("System`ArcCosh")
		es.MarkSeen("System`ArcTan")
		es.MarkSeen("System`ArcTanh")

		es.MarkSeen("System`AbsolutePointSize")
		es.MarkSeen("System`AbsoluteThickness")
		es.MarkSeen("System`AspectRatio")
		es.MarkSeen("System`Automatic")
		es.MarkSeen("System`Axes")
		es.MarkSeen("System`AxesLabel")
		es.MarkSeen("System`AxesOrigin")
		es.MarkSeen("System`Directive")
		es.MarkSeen("System`DisplayFunction")
		es.MarkSeen("System`Frame")
		es.MarkSeen("System`FrameLabel")
		es.MarkSeen("System`FrameTicks")
		es.MarkSeen("System`GoldenRatio")
		es.MarkSeen("System`Graphics")
		es.MarkSeen("System`GrayLevel")
		es.MarkSeen("System`GridLines")
		es.MarkSeen("System`GridLinesStyle")
		es.MarkSeen("System`Line")
		es.MarkSeen("System`Method")
		es.MarkSeen("System`None")
		es.MarkSeen("System`Opacity")
		es.MarkSeen("System`PlotRange")
		es.MarkSeen("System`PlotRangeClipping")
		es.MarkSeen("System`PlotRangePadding")
		es.MarkSeen("System`RGBColor")
		es.MarkSeen("System`Scaled")
		es.MarkSeen("System`Ticks")

		for _, defSet := range GetAllDefinitions() {
			for _, def := range defSet.Defs {
				es.MarkSeen(es.GetStringDef("System`$Context", "") + def.Name)
			}
		}
		// Load bootstrap definitions first.
		for _, defSet := range GetAllDefinitions() {
			for _, def := range defSet.Defs {
				if def.Bootstrap {
					es.Load(def)
				}
			}
		}
		// Load rest of definitions.
		for _, defSet := range GetAllDefinitions() {
			for _, def := range defSet.Defs {
				if !def.Bootstrap {
					es.Load(def)
				}
			}
			fn := fmt.Sprintf("resources/%v.m", defSet.Name)
			data, err := Asset(fn)
			if err == nil {
				EvalInterp("$Context = \"Private`\"", es)
				EvalInterpMany(string(data), fn, es)
				EvalInterp("$Context = \"System`\"", es)
			}
		}
		// System initialization
		fn := "resources/init.m"
		data := MustAsset(fn)
		EvalInterpMany(string(data), fn, es)
	}
	EvalInterp("$Context = \"Global`\"", es)
	EvalInterp("$ContextPath = Append[$ContextPath, \"Global`\"]", es)
	EvalInterp("$ExpreduceContextStack = {\"Global`\"}", es)
}

func NewEvalState() *EvalState {
	var es EvalState
	es.Init(true)

	es.SetUpLogging()
	es.DebugOff()

	signalChan := make(chan os.Signal, 1)
	signal.Notify(signalChan, os.Interrupt)
	go func() {
		for _ = range signalChan {
			es.interrupted = true
		}
	}()

	return &es
}

func NewEvalStateNoLog(loadAllDefs bool) *EvalState {
	var es EvalState
	es.Init(loadAllDefs)
	es.CASLogger.SetDebugState(false)
	return &es
}

func (this *EvalState) IsDef(name string) bool {
	_, isd := this.defined.Get(name)
	return isd
}

func (this *EvalState) GetDef(name string, lhs expreduceapi.Ex) (expreduceapi.Ex, bool, expreduceapi.ExpressionInterface) {
	if !this.IsDef(name) {
		return nil, false, nil
	}
	// Special case for checking simple variable definitions like "a = 5".
	// TODO: Perhaps split out single var values into the Definition to avoid
	// iterating over every one.
	if _, lhsIsSym := lhs.(*Symbol); lhsIsSym {
		for _, def := range this.defined.GetDef(name).Downvalues {
			if hp, hpDef := HeadAssertion(def.Rule.GetParts()[1], "System`HoldPattern"); hpDef {
				if len(hp.GetParts()) == 2 {
					if _, symDef := hp.GetParts()[1].(*Symbol); symDef {
						return def.Rule.GetParts()[2], true, def.Rule
					}
				}
			}
		}
		return nil, false, nil
	}
	this.Debugf("Inside GetDef(\"%s\",%s)", name, lhs)
	for i := range this.defined.GetDef(name).Downvalues {
		def := this.defined.GetDef(name).Downvalues[i].Rule

		defStr, lhsDefStr := "", ""
		started := int64(0)
		if this.IsProfiling() {
			defStr = def.String(this)
			lhsDefStr = lhs.String(this) + defStr
			started = time.Now().UnixNano()
		}

		res, replaced := Replace(lhs, def, this)

		if this.IsProfiling() {
			elapsed := float64(time.Now().UnixNano()-started) / 1000000000
			this.timeCounter.AddTime(timecounter.CounterGroupDefTime, defStr, elapsed)
			this.timeCounter.AddTime(timecounter.CounterGroupLHSDefTime, lhsDefStr, elapsed)
		}

		if replaced {
			return res, true, def
		}
	}
	return nil, false, nil
}

func (this *EvalState) GetSymDef(name string) (expreduceapi.Ex, bool) {
	sym := NewSymbol(name)
	symDef, isDef, _ := this.GetDef(name, sym)
	return symDef, isDef
}

func (this *EvalState) DefineAttrs(sym *Symbol, rhs expreduceapi.Ex) {
	attrsList, attrsIsList := HeadAssertion(rhs, "System`List")
	if !attrsIsList {
		return
	}
	var stringAttrs []string
	for _, attrEx := range attrsList.GetParts()[1:] {
		attrSym, attrIsSym := attrEx.(*Symbol)
		if !attrIsSym {
			return
		}
		if !strings.HasPrefix(attrSym.Name, "System`") {
			continue
		}
		stringAttrs = append(stringAttrs, attrSym.Name[7:])
	}
	attrs := stringsToAttributes(stringAttrs)
	if !this.IsDef(sym.Name) {
		this.defined.Set(sym.Name, expreduceapi.Def{})
	}
	tmp := this.defined.GetDef(sym.Name)
	tmp.Attributes = attrs
	this.defined.Set(sym.Name, tmp)
}

func (this *EvalState) DefineDownValues(sym *Symbol, rhs expreduceapi.Ex) {
	dvList, isList := HeadAssertion(rhs, "System`List")
	if !isList {
		fmt.Println("Assignment to DownValues must be List of Rules.")
		return
	}
	dvs := []expreduceapi.DownValue{}

	for _, dvEx := range dvList.GetParts()[1:] {
		rule, isRule := HeadAssertion(dvEx, "System`Rule")
		if !isRule {
			rule, isRule = HeadAssertion(dvEx, "System`RuleDelayed")
		}
		if !isRule || len(rule.GetParts()) != 3 {
			fmt.Println("Assignment to DownValues must be List of Rules.")
		}
		dvs = append(dvs, expreduceapi.DownValue{Rule: rule})
	}

	if !this.IsDef(sym.Name) {
		this.defined.Set(sym.Name, expreduceapi.Def{})
	}
	tmp := this.defined.GetDef(sym.Name)
	tmp.Downvalues = dvs
	this.defined.Set(sym.Name, tmp)
}

func (this *EvalState) MarkSeen(name string) {
	if !this.IsDef(name) {
		newDef := expreduceapi.Def{
			Downvalues: []expreduceapi.DownValue{},
		}
		this.defined.Set(name, newDef)
	}
}

// Attempts to compute a specificity metric for a rule. Higher specificity rules
// should be tried first.
func ruleSpecificity(lhs expreduceapi.Ex, rhs expreduceapi.Ex, name string, es *EvalState) int {
	if name == "Rubi`Int" {
		return 100
	}
	// Special case for single integer arguments.
	expr, isExpr := lhs.(expreduceapi.ExpressionInterface).GetParts()[1].(expreduceapi.ExpressionInterface)
	if isExpr && len(expr.GetParts()) == 2 {
		if _, isInt := expr.GetParts()[1].(*Integer); isInt {
			return 110
		}
	}
	// I define complexity as the length of the Lhs.String()
	// because it is simple, and it works for most of the common cases. We wish
	// to attempt f[x_Integer] before we attempt f[x_]. If LHSs map to the same
	// "complexity" score, order then matters. TODO: Create better measure of
	// complexity (or specificity)
	context, ContextPath := DefinitionComplexityStringFormArgs()
	stringParams := expreduceapi.ToStringParams{
		Form:        "InputForm",
		Context:     context,
		ContextPath: ContextPath,
		// No need for the EvalState reference. Used for string expansion for
		// Definition[], which should not be in an actual definition.
		Esi: es,
	}
	specificity := len(lhs.StringForm(stringParams))
	if _, rhsIsCond := HeadAssertion(rhs, "System`Condition"); rhsIsCond {
		// Condition rules will be ranked in order of definition, not
		// specificity. I'm not entirely sure if this is correct, but it seems
		// to be the case for all the Rubi rules.
		specificity = 100
	}
	return specificity
}

func (this *EvalState) Define(lhs expreduceapi.Ex, rhs expreduceapi.Ex) {
	if this.IsFrozen() {
		return
	}
	// This function used to require a name as a parameter. Centralize the logic
	// here.
	name := ""
	LhsSym, ok := lhs.(*Symbol)
	if ok {
		name = LhsSym.Name
	}
	LhsF, ok := lhs.(expreduceapi.ExpressionInterface)
	if ok {
		headAsSym, headIsSym := LhsF.GetParts()[0].(*Symbol)
		if headIsSym {
			name = headAsSym.Name
			if name == "System`Attributes" {
				if len(LhsF.GetParts()) != 2 {
					return
				}
				modifiedSym, modifiedIsSym := LhsF.GetParts()[1].(*Symbol)
				if !modifiedIsSym {
					return
				}
				this.DefineAttrs(modifiedSym, rhs)
				return
			} else if name == "System`DownValues" {
				if len(LhsF.GetParts()) != 2 {
					return
				}
				modifiedSym, modifiedIsSym := LhsF.GetParts()[1].(*Symbol)
				if !modifiedIsSym {
					return
				}
				this.DefineDownValues(modifiedSym, rhs)
				return
			}
		}
		_, opExpr, isVerbatimOp := OperatorAssertion(lhs, "System`Verbatim")
		if isVerbatimOp {
			opSym, opIsSym := opExpr.GetParts()[1].(*Symbol)
			if opIsSym {
				name = opSym.Name
			}
		}
	}
	if name == "" {
		log.Fatalf("Trying to define an invalid lhs: %v", lhs)
	}

	this.Debugf("Inside es.Define(\"%s\",%s,%s)", name, lhs, rhs)
	heldLhs := E(S("HoldPattern"), lhs)
	if !this.IsDef(name) {
		newDef := expreduceapi.Def{
			Downvalues: []expreduceapi.DownValue{
				expreduceapi.DownValue{
					Rule: NewExpression([]expreduceapi.Ex{
						NewSymbol("System`Rule"), heldLhs, rhs,
					}),
				},
			},
		}
		this.defined.Set(name, newDef)
		return
	}

	// Overwrite identical rules.
	for _, dv := range this.defined.GetDef(name).Downvalues {
		existingRule := dv.Rule
		existingLhs := existingRule.GetParts()[1]
		if IsSameQ(existingLhs, heldLhs, &this.CASLogger) {
			this.defined.LockKey(name)
			existingRhsCond := maskNonConditional(existingRule.GetParts()[2])
			newRhsCond := maskNonConditional(rhs)
			if IsSameQ(existingRhsCond, newRhsCond, &this.CASLogger) {
				dv.Rule.GetParts()[2] = rhs
				this.defined.UnlockKey(name)
				return
			}
			this.defined.UnlockKey(name)
		}
	}

	// Insert into definitions for name. Maintain order of decreasing
	// complexity.
	var tmp = this.defined.GetDef(name)
	newSpecificity := ruleSpecificity(heldLhs, rhs, name, this)
	for i, dv := range this.defined.GetDef(name).Downvalues {
		if dv.Specificity == 0 {
			dv.Specificity = ruleSpecificity(
				dv.Rule.GetParts()[1],
				dv.Rule.GetParts()[2],
				name,
				this,
			)
		}
		if dv.Specificity < newSpecificity {
			newRule := NewExpression([]expreduceapi.Ex{NewSymbol("System`Rule"), heldLhs, rhs})
			tmp.Downvalues = append(
				tmp.Downvalues[:i],
				append(
					[]expreduceapi.DownValue{expreduceapi.DownValue{
						Rule:        newRule,
						Specificity: newSpecificity,
					}},
					this.defined.GetDef(name).Downvalues[i:]...,
				)...,
			)
			this.defined.Set(name, tmp)
			return
		}
	}
	tmp.Downvalues = append(tmp.Downvalues, expreduceapi.DownValue{Rule: NewExpression([]expreduceapi.Ex{NewSymbol("System`Rule"), heldLhs, rhs})})
	this.defined.Set(name, tmp)
}

func (this *EvalState) ClearAll() {
	this.Init(!this.NoInit)
}

func (this *EvalState) Clear(name string) {
	_, ok := this.defined.Get(name)
	if ok {
		this.defined.Set(name, expreduceapi.Def{})
		//delete(this.defined, name)
	}
}

func (this *EvalState) GetDefinedSnapshot() expreduceapi.DefinitionMap {
	return this.defined.CopyDefs()
}

func (this *EvalState) GetDefinedMap() expreduceapi.DefinitionMap {
	return &this.defined
}

func (this *EvalState) IsFrozen() bool {
	return this.freeze
}

func (this *EvalState) SetFrozen(frozen bool) {
	this.freeze = frozen
}

func (this *EvalState) GetLogger() expreduceapi.LoggingInterface {
	return &this.CASLogger
}

func (this *EvalState) GetStringDef(name string, defaultVal string) string {
	nameSym := NewSymbol(name)
	def, isDef, _ := this.GetDef(name, nameSym)
	if !isDef {
		return defaultVal
	}
	defString, defIsString := def.(*String)
	if !defIsString {
		return defaultVal
	}
	return defString.Val
}

func (this *EvalState) GetListDef(name string) expreduceapi.ExpressionInterface {
	nameSym := NewSymbol(name)
	def, isDef, _ := this.GetDef(name, nameSym)
	if !isDef {
		return NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
	}
	defList, defIsList := HeadAssertion(def, "System`List")
	if !defIsList {
		return NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
	}
	return defList
}

func (es *EvalState) Throw(e expreduceapi.ExpressionInterface) {
	es.thrown = e
}

func (es *EvalState) HasThrown() bool {
	return es.thrown != nil
}

func (es *EvalState) Thrown() expreduceapi.ExpressionInterface {
	return es.thrown
}

func (es *EvalState) GetTrace() expreduceapi.ExpressionInterface {
	return es.trace
}

func (es *EvalState) SetTrace(newTrace expreduceapi.ExpressionInterface) {
	es.trace = newTrace
}

func (es *EvalState) GetReapSown() expreduceapi.ExpressionInterface {
	return es.reapSown
}

func (es *EvalState) SetReapSown(ex expreduceapi.ExpressionInterface) {
	es.reapSown = ex
}

func (es *EvalState) ProcessTopLevelResult(in expreduceapi.Ex, out expreduceapi.Ex) expreduceapi.Ex {
	theRes := out
	if es.HasThrown() {
		fmt.Printf("Throw::nocatch: %v returned to top level but uncaught.\n\n", es.thrown)
		theRes = NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Hold"),
			es.thrown,
		})
		// Clear exception
		es.Throw(nil)
	} else {
		es.interrupted = false
	}
	thisLine, _ := es.GetSymDef("System`$Line")
	E(S("SetDelayed"), E(S("In"), thisLine), in).Eval(es)
	E(S("Set"), E(S("Out"), thisLine), theRes).Eval(es)
	prePrintFn, hasPrePrint := es.GetSymDef("System`$PrePrint")
	if hasPrePrint {
		theRes = E(prePrintFn, theRes).Eval(es)
	}
	E(S("Increment"), S("$Line")).Eval(es)
	return theRes
}

func maskNonConditional(e expreduceapi.Ex) expreduceapi.Ex {
	var res expreduceapi.Ex = NewSymbol("System`ExpreduceNonConditional")
	if asHead, isHead := HeadAssertion(e, "System`Condition"); isHead {
		res = NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Condition"),
			maskNonConditional(asHead.GetParts()[1]),
			asHead.GetParts()[2],
		})
	}
	heads := []string{"System`With", "System`Module"}
	for _, head := range heads {
		if asHead, isHead := HeadAssertion(e, head); isHead {
			if len(asHead.GetParts()) == 3 {
				if _, hasCond := HeadAssertion(asHead.GetParts()[2], "System`Condition"); hasCond {
					res = NewExpression([]expreduceapi.Ex{
						NewSymbol(head),
						asHead.GetParts()[1],
						maskNonConditional(asHead.GetParts()[2]),
					})
				}
			}
		}
	}
	return res
}
