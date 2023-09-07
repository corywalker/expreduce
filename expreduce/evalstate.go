package expreduce

import (
	"fmt"
	"log"
	"os"
	"os/signal"
	"strings"
	"time"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/logging"
	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/corywalker/expreduce/expreduce/streammanager"
	"github.com/corywalker/expreduce/expreduce/timecounter"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// EvalState keeps track of the state of the Expreduce interpreter. It contains
// all definitions and any evaluation bits.
type EvalState struct {
	// Embedded type for logging
	logging.CASLogger

	defined                 expreduceapi.DefinitionMap
	trace                   expreduceapi.ExpressionInterface
	NoInit                  bool
	timeCounter             timecounter.Group
	freeze                  bool
	thrown                  expreduceapi.ExpressionInterface
	reapSown                expreduceapi.ExpressionInterface
	interrupted             bool
	toStringFns             map[string]expreduceapi.ToStringFnType
	profilingToStringParams expreduceapi.ToStringParams
	streamManager           expreduceapi.StreamManager
}

func (es *EvalState) GetDefined(name string) (expreduceapi.Def, bool) {
	return es.GetDefinedMap().Get(name)
}

func (es *EvalState) SetDefined(name string, def expreduceapi.Def) {
	es.GetDefinedMap().Set(name, def)
}

func (es *EvalState) GetStringFn(
	headStr string,
) (expreduceapi.ToStringFnType, bool) {
	fn, ok := es.toStringFns[headStr]
	return fn, ok
}

func (es *EvalState) load(def Definition) {
	// TODO: deprecate most of es. We should be using .m files now.
	def.Name = es.GetStringDef("System`$Context", "") + def.Name
	es.MarkSeen(def.Name)
	EvalInterp("$Context = \"Private`\"", es)

	if len(def.Usage) > 0 {

		es.Eval((atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`SetDelayed"),
			atoms.NewExpression([]expreduceapi.Ex{
				atoms.NewSymbol("System`MessageName"),
				atoms.NewSymbol(def.Name),
				atoms.NewString("usage"),
			}),

			atoms.NewString(def.Usage),
		})))

	}

	newDef, foundDef := es.defined.Get(def.Name)
	if !foundDef {
		newDef = expreduceapi.Def{}
	}

	if def.legacyEvalFn != nil {
		newDef.LegacyEvalFn = def.legacyEvalFn
	}
	protectedAttrs := append(def.Attributes, "Protected")
	newDef.Attributes = atoms.StringsToAttributes(protectedAttrs)
	if def.Default != "" {
		newDef.DefaultExpr = parser.Interp(def.Default, es)
	}
	if def.toString != nil {
		es.toStringFns[def.Name] = def.toString
	}
	es.defined.Set(def.Name, newDef)
	EvalInterp("$Context = \"System`\"", es)
}

func (es *EvalState) Init(loadAllDefs bool) {
	es.defined = newDefinitionMap()
	es.streamManager = streammanager.NewStreamManager()
	es.toStringFns = make(map[string]expreduceapi.ToStringFnType)
	// These are fundamental symbols that affect even the parsing of
	// expressions. We must define them before even the bootstrap definitions.
	es.Define(atoms.NewSymbol("System`$Context"), atoms.NewString("System`"))
	es.Define(
		atoms.NewSymbol("System`$ContextPath"),
		atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`List"),
			atoms.NewString("System`"),
		}),
	)
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
		es.MarkSeen("System`ENearlySameTest")
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
		es.MarkSeen("System`Superscript")

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
		es.MarkSeen("System`FresnelS")
		es.MarkSeen("System`Gamma")

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
					es.load(def)
				}
			}
		}
		// Load rest of definitions.
		for _, defSet := range GetAllDefinitions() {
			for _, def := range defSet.Defs {
				if !def.Bootstrap {
					es.load(def)
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

	es.profilingToStringParams = ActualStringFormArgsFull("InputForm", es)
}

func NewEvalState() *EvalState {
	var es EvalState
	es.Init(true)

	es.SetUpLogging()
	es.DebugOff()

	signalChan := make(chan os.Signal, 1)
	signal.Notify(signalChan, os.Interrupt)
	go func() {
		for range signalChan {
			es.interrupted = true
		}
	}()

	return &es
}

func (es *EvalState) IsDef(name string) bool {
	_, isd := es.defined.Get(name)
	return isd
}

func (es *EvalState) GetDef(
	name string,
	lhs expreduceapi.Ex,
) (expreduceapi.Ex, bool, expreduceapi.ExpressionInterface) {
	if !es.IsDef(name) {
		return nil, false, nil
	}
	// Special case for checking simple variable definitions like "a = 5".
	// TODO: Perhaps split out single var values into the Definition to avoid
	// iterating over every one.
	if _, lhsIsSym := lhs.(*atoms.Symbol); lhsIsSym {
		for _, def := range es.defined.GetDef(name).Downvalues {
			if hp, hpDef := atoms.HeadAssertion(def.Rule.GetParts()[1], "System`HoldPattern"); hpDef {
				if len(hp.GetParts()) == 2 {
					if _, symDef := hp.GetParts()[1].(*atoms.Symbol); symDef {
						return def.Rule.GetParts()[2], true, def.Rule
					}
				}
			}
		}
		return nil, false, nil
	}
	es.Debugf("Inside GetDef(\"%s\",%s)", name, lhs)
	for i := range es.defined.GetDef(name).Downvalues {
		def := es.defined.GetDef(name).Downvalues[i].Rule

		defStr, lhsDefStr := "", ""
		started := int64(0)
		if es.IsProfiling() {
			defStr = def.StringForm(es.profilingToStringParams)
			lhsDefStr = lhs.StringForm(es.profilingToStringParams) + defStr
			started = time.Now().UnixNano()
		}

		res, replaced := replace(lhs, def, es)

		if es.IsProfiling() {
			elapsed := float64(time.Now().UnixNano()-started) / 1000000000
			es.timeCounter.AddTime(
				timecounter.CounterGroupDefTime,
				defStr,
				elapsed,
			)
			es.timeCounter.AddTime(
				timecounter.CounterGroupLHSDefTime,
				lhsDefStr,
				elapsed,
			)
		}

		if replaced {
			return res, true, def
		}
	}
	return nil, false, nil
}

func (es *EvalState) GetSymDef(name string) (expreduceapi.Ex, bool) {
	sym := atoms.NewSymbol(name)
	symDef, isDef, _ := es.GetDef(name, sym)
	return symDef, isDef
}

func (es *EvalState) defineAttrs(sym *atoms.Symbol, rhs expreduceapi.Ex) {
	attrsList, attrsIsList := atoms.HeadAssertion(rhs, "System`List")
	if !attrsIsList {
		return
	}
	var stringAttrs []string
	for _, attrEx := range attrsList.GetParts()[1:] {
		attrSym, attrIsSym := attrEx.(*atoms.Symbol)
		if !attrIsSym {
			return
		}
		if !strings.HasPrefix(attrSym.Name, "System`") {
			continue
		}
		stringAttrs = append(stringAttrs, attrSym.Name[7:])
	}
	attrs := atoms.StringsToAttributes(stringAttrs)
	if !es.IsDef(sym.Name) {
		es.defined.Set(sym.Name, expreduceapi.Def{})
	}
	tmp := es.defined.GetDef(sym.Name)
	tmp.Attributes = attrs
	es.defined.Set(sym.Name, tmp)
}

func (es *EvalState) defineDownValues(sym *atoms.Symbol, rhs expreduceapi.Ex) {
	dvList, isList := atoms.HeadAssertion(rhs, "System`List")
	if !isList {
		fmt.Println("Assignment to DownValues must be List of Rules.")
		return
	}
	dvs := []expreduceapi.DownValue{}

	for _, dvEx := range dvList.GetParts()[1:] {
		rule, isRule := atoms.HeadAssertion(dvEx, "System`Rule")
		if !isRule {
			rule, isRule = atoms.HeadAssertion(dvEx, "System`RuleDelayed")
		}
		if !isRule || len(rule.GetParts()) != 3 {
			fmt.Println("Assignment to DownValues must be List of Rules.")
		}
		dvs = append(dvs, expreduceapi.DownValue{Rule: rule})
	}

	if !es.IsDef(sym.Name) {
		es.defined.Set(sym.Name, expreduceapi.Def{})
	}
	tmp := es.defined.GetDef(sym.Name)
	tmp.Downvalues = dvs
	es.defined.Set(sym.Name, tmp)
}

func (es *EvalState) MarkSeen(name string) {
	if !es.IsDef(name) {
		newDef := expreduceapi.Def{
			Downvalues: []expreduceapi.DownValue{},
		}
		es.defined.Set(name, newDef)
	}
}

// Attempts to compute a specificity metric for a rule. Higher specificity rules
// should be tried first.
func ruleSpecificity(
	lhs expreduceapi.Ex,
	rhs expreduceapi.Ex,
	name string,
	es *EvalState,
) int {
	if name == "Rubi`Int" {
		return 100
	}
	// Special case for single integer arguments.
	expr, isExpr := lhs.(expreduceapi.ExpressionInterface).GetParts()[1].(expreduceapi.ExpressionInterface)
	if isExpr && len(expr.GetParts()) == 2 {
		if _, isInt := expr.GetParts()[1].(*atoms.Integer); isInt {
			return 110
		}
	}
	// I define complexity as the length of the Lhs.String()
	// because it is simple, and it works for most of the common cases. We wish
	// to attempt f[x_Integer] before we attempt f[x_]. If LHSs map to the same
	// "complexity" score, order then matters. TODO: Create better measure of
	// complexity (or specificity)
	context, contextPath := definitionComplexityStringFormArgs()
	stringParams := expreduceapi.ToStringParams{
		Form:        "InputForm",
		Context:     context,
		ContextPath: contextPath,
		// No need for the EvalState reference. Used for string expansion for
		// Definition[], which should not be in an actual definition.
		Esi: es,
	}
	specificity := len(lhs.StringForm(stringParams))
	if _, rhsIsCond := atoms.HeadAssertion(rhs, "System`Condition"); rhsIsCond {
		// Condition rules will be ranked in order of definition, not
		// specificity. I'm not entirely sure if this is correct, but it seems
		// to be the case for all the Rubi rules.
		specificity = 100
	}
	return specificity
}

func (es *EvalState) Define(lhs expreduceapi.Ex, rhs expreduceapi.Ex) {
	if es.IsFrozen() {
		return
	}
	// This function used to require a name as a parameter. Centralize the logic
	// here.
	name := ""
	lhsSym, ok := lhs.(*atoms.Symbol)
	if ok {
		name = lhsSym.Name
	}
	lhsF, ok := lhs.(expreduceapi.ExpressionInterface)
	if ok {
		headAsSym, headIsSym := lhsF.GetParts()[0].(*atoms.Symbol)
		if headIsSym {
			name = headAsSym.Name
			if name == "System`Attributes" {
				if len(lhsF.GetParts()) != 2 {
					return
				}
				modifiedSym, modifiedIsSym := lhsF.GetParts()[1].(*atoms.Symbol)
				if !modifiedIsSym {
					return
				}
				es.defineAttrs(modifiedSym, rhs)
				return
			} else if name == "System`DownValues" {
				if len(lhsF.GetParts()) != 2 {
					return
				}
				modifiedSym, modifiedIsSym := lhsF.GetParts()[1].(*atoms.Symbol)
				if !modifiedIsSym {
					return
				}
				es.defineDownValues(modifiedSym, rhs)
				return
			}
		}
		_, opExpr, isVerbatimOp := atoms.OperatorAssertion(
			lhs,
			"System`Verbatim",
		)
		if isVerbatimOp {
			opSym, opIsSym := opExpr.GetParts()[1].(*atoms.Symbol)
			if opIsSym {
				name = opSym.Name
			}
		}
	}
	if name == "" {
		log.Fatalf("Trying to define an invalid lhs: %v", lhs)
	}

	es.Debugf("Inside es.Define(\"%s\",%s,%s)", name, lhs, rhs)
	heldLHS := atoms.E(atoms.S("HoldPattern"), lhs)
	if !es.IsDef(name) {
		newDef := expreduceapi.Def{
			Downvalues: []expreduceapi.DownValue{
				expreduceapi.DownValue{
					Rule: atoms.NewExpression([]expreduceapi.Ex{
						atoms.NewSymbol("System`Rule"), heldLHS, rhs,
					}),
				},
			},
		}
		es.defined.Set(name, newDef)
		return
	}

	// Overwrite identical rules.
	for _, dv := range es.defined.GetDef(name).Downvalues {
		existingRule := dv.Rule
		existingLHS := existingRule.GetParts()[1]
		if atoms.IsSameQ(existingLHS, heldLHS) {
			es.defined.LockKey(name)
			existingRHSCond := maskNonConditional(existingRule.GetParts()[2])
			newRHSCond := maskNonConditional(rhs)
			if atoms.IsSameQ(existingRHSCond, newRHSCond) {
				dv.Rule.GetParts()[2] = rhs
				es.defined.UnlockKey(name)
				return
			}
			es.defined.UnlockKey(name)
		}
	}

	// Insert into definitions for name. Maintain order of decreasing
	// complexity.
	var tmp = es.defined.GetDef(name)
	newSpecificity := ruleSpecificity(heldLHS, rhs, name, es)
	for i, dv := range es.defined.GetDef(name).Downvalues {
		if dv.Specificity == 0 {
			dv.Specificity = ruleSpecificity(
				dv.Rule.GetParts()[1],
				dv.Rule.GetParts()[2],
				name,
				es,
			)
		}
		if dv.Specificity < newSpecificity {
			newRule := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`Rule"), heldLHS, rhs},
			)
			tmp.Downvalues = append(
				tmp.Downvalues[:i],
				append(
					[]expreduceapi.DownValue{expreduceapi.DownValue{
						Rule:        newRule,
						Specificity: newSpecificity,
					}},
					es.defined.GetDef(name).Downvalues[i:]...,
				)...,
			)
			es.defined.Set(name, tmp)
			return
		}
	}
	tmp.Downvalues = append(
		tmp.Downvalues,
		expreduceapi.DownValue{
			Rule: atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`Rule"), heldLHS, rhs},
			),
		},
	)
	es.defined.Set(name, tmp)
}

func (es *EvalState) ClearAll() {
	es.Init(!es.NoInit)
}

func (es *EvalState) Clear(name string) {
	_, ok := es.defined.Get(name)
	if ok {
		es.defined.Set(name, expreduceapi.Def{})
		//delete(es.defined, name)
	}
}

func (es *EvalState) GetDefinedSnapshot() expreduceapi.DefinitionMap {
	return es.defined.CopyDefs()
}

func (es *EvalState) GetDefinedMap() expreduceapi.DefinitionMap {
	return es.defined
}

func (es *EvalState) IsFrozen() bool {
	return es.freeze
}

func (es *EvalState) SetFrozen(frozen bool) {
	es.freeze = frozen
}

func (es *EvalState) IsInterrupted() bool {
	return es.interrupted
}

func (es *EvalState) GetLogger() expreduceapi.LoggingInterface {
	return &es.CASLogger
}

func (es *EvalState) GetStringDef(name string, defaultVal string) string {
	nameSym := atoms.NewSymbol(name)
	def, isDef, _ := es.GetDef(name, nameSym)
	if !isDef {
		return defaultVal
	}
	defString, defIsString := def.(*atoms.String)
	if !defIsString {
		return defaultVal
	}
	return defString.Val
}

func (es *EvalState) GetListDef(name string) expreduceapi.ExpressionInterface {
	nameSym := atoms.NewSymbol(name)
	def, isDef, _ := es.GetDef(name, nameSym)
	if !isDef {
		return atoms.NewExpression(
			[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
		)
	}
	defList, defIsList := atoms.HeadAssertion(def, "System`List")
	if !defIsList {
		return atoms.NewExpression(
			[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
		)
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

func (es *EvalState) GetTimeCounter() *timecounter.Group {
	return &es.timeCounter
}

func (es *EvalState) ProcessTopLevelResult(
	in expreduceapi.Ex,
	out expreduceapi.Ex,
) expreduceapi.Ex {
	theRes := out
	if es.HasThrown() {
		fmt.Printf(
			"Throw::nocatch: %v returned to top level but uncaught.\n\n",
			es.thrown,
		)
		theRes = atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Hold"),
			es.thrown,
		})

		// Clear exception
		es.Throw(nil)
	} else {
		es.interrupted = false
	}
	thisLine, _ := es.GetSymDef("System`$Line")
	es.Eval(
		atoms.E(atoms.S("SetDelayed"), atoms.E(atoms.S("In"), thisLine), in),
	)
	es.Eval(atoms.E(atoms.S("Set"), atoms.E(atoms.S("Out"), thisLine), theRes))
	prePrintFn, hasPrePrint := es.GetSymDef("System`$PrePrint")
	if hasPrePrint {
		theRes = es.Eval(atoms.E(prePrintFn, theRes))
	}
	es.Eval(atoms.E(atoms.S("Increment"), atoms.S("$Line")))
	return theRes
}

func maskNonConditional(e expreduceapi.Ex) expreduceapi.Ex {
	var res expreduceapi.Ex = atoms.NewSymbol("System`ExpreduceNonConditional")
	if asHead, isHead := atoms.HeadAssertion(e, "System`Condition"); isHead {
		res = atoms.NewExpression([]expreduceapi.Ex{
			atoms.NewSymbol("System`Condition"),
			maskNonConditional(asHead.GetParts()[1]),
			asHead.GetParts()[2],
		})

	}
	heads := []string{"System`With", "System`Module"}
	for _, head := range heads {
		if asHead, isHead := atoms.HeadAssertion(e, head); isHead {
			if len(asHead.GetParts()) == 3 {
				if _, hasCond := atoms.HeadAssertion(asHead.GetParts()[2], "System`Condition"); hasCond {
					res = atoms.NewExpression([]expreduceapi.Ex{
						atoms.NewSymbol(head),
						asHead.GetParts()[1],
						maskNonConditional(asHead.GetParts()[2]),
					})

				}
			}
		}
	}
	return res
}

func (es *EvalState) GetStreamManager() expreduceapi.StreamManager {
	return es.streamManager
}
