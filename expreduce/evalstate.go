package expreduce

import (
	"bytes"
	"fmt"
	"os"
	"os/signal"
	"log"
	"sort"
	"strings"
	"time"
)

type DefMap map[string]Def

type EvalState struct {
	// Embedded type for logging
	CASLogger

	defined     DefMap
	trace       *Expression
	NoInit      bool
	timeCounter TimeCounterGroup
	freeze      bool
	thrown      *Expression
	interrupted bool
}

func (this *EvalState) Load(def Definition) {
	// TODO: deprecate most of this. We should be using .m files now.
	def.Name = this.GetStringDef("System`$Context", "") + def.Name
	this.MarkSeen(def.Name)
	EvalInterp("$Context = \"Private`\"", this)
	// TODO: do we really need SetDelayed here, or should we just write to
	// downvalues directly? If we did this, we could potentially remove the
	// "bootstrap" attribute that SetDelayed has.
	for _, rule := range def.Rules {
		(NewExpression([]Ex{
			NewSymbol("System`SetDelayed"),
			Interp(rule.Lhs, this),
			Interp(rule.Rhs, this),
		})).Eval(this)
	}

	if len(def.Usage) > 0 {
		(NewExpression([]Ex{
			NewSymbol("System`SetDelayed"),
			NewExpression([]Ex{
				NewSymbol("System`MessageName"),
				NewSymbol(def.Name),
				NewString("usage"),
			}),

			NewString(def.Usage),
		})).Eval(this)
	}

	newDef, foundDef := this.defined[def.Name]
	if !foundDef {
		newDef = Def{}
	}

	if def.legacyEvalFn != nil {
		newDef.legacyEvalFn = def.legacyEvalFn
	}
	protectedAttrs := append(def.Attributes, "Protected")
	newDef.attributes = stringsToAttributes(protectedAttrs)
	if def.Default != "" {
		newDef.defaultExpr = Interp(def.Default, this)
	}
	if def.toString != nil {
		// Global so that standard String() interface can access these
		toStringFns[def.Name] = def.toString
	}
	this.defined[def.Name] = newDef
	EvalInterp("$Context = \"System`\"", this)
}

func (es *EvalState) Init(loadAllDefs bool) {
	es.defined = make(map[string]Def)
	// These are fundamental symbols that affect even the parsing of
	// expressions. We must define them before even the bootstrap definitions.
	es.Define(NewSymbol("System`$Context"), NewString("System`"))
	es.Define(NewSymbol("System`$ContextPath"), NewExpression([]Ex{
		NewSymbol("System`List"),
		NewString("System`"),
	}))
	es.timeCounter.Init()

	es.NoInit = !loadAllDefs
	if !es.NoInit {
		// Init modules
		// Mark all core builtins as seen in the System context:
		es.MarkSeen("System`Symbol")
		es.MarkSeen("System`Integer")
		es.MarkSeen("System`Rational")
		es.MarkSeen("System`String")
		es.MarkSeen("System`True")
		es.MarkSeen("System`False")

		es.MarkSeen("System`InputForm")
		es.MarkSeen("System`OutputForm")
		es.MarkSeen("System`FullForm")

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

		es.MarkSeen("System`Exp")
		es.MarkSeen("System`AppellF1")

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
	es.CASLogger.debugState = false
	return &es
}

func (this *EvalState) IsDef(name string) bool {
	_, isd := this.defined[name]
	return isd
}

func (this *EvalState) GetDef(name string, lhs Ex) (Ex, bool, *Expression) {
	if !this.IsDef(name) {
		return nil, false, nil
	}
	// Special case for checking simple variable definitions like "a = 5".
	// TODO: Perhaps split out single var values into the Definition to avoid
	// iterating over every one.
	if _, lhsIsSym := lhs.(*Symbol); lhsIsSym {
		for _, def := range this.defined[name].downvalues {
			if hp, hpDef := HeadAssertion(def.rule.Parts[1], "System`HoldPattern"); hpDef {
				if len(hp.Parts) == 2 {
					if _, symDef := hp.Parts[1].(*Symbol); symDef {
						return def.rule.Parts[2], true, def.rule
					}
				}
			}
		}
		return nil, false, nil
	}
	this.Debugf("Inside GetDef(\"%s\",%s)", name, lhs)
	for i := range this.defined[name].downvalues {
		def := this.defined[name].downvalues[i].rule

		defStr, lhsDefStr := "", ""
		started := int64(0)
		if this.isProfiling {
			defStr = def.String()
			lhsDefStr = lhs.String() + defStr
			started = time.Now().UnixNano()
		}

		res, replaced := Replace(lhs, def, this)

		if this.isProfiling {
			elapsed := float64(time.Now().UnixNano()-started) / 1000000000
			this.timeCounter.AddTime(CounterGroupDefTime, defStr, elapsed)
			this.timeCounter.AddTime(CounterGroupLhsDefTime, lhsDefStr, elapsed)
		}

		if replaced {
			return res, true, def
		}
	}
	return nil, false, nil
}

func (this *EvalState) GetSymDef(name string) (Ex, bool) {
	sym := NewSymbol(name)
	symDef, isDef, _ := this.GetDef(name, sym)
	return symDef, isDef
}

func (this *EvalState) DefineAttrs(sym *Symbol, rhs Ex) {
	attrsList, attrsIsList := HeadAssertion(rhs, "System`List")
	if !attrsIsList {
		return
	}
	var stringAttrs []string
	for _, attrEx := range attrsList.Parts[1:] {
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
		this.defined[sym.Name] = Def{}
	}
	tmp := this.defined[sym.Name]
	tmp.attributes = attrs
	this.defined[sym.Name] = tmp
}

func (this *EvalState) DefineDownValues(sym *Symbol, rhs Ex) {
	dvList, isList := HeadAssertion(rhs, "System`List")
	if !isList {
		fmt.Println("Assignment to DownValues must be List of Rules.")
		return
	}
	dvs := []DownValue{}

	for _, dvEx := range dvList.Parts[1:] {
		rule, isRule := HeadAssertion(dvEx, "System`Rule")
		if !isRule {
			rule, isRule = HeadAssertion(dvEx, "System`RuleDelayed")
		}
		if !isRule || len(rule.Parts) != 3 {
			fmt.Println("Assignment to DownValues must be List of Rules.")
		}
		dvs = append(dvs, DownValue{rule: rule})
	}

	if !this.IsDef(sym.Name) {
		this.defined[sym.Name] = Def{}
	}
	tmp := this.defined[sym.Name]
	tmp.downvalues = dvs
	this.defined[sym.Name] = tmp
}

func (this *EvalState) MarkSeen(name string) {
	if !this.IsDef(name) {
		newDef := Def{
			downvalues: []DownValue{},
		}
		this.defined[name] = newDef
	}
}

// Attempts to compute a specificity metric for a rule. Higher specificity rules
// should be tried first.
func ruleSpecificity(lhs Ex, rhs Ex, name string) int {
	if name == "Rubi`Int" {
		return 100
	}
	// I define complexity as the length of the Lhs.String()
	// because it is simple, and it works for most of the common cases. We wish
	// to attempt f[x_Integer] before we attempt f[x_]. If LHSs map to the same
	// "complexity" score, order then matters. TODO: Create better measure of
	// complexity (or specificity)
	context, contextPath := DefinitionComplexityStringFormArgs()
	specificity := len(lhs.StringForm("InputForm", context, contextPath))
	if _, rhsIsCond := HeadAssertion(rhs, "System`Condition"); rhsIsCond {
		// Condition rules will be ranked in order of definition, not
		// specificity. I'm not entirely sure if this is correct, but it seems
		// to be the case for all the Rubi rules.
		specificity = 100
	}
	return specificity
}

func (this *EvalState) Define(lhs Ex, rhs Ex) {
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
	LhsF, ok := lhs.(*Expression)
	if ok {
		headAsSym, headIsSym := LhsF.Parts[0].(*Symbol)
		if headIsSym {
			name = headAsSym.Name
			if name == "System`Attributes" {
				if len(LhsF.Parts) != 2 {
					return
				}
				modifiedSym, modifiedIsSym := LhsF.Parts[1].(*Symbol)
				if !modifiedIsSym {
					return
				}
				this.DefineAttrs(modifiedSym, rhs)
				return
			} else if name == "System`DownValues" {
				if len(LhsF.Parts) != 2 {
					return
				}
				modifiedSym, modifiedIsSym := LhsF.Parts[1].(*Symbol)
				if !modifiedIsSym {
					return
				}
				this.DefineDownValues(modifiedSym, rhs)
				return
			}
		}
		_, opExpr, isVerbatimOp := OperatorAssertion(lhs, "System`Verbatim")
		if isVerbatimOp {
			opSym, opIsSym := opExpr.Parts[1].(*Symbol)
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
		newDef := Def{
			downvalues: []DownValue{
				DownValue{
					rule: NewExpression([]Ex{
						NewSymbol("System`Rule"), heldLhs, rhs,
					}),
				},
			},
		}
		this.defined[name] = newDef
		return
	}

	// Overwrite identical rules.
	for _, dv := range this.defined[name].downvalues {
		existingRule := dv.rule
		existingLhs := existingRule.Parts[1]
		if IsSameQ(existingLhs, heldLhs, &this.CASLogger) {
			existingRhsCond := maskNonConditional(existingRule.Parts[2])
			newRhsCond := maskNonConditional(rhs)
			if IsSameQ(existingRhsCond, newRhsCond, &this.CASLogger) {
				dv.rule.Parts[2] = rhs
				return
			}
		}
	}

	// Insert into definitions for name. Maintain order of decreasing
	// complexity.
	var tmp = this.defined[name]
	newSpecificity := ruleSpecificity(heldLhs, rhs, name)
	for i, dv := range this.defined[name].downvalues {
		if dv.specificity == 0 {
			dv.specificity = ruleSpecificity(
				dv.rule.Parts[1],
				dv.rule.Parts[2],
				name,
			)
		}
		if dv.specificity < newSpecificity {
			newRule := NewExpression([]Ex{NewSymbol("System`Rule"), heldLhs, rhs})
			tmp.downvalues = append(
				tmp.downvalues[:i],
				append(
					[]DownValue{DownValue{
						rule:        newRule,
						specificity: newSpecificity,
					}},
					this.defined[name].downvalues[i:]...,
				)...,
			)
			this.defined[name] = tmp
			return
		}
	}
	tmp.downvalues = append(tmp.downvalues, DownValue{rule: NewExpression([]Ex{NewSymbol("System`Rule"), heldLhs, rhs})})
	this.defined[name] = tmp
}

func (this *EvalState) ClearAll() {
	this.Init(!this.NoInit)
}

func (this *EvalState) Clear(name string) {
	_, ok := this.defined[name]
	if ok {
		this.defined[name] = Def{}
		//delete(this.defined, name)
	}
}

func (this *EvalState) GetDefinedSnapshot() map[string]Def {
	return CopyDefs(this.defined)
}

func (this *EvalState) String() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	// We sort the keys here such that converting identical EvalStates always
	// produces the same string.
	keys := []string{}
	for k := range this.defined {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		v := this.defined[k]
		buffer.WriteString(k)
		buffer.WriteString(": ")
		buffer.WriteString(v.String())
		buffer.WriteString(", ")
	}
	if strings.HasSuffix(buffer.String(), ", ") {
		buffer.Truncate(buffer.Len() - 2)
	}
	buffer.WriteString("}")
	return buffer.String()
}

func (this *EvalState) IsFrozen() bool {
	return this.freeze
}

func (this *EvalState) SetFrozen(frozen bool) {
	this.freeze = frozen
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

func (this *EvalState) GetListDef(name string) *Expression {
	nameSym := NewSymbol(name)
	def, isDef, _ := this.GetDef(name, nameSym)
	if !isDef {
		return NewExpression([]Ex{NewSymbol("System`List")})
	}
	defList, defIsList := HeadAssertion(def, "System`List")
	if !defIsList {
		return NewExpression([]Ex{NewSymbol("System`List")})
	}
	return defList
}

func (es *EvalState) Throw(e *Expression) {
	es.thrown = e
}

func (es *EvalState) HasThrown() bool {
	return es.thrown != nil
}

func (es *EvalState) ProcessTopLevelResult(e Ex) Ex {
	if es.HasThrown() {
		fmt.Printf("Throw::nocatch: %v returned to top level but uncaught.\n\n", es.thrown)
		toReturn := NewExpression([]Ex{
			NewSymbol("System`Hold"),
			es.thrown,
		})
		// Clear exception
		es.Throw(nil)
		return toReturn
	}
	es.interrupted = false
	return e
}

func maskNonConditional(e Ex) Ex {
	var res Ex = NewSymbol("System`ExpreduceNonConditional")
	if asHead, isHead := HeadAssertion(e, "System`Condition"); isHead {
		res = NewExpression([]Ex{
			NewSymbol("System`Condition"),
			maskNonConditional(asHead.Parts[1]),
			asHead.Parts[2],
		})
	}
	heads := []string{"System`With", "System`Module"}
	for _, head := range heads {
		if asHead, isHead := HeadAssertion(e, head); isHead {
			if len(asHead.Parts) == 3 {
				if _, hasCond := HeadAssertion(asHead.Parts[2], "System`Condition"); hasCond {
					res = NewExpression([]Ex{
						NewSymbol(head),
						asHead.Parts[1],
						maskNonConditional(asHead.Parts[2]),
					})
				}
			}
		}
	}
	return res
}
