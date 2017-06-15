package expreduce

import (
	"bytes"
	"log"
	"sort"
	"strings"
	"time"
)

type DefMap map[string]Def

type EvalState struct {
	// Embedded type for logging
	CASLogger

	defined DefMap
	trace   *Expression
	NoInit  bool
	defTimeCounter TimeCounter
	lhsDefTimeCounter TimeCounter
}

func (this *EvalState) Load(def Definition) {
	// TODO: do we really need SetDelayed here, or should we just write to
	// downvalues directly? If we did this, we could potentially remove the
	// "bootstrap" attribute that SetDelayed has.
	for _, rule := range def.Rules {
		(NewExpression([]Ex{
			&Symbol{"SetDelayed"},
			Interp(rule.Lhs),
			Interp(rule.Rhs),
		})).Eval(this)
	}

	if len(def.Usage) > 0 {
		(NewExpression([]Ex{
			&Symbol{"SetDelayed"},
			NewExpression([]Ex{
				&Symbol{"MessageName"},
				&Symbol{def.Name},
				&String{"usage"},
			}),

			&String{def.Usage},
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
	if def.toString != nil {
		// Global so that standard String() interface can access these
		toStringFns[def.Name] = def.toString
	}
	this.defined[def.Name] = newDef
}

func InitCAS(es *EvalState) {
	// System initialization
	EvalInterp("SeedRandom[UnixTime[]]", es)
}

func (es *EvalState) Init(loadAllDefs bool) {
	es.defined = make(map[string]Def)
	es.lhsDefTimeCounter.Init()
	es.defTimeCounter.Init()

	es.NoInit = !loadAllDefs
	if !es.NoInit {
		// Init modules
		for _, defSet := range GetAllDefinitions() {
			for _, def := range defSet.Defs {
				if def.Bootstrap {
					es.Load(def)
				}
			}
		}
		for _, defSet := range GetAllDefinitions() {
			for _, def := range defSet.Defs {
				if !def.Bootstrap {
					es.Load(def)
				}
			}
		}
		InitCAS(es)
	}
}

func NewEvalState() *EvalState {
	var es EvalState
	es.Init(true)

	es.SetUpLogging()
	es.DebugOff()

	return &es
}

func NewEvalStateNoLog(loadAllDefs bool) *EvalState {
	var es EvalState
	es.Init(loadAllDefs)
	es.CASLogger.debugState = false
	return &es
}

func (this *EvalState) GetDef(name string, lhs Ex) (Ex, bool, *Expression) {
	_, isd := this.defined[name]
	if !isd {
		return nil, false, nil
	}
	this.Debugf("Inside GetDef(\"%s\",%s)", name, lhs)
	for i := range this.defined[name].downvalues {
	    def := this.defined[name].downvalues[i]

		defStr, lhsDefStr := "", ""
		started := int64(0)
		if this.debugState {
			defStr = def.String()
			lhsDefStr = lhs.String() + defStr
			started = time.Now().UnixNano()
		}

		ismatchq, _ := IsMatchQ(lhs, def.Parts[1], EmptyPD(), this)
		if ismatchq {
			res := ReplaceAll(lhs, &def, this, EmptyPD(), "")
			return res, true, &def
		}

		if this.debugState {
			elapsed := float64(time.Now().UnixNano() - started) / 1000000000
			this.defTimeCounter.AddTime(defStr, elapsed)
			this.lhsDefTimeCounter.AddTime(lhsDefStr, elapsed)
		}
	}
	return nil, false, nil
}

func (this *EvalState) Define(lhs Ex, rhs Ex) {
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
		}
	}
	if name == "" {
		log.Fatalf("Trying to define an invalid lhs: %v", lhs)
	}

	this.Debugf("Inside es.Define(\"%s\",%s,%s)", name, lhs, rhs)
	_, isd := this.defined[name]
	if !isd {
		newDef := Def{
			downvalues: []Expression{*NewExpression([]Ex{&Symbol{"Rule"}, lhs, rhs})},
		}
		this.defined[name] = newDef
		return
	}

	for i := range this.defined[name].downvalues {
		if IsSameQ(this.defined[name].downvalues[i].Parts[1], lhs, &this.CASLogger) {
			this.defined[name].downvalues[i].Parts[2] = rhs
			return
		}
	}

	// Insert into definitions for name. Maintain order of decreasing
	// complexity. I define complexity as the length of the Lhs.String()
	// because it is simple, and it works for most of the common cases. We wish
	// to attempt f[x_Integer] before we attempt f[x_]. If LHSs map to the same
	// "complexity" score, order then matters. TODO: Create better measure of
	// complexity (or specificity)
	var tmp = this.defined[name]
	newLhsLen := len(lhs.StringForm("InputForm"))
	for i := range this.defined[name].downvalues {
		thisLhsLen := len(this.defined[name].downvalues[i].Parts[1].String())
		if thisLhsLen < newLhsLen {
			tmp.downvalues = append(tmp.downvalues[:i], append([]Expression{*NewExpression([]Ex{&Symbol{"Rule"}, lhs, rhs})}, this.defined[name].downvalues[i:]...)...)
			this.defined[name] = tmp
			return
		}
	}
	tmp.downvalues = append(tmp.downvalues, *NewExpression([]Ex{&Symbol{"Rule"}, lhs, rhs}))
	this.defined[name] = tmp
}

func (this *EvalState) ClearAll() {
	this.Init(!this.NoInit)
}

func (this *EvalState) Clear(name string) {
	_, ok := this.defined[name]
	if ok {
		delete(this.defined, name)
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
