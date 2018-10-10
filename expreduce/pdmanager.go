package expreduce

import (
	"bytes"
	"sort"
	"strings"
)

type PDManager struct {
	patternDefined map[string]Ex
}

func EmptyPD() *PDManager {
	return &PDManager{nil}
}

func CopyPD(orig *PDManager) (dest *PDManager) {
	dest = EmptyPD()
	// We do not care that this iterates in a random order.
	if (*orig).Len() > 0 {
		dest.LazyMakeMap()
		for k, v := range (*orig).patternDefined {
			(*dest).patternDefined[k] = v
		}
	}
	return
}

func (this *PDManager) LazyMakeMap() {
	if this.patternDefined == nil {
		this.patternDefined = make(map[string]Ex)
	}
}

func (this *PDManager) Update(toAdd *PDManager) {
	if (*toAdd).Len() > 0 {
		this.LazyMakeMap()
	}
	// We do not care that this iterates in a random order.
	for k, v := range (*toAdd).patternDefined {
		(*this).patternDefined[k] = v
	}
}

func (this *PDManager) Len() int {
	if this.patternDefined == nil {
		return 0
	}
	return len(this.patternDefined)
}

func (this *PDManager) String(es *EvalState) string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	// We sort the keys here such that converting identical PDManagers always
	// produces the same string.
	keys := []string{}
	for k := range this.patternDefined {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		v := this.patternDefined[k]
		buffer.WriteString(k)
		buffer.WriteString("_: ")
		buffer.WriteString(v.String(es))
		buffer.WriteString(", ")
	}
	if strings.HasSuffix(buffer.String(), ", ") {
		buffer.Truncate(buffer.Len() - 2)
	}
	buffer.WriteString("}")
	return buffer.String()
}

func (this *PDManager) Expression() Ex {
	res := NewExpression([]Ex{NewSymbol("System`List")})
	// We sort the keys here such that converting identical PDManagers always
	// produces the same string.
	keys := []string{}
	for k := range this.patternDefined {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		v := this.patternDefined[k]
		res.appendEx(NewExpression([]Ex{
			NewSymbol("System`Rule"),
			NewString(k),
			v,
		}))
	}
	return res
}

func DefineSequence(lhs parsedForm, sequence []Ex, pm *PDManager, sequenceHead string, es *EvalState) bool {
	var attemptDefine Ex = nil
	if lhs.hasPat {
		sequenceHeadSym := NewSymbol(sequenceHead)
		oneIdent := sequenceHeadSym.Attrs(&es.defined).OneIdentity
		if len(sequence) == 1 && (lhs.isBlank || oneIdent || lhs.isOptional) {
			attemptDefine = sequence[0]
		} else if len(sequence) == 0 && lhs.isOptional && lhs.defaultExpr != nil {
			attemptDefine = lhs.defaultExpr
		} else if lhs.isImpliedBs {
			attemptDefine = NewExpression(append([]Ex{sequenceHeadSym}, sequence...))
		} else {
			head := NewSymbol("System`Sequence")
			attemptDefine = NewExpression(append([]Ex{head}, sequence...))
		}

		if pm.patternDefined != nil {
			defined, ispd := pm.patternDefined[lhs.patSym.Name]
			if ispd && !IsSameQ(defined, attemptDefine, &es.CASLogger) {
				es.Debugf("patterns do not match! continuing.")
				return false
			}
		}
		pm.LazyMakeMap()
		pm.patternDefined[lhs.patSym.Name] = attemptDefine
	}
	return true
}
