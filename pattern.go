package cas

import "bytes"

type Pattern struct {
	S   Ex
	Obj Ex
}

func (this *Pattern) Eval(es *EvalState) Ex {
	return this
}

func (this *Pattern) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.S = this.S.Replace(r, es)
	this.Obj = this.Obj.Replace(r, es)
	return this.Eval(es)
}

func (this *Pattern) ToString() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("Pattern[")
		buffer.WriteString(this.S.ToString())
		buffer.WriteString(", ")
		// Assuming Obj will always be a Blank[] Expression
		buffer.WriteString(this.Obj.ToString())
		buffer.WriteString("]")
	} else {
		buffer.WriteString(this.S.ToString())
		// Assuming Obj will always be a Blank[] Expression
		buffer.WriteString(this.Obj.ToString())
	}
	return buffer.String()
}

func (this *Pattern) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Pattern)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.S,
		this.Obj,
	}, []Ex{
		other.S,
		other.Obj,
	}, es)
}

func (this *Pattern) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Pattern)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.S,
		this.Obj,
	}, []Ex{
		other.S,
		other.Obj,
	}, es)
}

func IsBlankType(e Ex, t string) bool {
	// Calling this function on an amatch_Integer with t == "Integer" would
	// yield true, while calling this function on an actual integer with
	// t == "Integer would return false.
	asPattern, patternOk := e.(*Pattern)
	if patternOk {
		asBlank, blankOk := asPattern.Obj.(*Blank)
		if blankOk {
			asSymbol, symbolOk := asBlank.H.(*Symbol)
			if symbolOk {
				return asSymbol.Name == t
			}
		}
	}
	asBlank, blankOk := e.(*Blank)
	if blankOk {
		asSymbol, symbolOk := asBlank.H.(*Symbol)
		if symbolOk {
			return asSymbol.Name == t
		}
	}
	return false
}

func IsBlankTypeCapturing(e Ex, target Ex, t string, es *EvalState) bool {
	// Similar to IsBlankType, but will capture target into es.patternDefined
	// if there is a valid match.
	asPattern, patternOk := e.(*Pattern)
	if patternOk {
		asBlank, blankOk := asPattern.Obj.(*Blank)
		if blankOk {
			asSymbol, symbolOk := asBlank.H.(*Symbol)
			if symbolOk {
				if asSymbol.Name == t || asSymbol.Name == "" {
					sAsSymbol, sAsSymbolOk := asPattern.S.(*Symbol)
					if sAsSymbolOk {
						_, isd := es.defined[sAsSymbol.Name]
						_, ispd := es.patternDefined[sAsSymbol.Name]
						if !ispd {
							es.patternDefined[sAsSymbol.Name] = target
						}
						if !es.patternDefined[sAsSymbol.Name].IsSameQ(target, es) {
							return false
						}

						if !isd {
							//es.defined[sAsSymbol.Name] = target
							es.Define(sAsSymbol.Name, sAsSymbol, target)
						} else {
							//return es.defined[sAsSymbol.Name].IsSameQ(target, es)
							return true
						}
					}
					return true
				}
				return false
			}
		}
	}
	asBlank, blankOk := e.(*Blank)
	if blankOk {
		asSymbol, symbolOk := asBlank.H.(*Symbol)
		if symbolOk {
			return asSymbol.Name == t || asSymbol.Name == ""
		}
	}
	return false
}

func (this *Pattern) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "Pattern") {
		return true
	}
	//return this.IsSameQ(otherEx, es)
	return false
}

func (this *Pattern) DeepCopy() Ex {
	return &Pattern{
		this.S.DeepCopy(),
		this.Obj.DeepCopy(),
	}
}

type Blank struct {
	H Ex
}

func (this *Blank) Eval(es *EvalState) Ex {
	return this
}

func (this *Blank) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.H = this.H.Replace(r, es)
	return this.Eval(es)
}

func (this *Blank) ToString() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("Blank[")
		buffer.WriteString(this.H.ToString())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("_")
		buffer.WriteString(this.H.ToString())
	}
	return buffer.String()
}

func (this *Blank) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Blank)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.H,
	}, []Ex{
		other.H,
	}, es)
}

func (this *Blank) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Blank)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.H,
	}, []Ex{
		other.H,
	}, es)
}

func (this *Blank) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "Blank") {
		return true
	}
	//return this.IsSameQ(otherEx, es)
	return false
}

func (this *Blank) DeepCopy() Ex {
	return &Blank{
		this.H.DeepCopy(),
	}
}

type BlankSequence struct {
	H Ex
}

func (this *BlankSequence) Eval(es *EvalState) Ex {
	return this
}

func (this *BlankSequence) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.H = this.H.Replace(r, es)
	return this.Eval(es)
}

func (this *BlankSequence) ToString() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("BlankSequence[")
		buffer.WriteString(this.H.ToString())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("__")
		buffer.WriteString(this.H.ToString())
	}
	return buffer.String()
}

func (this *BlankSequence) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*BlankSequence)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.H,
	}, []Ex{
		other.H,
	}, es)
}

func (this *BlankSequence) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*BlankSequence)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.H,
	}, []Ex{
		other.H,
	}, es)
}

func (this *BlankSequence) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "BlankSequence") {
		return true
	}
	//return this.IsSameQ(otherEx, es)
	return false
}

func (this *BlankSequence) DeepCopy() Ex {
	return &BlankSequence{
		this.H.DeepCopy(),
	}
}

type BlankNullSequence struct {
	H Ex
}

func (this *BlankNullSequence) Eval(es *EvalState) Ex {
	return this
}

func (this *BlankNullSequence) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.H = this.H.Replace(r, es)
	return this.Eval(es)
}

func (this *BlankNullSequence) ToString() string {
	var buffer bytes.Buffer
	if false {
		buffer.WriteString("BlankNullSequence[")
		buffer.WriteString(this.H.ToString())
		buffer.WriteString("]")
	} else {
		buffer.WriteString("___")
		buffer.WriteString(this.H.ToString())
	}
	return buffer.String()
}

func (this *BlankNullSequence) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*BlankNullSequence)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.H,
	}, []Ex{
		other.H,
	}, es)
}

func (this *BlankNullSequence) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*BlankNullSequence)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.H,
	}, []Ex{
		other.H,
	}, es)
}

func (this *BlankNullSequence) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "BlankNullSequence") {
		return true
	}
	//return this.IsSameQ(otherEx, es)
	return false
}

func (this *BlankNullSequence) DeepCopy() Ex {
	return &BlankNullSequence{
		this.H.DeepCopy(),
	}
}

// -------------------------

func BlankNullSequenceToBlank(bns *BlankNullSequence) *Blank {
	return &Blank{bns.H}
}

func BlankSequenceToBlank(bs *BlankSequence) *Blank {
	return &Blank{bs.H}
}

func ExArrayTestRepeatingMatch(array []Ex, b *Blank, es *EvalState) bool {
	toReturn := true
	for _, e := range array {
		tmpEs := NewEvalStateNoLog()
		isMatch := e.IsMatchQ(b, tmpEs)
		es.log.Debug(e.ToString(), b.ToString(), isMatch)
		toReturn = toReturn && isMatch
	}
	return toReturn
}
