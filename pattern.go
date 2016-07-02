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
	buffer.WriteString(this.S.ToString())
	// Assuming Obj will always be a Blank[] Expression
	buffer.WriteString(this.Obj.ToString())
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
	asPattern, patternOk := e.(*Pattern)
	if patternOk {
		asBlank, blankOk := asPattern.Obj.(*Blank)
		if blankOk {
			asSymbol, symbolOk := asBlank.H.(*Symbol)
			if symbolOk {
				if asSymbol.Name == t {
					sAsSymbol, sAsSymbolOk := asPattern.S.(*Symbol)
					if sAsSymbolOk {
						_, isdefined := es.defined[sAsSymbol.Name]
						if !isdefined {
							es.defined[sAsSymbol.Name] = target
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
			return asSymbol.Name == t
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
	buffer.WriteString("_")
	buffer.WriteString(this.H.ToString())
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
