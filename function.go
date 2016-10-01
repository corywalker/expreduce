package cas

import "bytes"

type Function struct {
	Name      Ex
	Arguments []Ex
}

func (this *Function) Eval(es *EvalState) Ex {

	// If any of the arguments are Sequence, merge them with arguments
	origLen := len(this.Arguments)
	offset := 0
	for i := 0; i < origLen; i++ {
		j := i + offset
		e := this.Arguments[j]
		seq, isseq := e.(*Sequence)
		if isseq {
			start := j
			end := j + 1
			if j == 0 {
				this.Arguments = append(seq.Arguments, this.Arguments[end:]...)
			} else if j == len(this.Arguments)-1 {
				this.Arguments = append(this.Arguments[:start], seq.Arguments...)
			} else {
				this.Arguments = append(append(this.Arguments[:start], seq.Arguments...), this.Arguments[end:]...)
			}
			offset += len(seq.Arguments) - 1
		}
	}

	nameAsSym, isNameSym := this.Name.(*Symbol)
	if isNameSym {
		nameStr := nameAsSym.Name
		if nameStr == "Power" && len(this.Arguments) == 2 {
			t := &Power{
				Base:  this.Arguments[0],
				Power: this.Arguments[1],
			}
			return t.Eval(es)
		}
		if nameStr == "Equal" && len(this.Arguments) == 2 {
			t := &Equal{
				Lhs: this.Arguments[0],
				Rhs: this.Arguments[1],
			}
			return t.Eval(es)
		}
		if nameStr == "SameQ" && len(this.Arguments) == 2 {
			t := &Equal{
				Lhs: this.Arguments[0],
				Rhs: this.Arguments[1],
			}
			return t.Eval(es)
		}
		if nameStr == "Plus" {
			t := &Plus{Addends: this.Arguments}
			return t.Eval(es)
		}
		if nameStr == "Times" {
			t := &Times{Multiplicands: this.Arguments}
			return t.Eval(es)
		}
		if nameStr == "Set" && len(this.Arguments) == 2 {
			t := &Set{
				Lhs: this.Arguments[0],
				Rhs: this.Arguments[1],
			}
			return t.Eval(es)
		}
		if nameStr == "SetDelayed" && len(this.Arguments) == 2 {
			t := &SetDelayed{
				Lhs: this.Arguments[0],
				Rhs: this.Arguments[1],
			}
			return t.Eval(es)
		}
		if nameStr == "If" && len(this.Arguments) == 3 {
			t := &If{
				Condition: this.Arguments[0],
				T:         this.Arguments[1],
				F:         this.Arguments[2],
			}
			return t.Eval(es)
		}
		if nameStr == "While" && len(this.Arguments) == 1 {
			t := &While{
				Test: this.Arguments[0],
				Body: &Symbol{"Null"},
			}
			return t.Eval(es)
		}
		if nameStr == "While" && len(this.Arguments) == 2 {
			t := &While{
				Test: this.Arguments[0],
				Body: this.Arguments[1],
			}
			return t.Eval(es)
		}
		if nameStr == "MatchQ" && len(this.Arguments) == 2 {
			t := &MatchQ{
				Expr: this.Arguments[0],
				Form: this.Arguments[1],
			}
			return t.Eval(es)
		}
		if nameStr == "Replace" && len(this.Arguments) == 2 {
			t := &Replace{
				Expr:  this.Arguments[0],
				Rules: this.Arguments[1],
			}
			return t.Eval(es)
		}
		if nameStr == "BasicSimplify" && len(this.Arguments) == 1 {
			t := &BasicSimplify{
				Expr: this.Arguments[0],
			}
			return t.Eval(es)
		}
		if nameStr == "SetLogging" && len(this.Arguments) == 1 {
			t := &SetLogging{
				Expr: this.Arguments[0],
			}
			return t.Eval(es)
		}
		if nameStr == "Definition" && len(this.Arguments) == 1 {
			t := &Definition{
				Expr: this.Arguments[0],
			}
			return t.Eval(es)
		}
		if nameStr == "Sequence" {
			t := &Sequence{Arguments: this.Arguments}
			return t.Eval(es)
		}

		theRes, isDefined := es.GetDef(nameStr, this)
		if isDefined {
			return theRes
		}
	}
	return this
}

func (this *Function) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs.Eval(es)
	}
	this.Name = this.Name.Replace(r, es)
	for i := range this.Arguments {
		this.Arguments[i] = this.Arguments[i].Replace(r, es)
	}
	return this.Eval(es)
}

func (this *Function) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString(this.Name.ToString())
	buffer.WriteString("[")
	for i, e := range this.Arguments {
		buffer.WriteString(e.ToString())
		if i != len(this.Arguments)-1 {
			buffer.WriteString(", ")
		}
	}
	buffer.WriteString("]")
	return buffer.String()
}

func (this *Function) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Function)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual(this.Arguments, other.Arguments, es)
}

func (this *Function) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Function)
	if !ok {
		return false
	}
	if !this.Name.IsSameQ(other.Name, es) {
		return false
	}
	return FunctionIsSameQ(this.Arguments, other.Arguments, es)
}

func (this *Function) IsMatchQ(otherEx Ex, es *EvalState) bool {
	nameAsSym, isNameSym := this.Name.(*Symbol)
	if isNameSym {
		nameStr := nameAsSym.Name
		if IsBlankType(otherEx, nameStr) {
			return true
		}
	}
	other, ok := otherEx.(*Function)
	if !ok {
		return false
	}
	if !this.Name.IsSameQ(other.Name, es) {
		return false
	}
	return NonCommutativeIsMatchQ(this.Arguments, other.Arguments, es)
}

func (this *Function) DeepCopy() Ex {
	var thiscopy = &Function{}
	thiscopy.Name = this.Name
	for i := range this.Arguments {
		thiscopy.Arguments = append(thiscopy.Arguments, this.Arguments[i].DeepCopy())
	}
	return thiscopy
}
