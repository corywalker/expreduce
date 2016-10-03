package cas

import "fmt"
import "bytes"

// Symbols are defined by a string-based name
type Symbol struct {
	Name string
}

func (this *Symbol) Eval(es *EvalState) Ex {
	//definition, isdefined := es.defined[this.Name]
	definition, isdefined := es.GetDef(this.Name, this)
	if isdefined {
		return definition.DeepCopy().Eval(es)
	}
	return this
}

func (this *Symbol) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	return this
}

func (this *Symbol) ToString() string {
	return fmt.Sprintf("%v", this.Name)
}

func (this *Symbol) IsEqual(other Ex, es *EvalState) string {
	otherConv, ok := other.(*Symbol)
	if !ok {
		return "EQUAL_UNK"
	}
	if this.Name == "False" && otherConv.Name == "True" {
		return "EQUAL_FALSE"
	}
	if this.Name == "True" && otherConv.Name == "False" {
		return "EQUAL_FALSE"
	}
	if this.Name != otherConv.Name {
		return "EQUAL_UNK"
	}
	return "EQUAL_TRUE"
}

func (this *Symbol) IsSameQ(other Ex, es *EvalState) bool {
	otherConv, ok := other.(*Symbol)
	if !ok {
		return false
	}
	if this.Name != otherConv.Name {
		return false
	}
	return true
}

func (this *Symbol) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankTypeCapturing(otherEx, this, "Symbol", es) {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *Symbol) DeepCopy() Ex {
	thiscopy := *this
	return &thiscopy
}

type Set struct {
	Lhs Ex
	Rhs Ex
}

func (this *Set) Eval(es *EvalState) Ex {
	LhsSym, ok := this.Lhs.(*Symbol)
	if !ok {
		return &Error{"Cannot set non-symbol to an expression"}
	}
	var evaluated Ex = this.Rhs.Eval(es)
	//es.defined[LhsSym.Name] = evaluated
	es.Define(LhsSym.Name, LhsSym, evaluated)
	return evaluated
}

func (this *Set) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Lhs = this.Lhs.Replace(r, es)
	this.Rhs = this.Rhs.Replace(r, es)
	return this.Eval(es)
}

func (this *Set) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") = (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Set) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *Set) IsSameQ(otherEx Ex, es *EvalState) bool {
	return false
}

func (this *Set) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *Set) DeepCopy() Ex {
	return &Set{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}

type SetDelayed struct {
	Lhs Ex
	Rhs Ex
}

func (this *SetDelayed) Eval(es *EvalState) Ex {
	LhsSym, ok := this.Lhs.(*Symbol)
	if ok {
		es.Define(LhsSym.Name, LhsSym, this.Rhs)
		return &Symbol{"Null"}
	}
	LhsF, ok := this.Lhs.(*Expression)
	if ok {
		headAsSym, headIsSym := LhsF.Parts[0].(*Symbol)
		if headIsSym {
			es.Define(headAsSym.Name, LhsF, this.Rhs)
			return &Symbol{"Null"}
		}
	}

	return &Error{"Can only set expression to a symbol or a function"}
}

func (this *SetDelayed) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	this.Lhs = this.Lhs.Replace(r, es)
	this.Rhs = this.Rhs.Replace(r, es)
	return this.Eval(es)
}

func (this *SetDelayed) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") := (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *SetDelayed) IsEqual(otherEx Ex, es *EvalState) string {
	return "EQUAL_UNK"
}

func (this *SetDelayed) IsSameQ(otherEx Ex, es *EvalState) bool {
	return false
}

func (this *SetDelayed) IsMatchQ(otherEx Ex, es *EvalState) bool {
	return this.IsSameQ(otherEx, es)
}

func (this *SetDelayed) DeepCopy() Ex {
	return &SetDelayed{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}
