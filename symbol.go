package cas

import "fmt"
import "bytes"

// Symbols are defined by a string-based name
type Symbol struct {
	Name string
}

func (v *Symbol) Eval(es *EvalState) Ex {
	return v
}

func (v *Symbol) ToString() string {
	return fmt.Sprintf("%v", v.Name)
}

func (this *Symbol) IsEqual(other Ex, es *EvalState) string {
	otherConv, ok := other.(*Symbol)
	if !ok {
		return "EQUAL_FALSE"
	}
	if this.Name != otherConv.Name {
		return "EQUAL_FALSE"
	}
	return "EQUAL_TRUE"
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
	es.defined[LhsSym.Name] = evaluated
	return evaluated
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

type SetDelayed struct {
	Lhs Ex
	Rhs Ex
}

func (this *SetDelayed) Eval(es *EvalState) Ex {
	LhsSym, ok := this.Lhs.(*Symbol)
	if !ok {
		return &Error{"Cannot set non-symbol to an expression"}
	}
	es.defined[LhsSym.Name] = this.Rhs
	return this.Rhs
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
