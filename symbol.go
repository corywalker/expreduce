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

func (this *Symbol) Replace(r *Expression, es *EvalState) Ex {
	if IsMatchQ(this, r.Parts[1], es) {
		return r.Parts[2]
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

func (this *Expression) EvalSet(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	var evaluated Ex = this.Parts[2].Eval(es)
	LhsSym, ok := this.Parts[1].(*Symbol)
	if ok {
		es.Define(LhsSym.Name, LhsSym, evaluated)
		return evaluated
	}
	LhsF, ok := this.Parts[1].(*Expression)
	if ok {
		headAsSym, headIsSym := LhsF.Parts[0].(*Symbol)
		if headIsSym {
			es.Define(headAsSym.Name, LhsF, evaluated)
			return evaluated
		}
	}

	return &Expression{[]Ex{&Symbol{"Error"}, &String{"Can only set expression to a symbol or a function"}}}
}

func (this *Expression) ToStringSet() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].ToString())
	buffer.WriteString(") = (")
	buffer.WriteString(this.Parts[2].ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Expression) EvalSetDelayed(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}

	LhsSym, ok := this.Parts[1].(*Symbol)
	if ok {
		es.Define(LhsSym.Name, LhsSym, this.Parts[2])
		return &Symbol{"Null"}
	}
	LhsF, ok := this.Parts[1].(*Expression)
	if ok {
		headAsSym, headIsSym := LhsF.Parts[0].(*Symbol)
		if headIsSym {
			es.Define(headAsSym.Name, LhsF, this.Parts[2])
			return &Symbol{"Null"}
		}
	}

	return &Expression{[]Ex{&Symbol{"Error"}, &String{"Can only set expression to a symbol or a function"}}}
}

func (this *Expression) ToStringSetDelayed() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].ToString())
	buffer.WriteString(") := (")
	buffer.WriteString(this.Parts[2].ToString())
	buffer.WriteString(")")
	return buffer.String()
}
