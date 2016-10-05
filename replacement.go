package cas

import "bytes"

type Rule struct {
	Lhs Ex
	Rhs Ex
}

func (this *Rule) Eval(es *EvalState) Ex {
	this.Lhs = this.Lhs.Eval(es)
	this.Rhs = this.Rhs.Eval(es)
	return this
}

func (this *Rule) Replace(r *Rule, es *EvalState) Ex {
	if this.IsMatchQ(r.Lhs, es) {
		return r.Rhs
	}
	return this
}

func (this *Rule) ToString() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Lhs.ToString())
	buffer.WriteString(") -> (")
	buffer.WriteString(this.Rhs.ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Rule) IsEqual(otherEx Ex, es *EvalState) string {
	other, ok := otherEx.(*Rule)
	if !ok {
		return "EQUAL_UNK"
	}
	return FunctionIsEqual([]Ex{
		this.Lhs,
		this.Rhs,
	}, []Ex{
		other.Lhs,
		other.Rhs,
	}, es)
}

func (this *Rule) IsSameQ(otherEx Ex, es *EvalState) bool {
	other, ok := otherEx.(*Rule)
	if !ok {
		return false
	}
	return FunctionIsSameQ([]Ex{
		this.Lhs,
		this.Rhs,
	}, []Ex{
		other.Lhs,
		other.Rhs,
	}, es)
}

func (this *Rule) IsMatchQ(otherEx Ex, es *EvalState) bool {
	if IsBlankType(otherEx, "Rule") {
		return true
	}
	return this.IsSameQ(otherEx, es)
}

func (this *Rule) DeepCopy() Ex {
	return &Rule{
		this.Lhs.DeepCopy(),
		this.Rhs.DeepCopy(),
	}
}

func (this *Expression) EvalReplace(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}
	this.Parts[1] = this.Parts[1].Eval(es)
	this.Parts[2] = this.Parts[2].Eval(es)
	//_, ok := this.Parts[2].(*Rule)
	rulesRule, ok := this.Parts[2].(*Rule)
	if ok {
		oldVars := es.GetDefinedSnapshot()
		newEx := this.Parts[1].Replace(rulesRule, es)
		es.ClearPD()
		newEx = newEx.Eval(es)
		es.defined = oldVars
		return newEx
		//return this
	}
	return this
}

func (this *Expression) ToStringReplace() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].ToString())
	buffer.WriteString(") /. (")
	buffer.WriteString(this.Parts[2].ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Expression) EvalReplaceRepeated(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}
	es.log.Infof(es.Pre() + "Starting ReplaceRepeated.")
	this.Parts[1] = this.Parts[1].Eval(es)
	this.Parts[2] = this.Parts[2].Eval(es)
	//_, ok := this.Parts[2].(*Rule)
	rulesRule, ok := this.Parts[2].(*Rule)
	if ok {
		isSame := false
		oldEx := this.Parts[1]
		es.log.Infof(es.Pre()+"In ReplaceRepeated. Initial expr: %v", oldEx.ToString())
		for !isSame {
			oldVars := es.GetDefinedSnapshot()
			newEx := oldEx.DeepCopy().Replace(rulesRule, es)
			es.ClearPD()
			newEx = newEx.Eval(es)
			es.defined = oldVars
			es.log.Infof(es.Pre()+"In ReplaceRepeated. New expr: %v", newEx.ToString())

			oldVars = es.GetDefinedSnapshot()
			if oldEx.IsSameQ(newEx, es) {
				isSame = true
			}
			es.ClearPD()
			es.defined = oldVars
			oldEx = newEx
		}
		return oldEx
		//return this
	}
	return this
}

func (this *Expression) ToStringReplaceRepeated() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].ToString())
	buffer.WriteString(") //. (")
	buffer.WriteString(this.Parts[2].ToString())
	buffer.WriteString(")")
	return buffer.String()
}
