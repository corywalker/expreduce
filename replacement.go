package cas

import "bytes"

func (this *Expression) ToStringRule() string {
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(this.Parts[1].ToString())
	buffer.WriteString(") -> (")
	buffer.WriteString(this.Parts[2].ToString())
	buffer.WriteString(")")
	return buffer.String()
}

func (this *Expression) EvalReplace(es *EvalState) Ex {
	if len(this.Parts) != 3 {
		return this
	}
	this.Parts[1] = this.Parts[1].Eval(es)
	this.Parts[2] = this.Parts[2].Eval(es)
	//_, ok := this.Parts[2].(*Rule)
	rulesRule, ok := HeadAssertion(this.Parts[2], "Rule")
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
	rulesRule, ok := HeadAssertion(this.Parts[2], "Rule")
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
