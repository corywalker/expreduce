package cas

func (this *Expression) EvalSetLogging(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	sym, ok := this.Parts[1].(*Symbol)
	if ok {
		if sym.Name == "True" {
			es.DebugOn()
			return &Symbol{"Null"}
		} else if sym.Name == "False" {
			es.DebugOff()
			return &Symbol{"Null"}
		}
	}
	return this
}

func (this *Expression) EvalDefinition(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	//sym, ok := this.Expr.(*Symbol)
	return &Expression{[]Ex{&Symbol{"Error"}, &String{es.ToString()}}}
}
