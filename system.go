package cas

import "math/big"
import "time"

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
	return &Expression{[]Ex{&Symbol{"Error"}, &String{es.String()}}}
}

func (this *Expression) EvalTiming(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	start := time.Now()
	res := this.Parts[1].Eval(es)
	elapsed := time.Since(start).Seconds()
	return &Expression{[]Ex{&Symbol{"List"}, &Flt{big.NewFloat(elapsed)}, res}}
}
