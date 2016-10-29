package cas

import "math/big"
import "time"
import "fmt"

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

func (this *Expression) EvalPrint(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	fmt.Printf("%s\n", this.Parts[1].String())
	return &Symbol{"Null"}
}

func (this *Expression) EvalCompoundExpression(es *EvalState) Ex {
	var toReturn Ex
	for i := 1; i < len(this.Parts); i++ {
		toReturn = this.Parts[i].Eval(es)
	}
	return toReturn
}

func (this *Expression) EvalHead(es *EvalState) Ex {
	if len(this.Parts) != 2 {
		return this
	}

	_, IsFlt := this.Parts[1].(*Flt)
	if IsFlt {
		return &Symbol{"Real"}
	}
	_, IsInteger := this.Parts[1].(*Integer)
	if IsInteger {
		return &Symbol{"Integer"}
	}
	_, IsString := this.Parts[1].(*String)
	if IsString {
		return &Symbol{"String"}
	}
	_, IsSymbol := this.Parts[1].(*Symbol)
	if IsSymbol {
		return &Symbol{"Symbol"}
	}
	_, IsRational := this.Parts[1].(*Rational)
	if IsRational {
		return &Symbol{"Rational"}
	}
	asExpr, IsExpression := this.Parts[1].(*Expression)
	if IsExpression {
		return asExpr.Parts[0].DeepCopy()
	}
	return this
}
