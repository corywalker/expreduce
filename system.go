package cas

import "math/big"
import "time"
import "fmt"
import "bytes"

func (this *Expression) ToStringInfix(form string) (bool, string) {
	if len(this.Parts) != 3 {
		return false, ""
	}
	expr, isExpr := this.Parts[1].(*Expression)
	delim, delimIsStr := this.Parts[2].(*String)
	if !isExpr || !delimIsStr {
		return false, ""
	}
	if len(expr.Parts) < 3 {
		return false, ""
	}
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i := 1; i < len(expr.Parts); i++ {
		buffer.WriteString(expr.Parts[i].String())
		if i != len(expr.Parts)-1 {
			buffer.WriteString(delim.Val)
		}
	}
	buffer.WriteString(")")
	return true, buffer.String()
}

func TrueQ(ex Ex) bool {
	asSym, isSym := ex.(*Symbol)
	if !isSym {
		return false
	}
	if !(asSym.Name == "True") {
		return false
	}
	return true
}

func (this *Expression) ToStringInfixAdvanced(form string) (bool, string) {
	if len(this.Parts) != 6 {
		return false, ""
	}
	expr, isExpr := this.Parts[1].(*Expression)
	delim, delimIsStr := this.Parts[2].(*String)
	start, startIsStr := this.Parts[4].(*String)
	end, endIsStr := this.Parts[5].(*String)
	if !isExpr || !delimIsStr || !startIsStr || !endIsStr {
		return false, ""
	}
	if len(expr.Parts) < 3 {
		return false, ""
	}
	surroundEachArg := TrueQ(this.Parts[3])
	var buffer bytes.Buffer
	if !surroundEachArg {
		buffer.WriteString(start.Val)
	}
	for i := 1; i < len(expr.Parts); i++ {
		if surroundEachArg {
			buffer.WriteString("(")
			buffer.WriteString(expr.Parts[i].String())
			buffer.WriteString(")")
		} else {
			buffer.WriteString(expr.Parts[i].String())
		}
		if i != len(expr.Parts)-1 {
			buffer.WriteString(delim.Val)
		}
	}
	if !surroundEachArg {
		buffer.WriteString(end.Val)
	}
	return true, buffer.String()
}

func GetSystemDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "SetLogging",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
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
		},
	})
	defs = append(defs, Definition{
		name: "Definition",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			//sym, ok := this.Expr.(*Symbol)
			return &Expression{[]Ex{&Symbol{"Error"}, &String{es.String()}}}
		},
	})
	defs = append(defs, Definition{
		name: "Timing",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			start := time.Now()
			res := this.Parts[1].Eval(es)
			elapsed := time.Since(start).Seconds()
			return &Expression{[]Ex{&Symbol{"List"}, &Flt{big.NewFloat(elapsed)}, res}}
		},
	})
	defs = append(defs, Definition{
		name: "Print",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			fmt.Printf("%s\n", this.Parts[1].String())
			return &Symbol{"Null"}
		},
	})
	defs = append(defs, Definition{
		name: "CompoundExpression",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			var toReturn Ex
			for i := 1; i < len(this.Parts); i++ {
				toReturn = this.Parts[i].Eval(es)
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		name: "Head",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
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
		},
	})
	defs = append(defs, Definition{
		name: "MessageName",
		rules: map[string]string{
			"MessageName[symmatch_,tagmatch_Symbol]": "MessageName[symmatch,ToString[tagmatch,InputForm]]",
		},
	})
	defs = append(defs, Definition{
		name: "Infix",
		toString: (*Expression).ToStringInfix,
	})
	defs = append(defs, Definition{
		name: "InfixAdvanced",
		toString: (*Expression).ToStringInfixAdvanced,
	})
	return
}
