package cas

import "fmt"

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

func (this *Symbol) StringForm(form string) string {
	if len(this.Name) == 0 {
		return "<EMPTYSYM>"
	}
	return fmt.Sprintf("%v", this.Name)
}

func (this *Symbol) String() string {
	return this.StringForm("InputForm")
}

func (this *Symbol) IsEqual(other Ex, cl *CASLogger) string {
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

func (this *Symbol) DeepCopy() Ex {
	thiscopy := *this
	return &thiscopy
}

func GetSymbolDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "Set",
		rules: map[string]string{
			"Format[Set[lhs_, rhs_], InputForm|OutputForm]": "InfixAdvanced[{lhs, rhs}, \" = \", True, \"(\", \")\"]",
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
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
		},
	})
	defs = append(defs, Definition{
		name:      "SetDelayed",
		rules: map[string]string{
			"Format[SetDelayed[lhs_, rhs_], InputForm|OutputForm]": "InfixAdvanced[{lhs, rhs}, \" := \", True, \"(\", \")\"]",
		},
		bootstrap: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
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
		},
	})
	return
}
