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
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " = ", true, "(", ")", form)
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			LhsSym, ok := this.Parts[1].(*Symbol)
			if ok {
				es.Define(LhsSym.Name, LhsSym, this.Parts[2])
				return this.Parts[2]
			}
			LhsF, ok := this.Parts[1].(*Expression)
			if ok {
				headAsSym, headIsSym := LhsF.Parts[0].(*Symbol)
				if headIsSym {
					es.Define(headAsSym.Name, LhsF, this.Parts[2])
					return this.Parts[2]
				}
			}

			return &Expression{[]Ex{&Symbol{"Error"}, &String{"Can only set expression to a symbol or a function"}}}
		},
		tests: []TestInstruction{
			&StringTest{"3", "x=1+2"},
			&StringTest{"3", "x"},
			&StringTest{"4", "x+1"},
			// To make sure the result does not change
			&StringTest{"4", "x+1"},

			&StringTest{"3", "x=1+2"},
			&StringTest{"6", "x*2"},
			// To make sure the result does not change
			&StringTest{"6", "x=x*2"},
			&StringTest{"36", "x=x*x"},

			&StringTest{"a^2", "y=a*a"},
			&StringTest{"a^4", "y=y*y"},
			&StringTest{"2", "a=2"},
			&StringTest{"16", "y"},
		},
	})
	defs = append(defs, Definition{
		name: "SetDelayed",
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " := ", true, "(", ")", form)
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
		tests: []TestInstruction{
			// Test function definitions
			&SameTest{"Null", "testa[x_] := x*2"},
			&SameTest{"Null", "testa[x_Integer] := x*3"},
			&SameTest{"Null", "testa[x_Real] := x*4"},
			&SameTest{"8.", "testa[2.]"},
			&SameTest{"6", "testa[2]"},
			&SameTest{"2 * k", "testa[k]"},
			&SameTest{"Null", "testb[x_Real] := x*4"},
			&SameTest{"Null", "testb[x_Integer] := x*3"},
			&SameTest{"Null", "testb[x_] := x*2"},
			&SameTest{"8.", "testb[2.]"},
			&SameTest{"6", "testb[2]"},
			&SameTest{"2 * k", "testb[k]"},
			&SameTest{"testa", "testa"},
			&SameTest{"testb", "testb"},
			&SameTest{"Null", "testb[x_] := x*5"},
			&SameTest{"5 * k", "testb[k]"},
			&SameTest{"8.", "testb[2.]"},
			&SameTest{"Null", "testb[x_Real + sym] := 5"},
			&SameTest{"5", "testb[2.+sym]"},
			&SameTest{"5", "testb[sym+2.]"},
			&SameTest{"Null", "testb[x_Real + sym] := 6"},
			&SameTest{"6", "testb[2.+sym]"},
			&SameTest{"6", "testb[sym+2.]"},
			&SameTest{"Null", "dist[x_, y_]:=(x^2 + y^2)^.5"},
			&SameTest{"(j^2+k^2)^.5", "dist[j,k]"},

			// Test pattern name conflicts.
			&SameTest{"Null", "foo[k_, m_] := bar[k, m]"},
			&SameTest{"bar[m, 2]", "foo[m, 2]"},
			&SameTest{"Null", "fizz[m_, k_] := buzz[m, k]"},
			&SameTest{"buzz[m, 2]", "fizz[m, 2]"},
		},
	})
	return
}
