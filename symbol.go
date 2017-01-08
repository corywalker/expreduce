package cas

import "fmt"
import "sort"

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

type Attributes struct {
	Orderless bool
	Flat bool
	OneIdentity bool
	Listable bool
	Constant bool
	NumericFunction bool
	Protected bool
	Locked bool
	ReadProtected bool
	HoldFirst bool
	HoldRest bool
	HoldAll bool
	HoldAllComplete bool
	NHoldFirst bool
	NHoldRest bool
	NHoldAll bool
	SequenceHold bool
	Temporary bool
	Stub bool
}

func (this *Symbol) Attrs(es *EvalState) Attributes {
	def, isDef := es.defined[this.Name]
	if !isDef {
		return Attributes{}
	}
	return def.attributes
}

func stringsToAttributes(strings []string) Attributes {
	attrs := Attributes{}
	for _, s := range strings {
		if s == "Orderless" {
			attrs.Orderless = true
		}
		if s == "Flat" {
			attrs.Flat = true
		}
		if s == "OneIdentity" {
			attrs.OneIdentity = true
		}
		if s == "Listable" {
			attrs.Listable = true
		}
		if s == "Constant" {
			attrs.Constant = true
		}
		if s == "NumericFunction" {
			attrs.NumericFunction = true
		}
		if s == "Protected" {
			attrs.Protected = true
		}
		if s == "Locked" {
			attrs.Locked = true
		}
		if s == "ReadProtected" {
			attrs.ReadProtected = true
		}
		if s == "HoldFirst" {
			attrs.HoldFirst = true
		}
		if s == "HoldRest" {
			attrs.HoldRest = true
		}
		if s == "HoldAll" {
			attrs.HoldAll = true
		}
		if s == "HoldAllComplete" {
			attrs.HoldAllComplete = true
		}
		if s == "NHoldFirst" {
			attrs.NHoldFirst = true
		}
		if s == "NHoldRest" {
			attrs.NHoldRest = true
		}
		if s == "NHoldAll" {
			attrs.NHoldAll = true
		}
		if s == "SequenceHold" {
			attrs.SequenceHold = true
		}
		if s == "Temporary" {
			attrs.Temporary = true
		}
		if s == "Stub" {
			attrs.Stub = true
		}
	}
	return attrs
}

func (this *Attributes) toStrings() []string {
	var strings []string
	if this.Orderless {
		strings = append(strings, "Orderless")
	}
	if this.Flat {
		strings = append(strings, "Flat")
	}
	if this.OneIdentity {
		strings = append(strings, "OneIdentity")
	}
	if this.Listable {
		strings = append(strings, "Listable")
	}
	if this.Constant {
		strings = append(strings, "Constant")
	}
	if this.NumericFunction {
		strings = append(strings, "NumericFunction")
	}
	if this.Protected {
		strings = append(strings, "Protected")
	}
	if this.Locked {
		strings = append(strings, "Locked")
	}
	if this.ReadProtected {
		strings = append(strings, "ReadProtected")
	}
	if this.HoldFirst {
		strings = append(strings, "HoldFirst")
	}
	if this.HoldRest {
		strings = append(strings, "HoldRest")
	}
	if this.HoldAll {
		strings = append(strings, "HoldAll")
	}
	if this.HoldAllComplete {
		strings = append(strings, "HoldAllComplete")
	}
	if this.NHoldFirst {
		strings = append(strings, "NHoldFirst")
	}
	if this.NHoldRest {
		strings = append(strings, "NHoldRest")
	}
	if this.NHoldAll {
		strings = append(strings, "NHoldAll")
	}
	if this.SequenceHold {
		strings = append(strings, "SequenceHold")
	}
	if this.Temporary {
		strings = append(strings, "Temporary")
	}
	if this.Stub {
		strings = append(strings, "Stub")
	}

	sort.Strings(strings)
	return strings
}

func GetSymbolDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		name: "Set",
		attributes: []string{"HoldFirst", "SequenceHold"},
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
		attributes: []string{"HoldAll", "SequenceHold"},
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
	defs = append(defs, Definition{
		name: "Attributes",
		attributes: []string{"HoldAll", "Listable"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			sym, isSym := this.Parts[1].(*Symbol)
			if !isSym {
				return this
			}

			toReturn := &Expression{[]Ex{&Symbol{"List"}}}
			def, isDef := es.defined[sym.Name]
			if isDef {
				for _, s := range def.attributes.toStrings() {
					toReturn.Parts = append(toReturn.Parts, &Symbol{s})
				}
			}
			return toReturn
		},
		tests: []TestInstruction{
			&SameTest{"{Protected, ReadProtected}", "Attributes[Infinity]"},
			&SameTest{"{HoldAll, Listable, Protected}", "Attributes[Attributes]"},
			&SameTest{"{Flat, Listable, NumericFunction, OneIdentity, Orderless, Protected}", "Attributes[Plus]"},
		},
	})
	defs = append(defs, Definition{
		name: "Clear",
		attributes: []string{"HoldAll"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			for _, arg := range this.Parts[1:] {
				es.Debugf("arg: %v", arg)
				sym, isSym := arg.(*Symbol)
				if isSym {
					es.Clear(sym.Name)
				}
			}
			return &Symbol{"Null"}
		},
		tests: []TestInstruction{
			&SameTest{"a", "a"},
			&SameTest{"5", "a = 5"},
			&SameTest{"6", "b = 6"},
			&SameTest{"7", "c = 7"},
			&SameTest{"5", "a"},
			&SameTest{"Null", "Clear[a, 99, b]"},
			&StringTest{"a", "a"},
			&StringTest{"b", "b"},
			&StringTest{"7", "c"},
		},
	})
	return
}
