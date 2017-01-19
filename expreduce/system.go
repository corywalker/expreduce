package expreduce

import "math/big"
import "time"
import "fmt"
import "bytes"

func ToStringInfix(parts []Ex, delim string, form string) (bool, string) {
	if form != "InputForm" && form != "OutputForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	var buffer bytes.Buffer
	buffer.WriteString("(")
	for i := 0; i < len(parts); i++ {
		buffer.WriteString(parts[i].StringForm(form))
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	buffer.WriteString(")")
	return true, buffer.String()
}

func (this *Expression) ToStringInfix(form string) (bool, string) {
	if len(this.Parts) != 3 {
		return false, ""
	}
	expr, isExpr := this.Parts[1].(*Expression)
	delim, delimIsStr := this.Parts[2].(*String)
	if !isExpr || !delimIsStr {
		return false, ""
	}
	return ToStringInfix(expr.Parts[1:], delim.Val, form)
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

func ToStringInfixAdvanced(parts []Ex, delim string, surroundEachArg bool, start string, end string, form string) (bool, string) {
	if form != "InputForm" && form != "OutputForm" {
		return false, ""
	}
	if len(parts) < 2 {
		return false, ""
	}
	var buffer bytes.Buffer
	if !surroundEachArg {
		buffer.WriteString(start)
	}
	for i := 0; i < len(parts); i++ {
		if surroundEachArg {
			buffer.WriteString("(")
			buffer.WriteString(parts[i].String())
			buffer.WriteString(")")
		} else {
			buffer.WriteString(parts[i].String())
		}
		if i != len(parts)-1 {
			buffer.WriteString(delim)
		}
	}
	if !surroundEachArg {
		buffer.WriteString(end)
	}
	return true, buffer.String()
}

func GetSystemDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "ExpreduceSetLogging",
		Usage: "`ExpreduceSetLogging[bool]` sets the logging state to `bool`.",
		Details: "Logging output prints to the console. There can be a lot of logging output, especially for more complicated pattern matches.",
		ExpreduceSpecific: true,
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
		Name:       "Definition",
		Attributes: []string{"HoldAll"},
		OmitDocumentation: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			//sym, ok := this.Expr.(*Symbol)
			return &Expression{[]Ex{&Symbol{"Error"}, &String{es.String()}}}
		},
	})
	defs = append(defs, Definition{
		Name:       "Timing",
		Usage: "`Timing[expr]` returns a `List` with the first element being the time in seconds for the evaluation of `expr`, and the second element being the result.",
		Attributes: []string{"HoldAll", "SequenceHold"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			start := time.Now()
			res := this.Parts[1].Eval(es)
			elapsed := time.Since(start).Seconds()
			return &Expression{[]Ex{&Symbol{"List"}, &Flt{big.NewFloat(elapsed)}, res}}
		},
		SimpleExamples: []TestInstruction{
			&ExampleOnlyInstruction{"{0.00167509, 5000000050000000}", "Timing[Sum[a, {a, 100000000}]]"},
		},
	})
	defs = append(defs, Definition{
		Name: "Print",
		Usage: "`Print[expr]` prints the string representation of `expr` to the console and returns `Null`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			fmt.Printf("%s\n", this.Parts[1].String())
			return &Symbol{"Null"}
		},
	})
	defs = append(defs, Definition{
		Name:       "CompoundExpression",
		Usage: "`CompoundExpression[e1, e2, ...]` evaluates each expression in order and returns the result of the last one.",
		Attributes: []string{"HoldAll", "ReadProtected"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			var toReturn Ex
			for i := 1; i < len(this.Parts); i++ {
				toReturn = this.Parts[i].Eval(es)
			}
			return toReturn
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"The result of the first expression is not included in the output, but the result of the second is:"},
			&SameTest{"3", "a = 5; a - 2"},
			&TestComment{"Including a trailing semicolon causes the expression to return `Null`:"},
			&SameTest{"Null", "a = 5; a - 2;"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Head",
		Usage: "`Head[expr]` returns the head of the expression.",
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
		SimpleExamples: []TestInstruction{
			&SameTest{"f", "Head[f[x]]"},
			&SameTest{"Symbol", "Head[x]"},
			&SameTest{"List", "Head[{x}]"},
			&SameTest{"Plus", "Head[a + b]"},
			&SameTest{"Integer", "Head[1]"},
			&SameTest{"Real", "Head[1.]"},
			&SameTest{"Rational", "Head[2/7]"},
			&SameTest{"Rational", "Head[1/7]"},
			&SameTest{"String", "Head[\"1\"]"},
			&SameTest{"Plus", "Head[Head[(a + b)[x]]]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "MessageName",
		Usage: "`sym::msg` references a particular message for `sym`.",
		Attributes: []string{"HoldFirst", "ReadProtected"},
		SimpleExamples: []TestInstruction{
			&TestComment{"`MessageName` is used to store the usage messages of built-in symbols:"},
			&SameTest{"\"`sym::msg` references a particular message for `sym`.\"", "MessageName::usage"},
		},
	})
	defs = append(defs, Definition{
		Name:     "Infix",
		Usage: "`Infix[expr, sep]` represents `expr` in infix form with separator `sep` when converted to a string.",
		toString: (*Expression).ToStringInfix,
		SimpleExamples: []TestInstruction{
			&SameTest{"\"(bar|fuzz|zip)\"", "Infix[foo[bar, fuzz, zip], \"|\"] // ToString"},
		},
	})
	return
}
