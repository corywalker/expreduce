package expreduce

import "math/big"
import "time"
import "fmt"
import "github.com/op/go-logging"

func exprToN(es *EvalState, e Ex) Ex {
	asInt, isInt := e.(*Integer)
	if isInt {
		toReturn, _ := IntegerToFlt(asInt)
		return toReturn
	}
	asRat, isRat := e.(*Rational)
	if isRat {
		toReturn, _ := RationalToFlt(asRat)
		return toReturn
	}
	asExpr, isExpr := e.(*Expression)
	if isExpr {
		toReturn, defined, _ := es.GetDef(
			"N",
			NewExpression([]Ex{&Symbol{"N"}, e}),
		)
		if defined {
			return toReturn
		}
		exToReturn := NewEmptyExpression()
		for _, part := range asExpr.Parts {
			toAdd, defined, _ := es.GetDef(
				"N",
				NewExpression([]Ex{&Symbol{"N"}, part}),
			)
			if !defined {
				toAdd = exprToN(es, part)
			}
			exToReturn.Parts = append(exToReturn.Parts, toAdd)
		}
		return exToReturn
	}
	return e.DeepCopy()
}

func GetSystemDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:              "ExpreduceSetLogging",
		Usage:             "`ExpreduceSetLogging[bool, level]` sets the logging state to `bool` and the level to `level`.",
		Details:           "Logging output prints to the console. There can be a lot of logging output, especially for more complicated pattern matches. Valid levels are `Debug`, `Info`, `Notice`, `Warning`, `Error`, and `Critical`.",
		ExpreduceSpecific: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			sym, ok := this.Parts[1].(*Symbol)
			if ok {
				if sym.Name == "True" {
			        levelSym, lsOk := this.Parts[2].(*Symbol)
					if !lsOk {
					  return NewExpression([]Ex{&Symbol{"Error"}, &String{"Invalid level."}})
					}
					if levelSym.Name == "Debug" {
						es.DebugOn(logging.DEBUG)
					} else if levelSym.Name == "Info" {
						es.DebugOn(logging.INFO)
					} else if levelSym.Name == "Notice" {
						es.DebugOn(logging.NOTICE)
					} else {
					  return NewExpression([]Ex{&Symbol{"Error"}, &String{"Invalid level."}})
					}
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
		Name:              "ExpreduceDefinitionTimes",
		Usage:             "`ExpreduceDefinitionTimes[]` prints the time in seconds evaluating various definitions.",
		Details:           "For timing information to record, debug mode must be enabled through `ExpreduceSetLogging`.",
		ExpreduceSpecific: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			fmt.Println(es.lhsDefTimeCounter.String())
			fmt.Println(es.defTimeCounter.String())

			return &Symbol{"Null"}
		},
	})
	defs = append(defs, Definition{
		Name:       "Attributes",
		Usage:      "`Attributes[sym]` returns a `List` of attributes for `sym`.",
		Attributes: []string{"HoldAll", "Listable"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			sym, isSym := this.Parts[1].(*Symbol)
			if !isSym {
				return this
			}

			toReturn := NewExpression([]Ex{&Symbol{"List"}})
			def, isDef := es.defined[sym.Name]
			if isDef {
				for _, s := range def.attributes.toStrings() {
					toReturn.Parts = append(toReturn.Parts, &Symbol{s})
				}
			}
			return toReturn
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{Protected, ReadProtected}", "Attributes[Infinity]"},
			&SameTest{"{HoldAll, Listable, Protected}", "Attributes[Attributes]"},
			&SameTest{"{Flat, Listable, NumericFunction, OneIdentity, Orderless, Protected}", "Attributes[Plus]"},
			&TestComment{"The default set of attributes is the empty list:"},
			&SameTest{"{}", "Attributes[undefinedSym]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"Only symbols can have attributes:"},
			&SameTest{"Attributes[2]", "Attributes[2]"},
			&SameTest{"Attributes[a^2]", "Attributes[a^2]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Clear",
		Usage:      "`Clear[sym1, sym2, ...]` clears the symbol definitions from the evaluation context.",
		Attributes: []string{"HoldAll"},
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
		SimpleExamples: []TestInstruction{
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
	defs = append(defs, Definition{
		Name:              "Definition",
		Attributes:        []string{"HoldAll"},
		OmitDocumentation: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			sym, ok := this.Parts[1].(*Symbol)
			if !ok {
				return this
			}
			def, isd := es.defined[sym.Name]
			if !isd {
				return &Symbol{"Null"}
			}
			return NewExpression([]Ex{&Symbol{"Error"}, &String{def.String()}})
		},
	})
	defs = append(defs, Definition{
		Name:       "Set",
		Usage:      "`lhs = rhs` sets `lhs` to stand for `rhs`.",
		Attributes: []string{"HoldFirst", "SequenceHold"},
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

			es.Define(this.Parts[1], this.Parts[2])
			return this.Parts[2]
		},
		SimpleExamples: []TestInstruction{
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
		FurtherExamples: []TestInstruction{
			&TestComment{"`Set` has the `HoldFirst` attribute, meaning `rhs` is evaluated before assignment:"},
			&SameTest{"{HoldFirst, Protected, SequenceHold}", "Attributes[Set]"},
			&TestComment{"`SetDelayed` has the `HoldAll` attribute, meaning `rhs` is not evaluated during assignment:"},
			&SameTest{"{HoldAll, Protected, SequenceHold}", "Attributes[SetDelayed]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "SetDelayed",
		Usage:      "`lhs := rhs` sets `lhs` to stand for `rhs`, with `rhs` not being evaluated until it is referenced by `lhs`.",
		Attributes: []string{"HoldAll", "SequenceHold"},
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " := ", true, "(", ")", form)
		},
		Bootstrap: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			es.Define(this.Parts[1], this.Parts[2])
			return &Symbol{"Null"}
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"`SetDelayed` can be used to define functions:"},
			&SameTest{"Null", "testa[x_] := x*2"},
			&SameTest{"Null", "testa[x_Integer] := x*3"},
			&SameTest{"Null", "testa[x_Real] := x*4"},
			&TestComment{"The more \"specific\" definitions match first:"},
			&SameTest{"8.", "testa[2.]"},
			&SameTest{"6", "testa[2]"},
			&TestComment{"There is no specific match for `testa[k]`, so the general case matches:"},
			&SameTest{"2 * k", "testa[k]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"`Set` has the `HoldFirst` attribute, meaning `rhs` is evaluated before assignment:"},
			&SameTest{"{HoldFirst, Protected, SequenceHold}", "Attributes[Set]"},
			&TestComment{"`SetDelayed` has the `HoldAll` attribute, meaning `rhs` is not evaluated during assignment:"},
			&SameTest{"{HoldAll, Protected, SequenceHold}", "Attributes[SetDelayed]"},
		},
		Tests: []TestInstruction{
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
		Name:       "Timing",
		Usage:      "`Timing[expr]` returns a `List` with the first element being the time in seconds for the evaluation of `expr`, and the second element being the result.",
		Attributes: []string{"HoldAll", "SequenceHold"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			start := time.Now()
			res := this.Parts[1].Eval(es)
			elapsed := time.Since(start).Seconds()
			return NewExpression([]Ex{&Symbol{"List"}, &Flt{big.NewFloat(elapsed)}, res})
		},
		SimpleExamples: []TestInstruction{
			&ExampleOnlyInstruction{"{0.00167509, 5000000050000000}", "Timing[Sum[a, {a, 100000000}]]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Print",
		Usage: "`Print[expr1, expr2, ...]` prints the string representation of the expressions to the console and returns `Null`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) < 2 {
				return this
			}

			for i := 1; i < len(this.Parts); i++ {
				fmt.Printf("%s", this.Parts[i].String())
			}
			fmt.Printf("\n")
			return &Symbol{"Null"}
		},
	})
	defs = append(defs, Definition{
		Name:       "MessageName",
		Usage:      "`sym::msg` references a particular message for `sym`.",
		Attributes: []string{"HoldFirst", "ReadProtected"},
		SimpleExamples: []TestInstruction{
			&TestComment{"`MessageName` is used to store the usage messages of built-in symbols:"},
			&SameTest{"\"`sym::msg` references a particular message for `sym`.\"", "MessageName::usage"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Trace",
		Usage:      "`Trace[expr]` traces the evaluation of `expr`.",
		Attributes: []string{"HoldAll"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			// TODO: this will prevent nested Trace calls. Figure out a better
			// way.

			// Put system in trace mode:
			es.trace = NewExpression([]Ex{&Symbol{"List"}})
			// Evaluate first argument in trace mode:
			this.Parts[1].Eval(es)
			if len(es.trace.Parts) > 2 {
				// Take system out of trace mode:
				toReturn := es.trace.DeepCopy()
				es.trace = nil
				return toReturn
			}
			es.trace = nil
			return NewExpression([]Ex{&Symbol{"List"}})
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"List[HoldForm[Plus[1, 2]], HoldForm[3]]", "1 + 2 // Trace"},
			&SameTest{"List[List[HoldForm[Plus[1, 3]], HoldForm[4]], HoldForm[Plus[4, 2]], HoldForm[6]]", "(1 + 3) + 2 // Trace"},
			&SameTest{"List[List[HoldForm[Plus[1, 3]], HoldForm[4]], HoldForm[Plus[2, 4]], HoldForm[6]]", "2 + (1 + 3) // Trace"},
		},
		Tests: []TestInstruction{
			&SameTest{"{}", "Trace[a + b + c]"},
			&SameTest{"{}", "Trace[1]"},
			&SameTest{"{HoldForm[2^2], HoldForm[4]}", "Trace[2^2]"},
			&SameTest{"{{HoldForm[2^2], HoldForm[4]}, HoldForm[4*5], HoldForm[20]}", "Trace[2^2*5]"},
			&SameTest{"{{{HoldForm[2^2], HoldForm[4]}, HoldForm[4*5], HoldForm[20]}, HoldForm[20 + 4], HoldForm[24]}", "Trace[2^2*5+4]"},
			&SameTest{"{{{HoldForm[2^2], HoldForm[4]}, {HoldForm[3^3], HoldForm[27]}, HoldForm[4*27*5], HoldForm[540]}, HoldForm[540 + 4], HoldForm[544]}", "Trace[2^2*3^3*5+4]"},
			&SameTest{"{HoldForm[b + a], HoldForm[a + b]}", "Trace[b+a]"},
			&SameTest{"{}", "Trace[a+foo[a,b]]"},
			&SameTest{"{HoldForm[foo[Sequence[a, b]]], HoldForm[foo[a, b]]}", "Trace[foo[Sequence[a,b]]]"},
		},
		KnownFailures: []TestInstruction{
			// We are close with this one but not quite:
			&SameTest{"{{{HoldForm[a*a], HoldForm[a^2]}, HoldForm[foo[a^2, b]]}, HoldForm[a + foo[a^2, b]]}", "Trace[a+foo[a*a,b]]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "N",
		Usage: "`N[expr]` attempts to convert `expr` to a numeric value.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			return exprToN(es, this.Parts[1])
		},
		Tests: []TestInstruction{
			&SameTest{"2.", "N[2]"},
			&SameTest{"0.5", "N[1/2]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Listable",
		Usage: "`Listable` is an attribute that calls for functions to automatically map over lists.",
		SimpleExamples: []TestInstruction{
			&SameTest{"{1, 1, 1, 0}", "Boole[{True, True, True, False}]"},
			&SameTest{"{False, True, True}", "Positive[{-1, 4, 5}]"},
			&SameTest{"{{False, True, True}}", "Positive[{{-1, 4, 5}}]"},
			&SameTest{"{{False, True, True}, {True, False}}", "Positive[{{-1, 4, 5}, {6, -1}}]"},
		},
		Tests: []TestInstruction{
			&SameTest{"{Positive[-1, 2], Positive[4, 2], Positive[5, 2]}", "Positive[{-1, 4, 5}, 2]"},
			&SameTest{"Positive[{-1, 4, 5}, {1, 2}]", "Positive[{-1, 4, 5}, {1, 2}]"},
			&SameTest{"{Positive[-1, 1], Positive[4, 2], Positive[5, 3]}", "Positive[{-1, 4, 5}, {1, 2, 3}]"},
		},
	})
	defs = append(defs, Definition{
		Name: "ExpreduceFlatFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes: []string{"Flat"},
	})
	defs = append(defs, Definition{
		Name: "ExpreduceOrderlessFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes: []string{"Orderless"},
	})
	defs = append(defs, Definition{
		Name: "ExpreduceOneIdentityFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes: []string{"OneIdentity"},
	})
	defs = append(defs, Definition{
		Name: "ExpreduceFlatFn2",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes: []string{"Flat"},
	})
	defs = append(defs, Definition{
		Name: "ExpreduceFlOrFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes: []string{"Flat", "Orderless"},
	})
	defs = append(defs, Definition{
		Name: "ExpreduceFlOiFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes: []string{"Flat", "OneIdentity"},
	})
	defs = append(defs, Definition{
		Name: "ExpreduceFlOrOiFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes: []string{"Flat", "Orderless", "OneIdentity"},
	})
	return
}
