package expreduce

import "math/big"
import "time"
import "fmt"
import "os"
import "runtime/pprof"
import "log"
import "io/ioutil"
import "github.com/op/go-logging"
import "flag"

var mymemprofile = flag.String("mymemprofile", "", "write memory profile to this file")

func hashEx(e Ex) uint64 {
	return e.Hash()
}

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
	_, isSym := e.(*Symbol)
	if isSym {
		toReturn, defined, _ := es.GetDef(
			"System`N",
			NewExpression([]Ex{&Symbol{"System`N"}, e}),
		)
		if defined {
			return toReturn
		}
	}
	asExpr, isExpr := e.(*Expression)
	if isExpr {
		toReturn, defined, _ := es.GetDef(
			"System`N",
			NewExpression([]Ex{&Symbol{"System`N"}, e}),
		)
		if defined {
			return toReturn
		}
		exToReturn := NewEmptyExpression()
		for _, part := range asExpr.Parts {
			toAdd, defined, _ := es.GetDef(
				"System`N",
				NewExpression([]Ex{&Symbol{"System`N"}, part}),
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

func TryReadFile(fn Ex, es *EvalState) (string, string, bool) {
	pathSym := &Symbol{"System`$Path"}
	path, isDef, _ := es.GetDef("System`$Path", pathSym)
	if !isDef {
		return "", "", false
	}
	pathL, pathIsList := HeadAssertion(path, "System`List")
	if !pathIsList {
		return "", "", false
	}
	filenameString, fnIsStr := fn.(*String)
	if !fnIsStr {
		return "", "", false
	}
	rawFn := filenameString.Val
	pathsToTry := []string{}
	for _, pathEx := range pathL.Parts[1:] {
		pathString, pathIsString := pathEx.(*String)
		if !pathIsString {
			fmt.Printf("Invalid path: %v\n", pathEx)
			continue
		}
		rawDir := pathString.Val
		rawPath := rawDir + string(os.PathSeparator) + rawFn
		pathsToTry = append(pathsToTry, rawPath)
	}
	pathsToTry = append(pathsToTry, rawFn)
	for _, rawPath := range pathsToTry {
		dat, err := ioutil.ReadFile(rawPath)
		if err != nil {
			continue
		}
		fileData := string(dat)
		return fileData, rawPath, true
	}
	return "", "", false
}

func snagUnique(prefix string, es *EvalState) (string, bool) {
	mnExpr, mnIsDef := es.GetSymDef("System`$ModuleNumber")
	if !mnIsDef {
		return "", false
	}
	mnInteger, mnIsInt := mnExpr.(*Integer)
	if !mnIsInt {
		return "", false
	}
	mn := mnInteger.Val.Int64()

	// Find the next ModuleNumber to use.
	for {
		toTry := fmt.Sprintf("%v$%v", prefix, mn)
		if !es.IsDef(toTry) {
			es.Define(&Symbol{"System`$ModuleNumber"}, &Integer{big.NewInt(mn + 1)})
			return toTry, true
		}
		mn += 1
	}
	return "", false
}


func applyModuleFn(this *Expression, es *EvalState) (Ex, bool) {
	// Coarse parsing of arguments.
	if len(this.Parts) != 3 {
		return nil, false
	}
	locals, localsIsList := HeadAssertion(this.Parts[1], "System`List")
	if !localsIsList {
		return nil, false
	}

	// Parse locals into a struct
	type parsedLocal struct {
		sym          *Symbol
		uniqueName   string
		setValue     Ex
		isSet        bool
		isSetDelayed bool
	}
	var parsedLocals []parsedLocal
	for _, localEx := range locals.Parts[1:] {
		pl := parsedLocal{}
		symEx := localEx
		localSet, localIsSet := HeadAssertion(localEx, "System`Set")
		pl.isSet = localIsSet
		localSetDelayed, localIsSetDelayed := HeadAssertion(localEx, "System`SetDelayed")
		pl.isSetDelayed = localIsSetDelayed
		if localIsSet && len(localSet.Parts) == 3 {
			symEx = localSet.Parts[1]
			pl.setValue = localSet.Parts[2]
		}
		if localIsSetDelayed && len(localSetDelayed.Parts) == 3 {
			symEx = localSetDelayed.Parts[1]
			pl.setValue = localSetDelayed.Parts[2]
		}
		localSym, localIsSym := symEx.(*Symbol)
		pl.sym = localSym
		if !localIsSym {
			return nil, false
		}
		parsedLocals = append(parsedLocals, pl)
	}

	for i := range parsedLocals {
		unique, ok := snagUnique(parsedLocals[i].sym.Name, es)
		if !ok {
			log.Fatal("Error snagging unique.")
		}
		parsedLocals[i].uniqueName = unique
	}
	toReturn := this.Parts[2]
	pm := EmptyPD()
	for _, pl := range parsedLocals {
		if pl.isSet || pl.isSetDelayed {
			rhs := pl.setValue
			if pl.isSet {
				rhs = rhs.Eval(es)
			}
			es.defined[pl.uniqueName] = Def{
				downvalues: []DownValue{
					DownValue{
						rule: *NewExpression([]Ex{
							&Symbol{"System`Rule"},
							&Symbol{pl.uniqueName},
							rhs,
						}),
					},
				},
			}
		} else {
			es.defined[pl.uniqueName] = Def{}
		}
		pm.LazyMakeMap()
		pm.patternDefined[pl.sym.Name] = &Symbol{pl.uniqueName}
	}
	toReturn = ReplacePD(toReturn, es, pm)
	return toReturn, true
}

func GetSystemDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:              "ExpreduceSetLogging",
		Details:           "Logging output prints to the console. There can be a lot of logging output, especially for more complicated pattern matches. Valid levels are `Debug`, `Info`, `Notice`, `Warning`, `Error`, and `Critical`.",
		ExpreduceSpecific: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			sym, ok := this.Parts[1].(*Symbol)
			if ok {
				if sym.Name == "System`True" {
					errorStr := "Invalid level. Must be one of {Debug, Info, Notice}."
					levelSym, lsOk := this.Parts[2].(*Symbol)
					if !lsOk {
						return NewExpression([]Ex{&Symbol{"System`Error"}, &String{errorStr}})
					}
					if levelSym.Name == "System`Debug" {
						es.DebugOn(logging.DEBUG)
					} else if levelSym.Name == "System`Info" {
						es.DebugOn(logging.INFO)
					} else if levelSym.Name == "System`Notice" {
						es.DebugOn(logging.NOTICE)
					} else {
						return NewExpression([]Ex{&Symbol{"System`Error"}, &String{errorStr}})
					}
					return &Symbol{"System`Null"}
				} else if sym.Name == "System`False" {
					es.DebugOff()
					return &Symbol{"System`Null"}
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceDefinitionTimes",
		Details:           "For timing information to record, debug mode must be enabled through `ExpreduceSetLogging`.",
		ExpreduceSpecific: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if *mymemprofile != "" {
				f, err := os.Create(*mymemprofile)
				if err != nil {
					log.Fatal(err)
				}
				pprof.WriteHeapProfile(f)
				f.Close()
			}
			fmt.Println(es.timeCounter.String())
			return &Symbol{"System`Null"}
		},
	})
	defs = append(defs, Definition{
		Name: "Attributes",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			sym, isSym := this.Parts[1].(*Symbol)
			if !isSym {
				return this
			}

			toReturn := NewExpression([]Ex{&Symbol{"System`List"}})
			def, isDef := es.defined[sym.Name]
			if isDef {
				for _, s := range def.attributes.toStrings() {
					toReturn.Parts = append(toReturn.Parts, &Symbol{"System`" + s})
				}
			}
			return toReturn
		},
	})
	defs = append(defs, Definition{
		Name: "Default",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			sym, isSym := this.Parts[1].(*Symbol)
			if !isSym {
				return this
			}

			def := sym.Default(&es.defined)
			if def != nil {
				return def
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Clear",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			for _, arg := range this.Parts[1:] {
				es.Debugf("arg: %v", arg)
				sym, isSym := arg.(*Symbol)
				if isSym {
					es.Clear(sym.Name)
				}
			}
			return &Symbol{"System`Null"}
		},
	})
	defs = append(defs, Definition{
		Name:              "Definition",
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
				return &Symbol{"System`Null"}
			}
			context, contextPath := DefinitionComplexityStringFormArgs()
			return NewExpression([]Ex{&Symbol{"System`Error"}, &String{def.StringForm("InputForm", context, contextPath)}})
		},
	})
	defs = append(defs, Definition{
		Name:              "DownValues",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			sym, ok := this.Parts[1].(*Symbol)
			if !ok {
				return this
			}
			res := NewExpression([]Ex{&Symbol{"System`List"}})
			def, isd := es.defined[sym.Name]
			if !isd {
				return res
			}
			for _, dv := range def.downvalues {
				res.Parts = append(res.Parts, NewExpression([]Ex{
					&Symbol{"System`RuleDelayed"},
					NewExpression([]Ex{
						&Symbol{"System`HoldPattern"},
						dv.rule.Parts[1],
					}),
					dv.rule.Parts[2],
				}))
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name:       "Set",
		Usage:      "`lhs = rhs` sets `lhs` to stand for `rhs`.",
		Attributes: []string{"HoldFirst", "SequenceHold"},
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " = ", true, "(", ")", form, context, contextPath)
		},
		Bootstrap: true,
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
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"`Set` has the `HoldFirst` attribute, meaning `rhs` is evaluated before assignment:"},
			&SameTest{"{HoldFirst, Protected, SequenceHold}", "Attributes[Set]"},
			&TestComment{"`SetDelayed` has the `HoldAll` attribute, meaning `rhs` is not evaluated during assignment:"},
			&SameTest{"{HoldAll, Protected, SequenceHold}", "Attributes[SetDelayed]"},
		},
		KnownFailures: []TestInstruction{
			// Set up for the known failure:
			&SameTest{"a^2", "y=a*a"},
			&SameTest{"a^4", "y=y*y"},
			&SameTest{"2", "a=2"},
			// Known failure until we fix the re-evaluation issue.
			&SameTest{"16", "y"},
			&SameTest{"Null", "Clear[a]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "SetDelayed",
		Usage:      "`lhs := rhs` sets `lhs` to stand for `rhs`, with `rhs` not being evaluated until it is referenced by `lhs`.",
		Attributes: []string{"HoldAll", "SequenceHold"},
		toString: func(this *Expression, form string, context *String, contextPath *Expression) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			return ToStringInfixAdvanced(this.Parts[1:], " := ", true, "(", ")", form, context, contextPath)
		},
		Bootstrap: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			lhs, lhsIsExpr := this.Parts[1].(*Expression)
			if lhsIsExpr {
				for i := range lhs.Parts {
					lhs.Parts[i] = lhs.Parts[i].Eval(es)
				}
				es.Define(lhs, this.Parts[2])
			}
			es.Define(this.Parts[1], this.Parts[2])
			return &Symbol{"System`Null"}
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
		Name: "Timing",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			start := time.Now()
			res := this.Parts[1].Eval(es)
			elapsed := time.Since(start).Seconds()
			return NewExpression([]Ex{&Symbol{"System`List"}, &Flt{big.NewFloat(elapsed)}, res})
		},
	})
	defs = append(defs, Definition{
		Name:      "Print",
		Usage:     "`Print[expr1, expr2, ...]` prints the string representation of the expressions to the console and returns `Null`.",
		Bootstrap: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) < 2 {
				return this
			}

			for i := 1; i < len(this.Parts); i++ {
				fmt.Printf("%s", this.Parts[i].String())
			}
			fmt.Printf("\n")
			return &Symbol{"System`Null"}
		},
	})
	defs = append(defs, Definition{
		Name: "MessageName",
	})
	defs = append(defs, Definition{
		Name: "Trace",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			// TODO: this will prevent nested Trace calls. Figure out a better
			// way.

			// Put system in trace mode:
			es.trace = NewExpression([]Ex{&Symbol{"System`List"}})
			// Evaluate first argument in trace mode:
			this.Parts[1].Eval(es)
			if len(es.trace.Parts) > 2 {
				// Take system out of trace mode:
				toReturn := es.trace.DeepCopy()
				es.trace = nil
				return toReturn
			}
			es.trace = nil
			return NewExpression([]Ex{&Symbol{"System`List"}})
		},
	})
	defs = append(defs, Definition{
		Name: "N",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			return exprToN(es, this.Parts[1])
		},
	})
	defs = append(defs, Definition{
		Name: "Listable",
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlatFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes:        []string{"Flat"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceOrderlessFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes:        []string{"Orderless"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceOneIdentityFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes:        []string{"OneIdentity"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlatFn2",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes:        []string{"Flat"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlOrFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes:        []string{"Flat", "Orderless"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlOiFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes:        []string{"Flat", "OneIdentity"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlOrOiFn",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes:        []string{"Flat", "Orderless", "OneIdentity"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceLikePlus",
		Default:           "0",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Attributes:        []string{"Flat", "Listable", "NumericFunction", "OneIdentity", "Orderless"},
	})
	defs = append(defs, Definition{
		Name: "Get",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			fileData, rawPath, ok := TryReadFile(this.Parts[1], es)
			if !ok {
				return &Symbol{"System`$Failed"}
			}
			return EvalInterpMany(fileData, rawPath, es)
		},
	})
	defs = append(defs, Definition{
		Name: "Module",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			res, ok := applyModuleFn(this, es)
			if !ok {
				return this
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name:              "ESameTest",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		Bootstrap:         true,
		Attributes:        []string{"HoldAll", "SequenceHold"},
	})
	defs = append(defs, Definition{
		Name: "Hash",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			i := big.NewInt(0)
			i.SetUint64(hashEx(this.Parts[1]))
			return &Integer{i}
		},
	})
	defs = append(defs, Definition{
		Name: "ReadList",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			fileData, rawPath, ok := TryReadFile(this.Parts[1], es)
			if !ok {
				return &Symbol{"System`$Failed"}
			}
			return ReadList(fileData, rawPath, es)
		},
	})
	defs = append(defs, Definition{Name: "BeginPackage"})
	defs = append(defs, Definition{Name: "EndPackage"})
	defs = append(defs, Definition{Name: "Begin"})
	defs = append(defs, Definition{Name: "End"})
	defs = append(defs, Definition{Name: "PrintTemporary"})
	defs = append(defs, Definition{Name: "SetAttributes"})
	defs = append(defs, Definition{Name: "ClearAttributes"})
	defs = append(defs, Definition{Name: "Protect"})
	defs = append(defs, Definition{Name: "Unprotect"})
	defs = append(defs, Definition{Name: "ClearAll"})
	defs = append(defs, Definition{
		Name: "Quiet",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name: "TimeConstrained",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name: "Throw",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			es.Throw(this)
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Catch",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			res := this.Parts[1].Eval(es)
			if es.HasThrown() {
				toReturn := es.thrown.Parts[1]
				es.Throw(nil)
				return toReturn
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceMaskNonConditional",
		OmitDocumentation: true,
		ExpreduceSpecific: true,
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}
			return NewExpression([]Ex{
				&Symbol{"System`Hold"},
				maskNonConditional(this.Parts[1]),
			})
		},
	})
	defs = append(defs, Definition{
		Name: "Unique",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 1 {
				return this
			}
			unique, ok := snagUnique("Global`", es)
			if !ok {
				log.Fatal("Error snagging unique.")
			}
			return &Symbol{unique}
		},
	})
	return
}
