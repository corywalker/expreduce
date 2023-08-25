package expreduce

import (
	"bytes"
	"compress/zlib"
	"encoding/gob"
	"flag"
	"fmt"
	"log"
	"math/big"
	"os"
	"regexp"
	"runtime/pprof"
	"sort"
	"strings"
	"time"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/matcher"
	"github.com/corywalker/expreduce/expreduce/rubi_snapshot"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/op/go-logging"
)

var mymemprofile = flag.String(
	"mymemprofile",
	"",
	"write memory profile to this file",
)

var exprFileHeader = []byte{26, 166, 245, 29, 69, 251, 144, 0}

type encodedDef struct {
	Name string
	Def  expreduceapi.Def
}

func hashEx(e expreduceapi.Ex) uint64 {
	return e.Hash()
}

func exprToN(
	es expreduceapi.EvalStateInterface,
	e expreduceapi.Ex,
) expreduceapi.Ex {
	asInt, isInt := e.(*atoms.Integer)
	if isInt {
		toReturn, _ := atoms.IntegerToFlt(asInt)
		return toReturn
	}
	asRat, isRat := e.(*atoms.Rational)
	if isRat {
		toReturn, _ := atoms.RationalToFlt(asRat)
		return toReturn
	}
	_, isSym := e.(*atoms.Symbol)
	if isSym {
		toReturn, defined, _ := es.GetDef(
			"System`N",
			atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`N"), e},
			),
		)
		if defined {
			return toReturn
		}
	}
	asExpr, isExpr := e.(expreduceapi.ExpressionInterface)
	if isExpr {
		toReturn, defined, _ := es.GetDef(
			"System`N",
			atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`N"), e},
			),
		)
		if defined {
			return toReturn
		}
		exToReturn := atoms.NewEmptyExpression()
		for _, part := range asExpr.GetParts() {
			toAdd, defined, _ := es.GetDef(
				"System`N",
				atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`N"), part},
				),
			)
			if !defined {
				toAdd = exprToN(es, part)
			}
			exToReturn.AppendEx(toAdd)
		}
		return exToReturn
	}
	return e.DeepCopy()
}

func tryReadFile(
	fn expreduceapi.Ex,
	es expreduceapi.EvalStateInterface,
) ([]byte, string, bool) {
	pathSym := atoms.NewSymbol("System`$Path")
	path, isDef, _ := es.GetDef("System`$Path", pathSym)
	if !isDef {
		return []byte{}, "", false
	}
	pathL, pathIsList := atoms.HeadAssertion(path, "System`List")
	if !pathIsList {
		return []byte{}, "", false
	}
	filenameString, fnIsStr := fn.(*atoms.String)
	if !fnIsStr {
		return []byte{}, "", false
	}
	rawFn := filenameString.Val

	// Handle resource file reads
	if strings.HasPrefix(rawFn, "__res__/") {
		fileData, err := Asset("resources/" + rawFn[8:])
		if err == nil {
			return fileData, rawFn, true
		}
	}
	if strings.HasPrefix(rawFn, "__rubi_snapshot__/") {
		fileData, err := rubi_snapshot.Asset(rawFn[18:])
		if err == nil {
			return fileData, rawFn, true
		}
	}

	pathsToTry := []string{}
	for _, pathEx := range pathL.GetParts()[1:] {
		pathString, pathIsString := pathEx.(*atoms.String)
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
		dat, err := os.ReadFile(rawPath)
		if err != nil {
			continue
		}
		return dat, rawPath, true
	}
	return []byte{}, "", false
}

func snagUnique(
	context string,
	prefix string,
	es expreduceapi.EvalStateInterface,
) (string, bool) {
	mnExpr, mnIsDef := es.GetSymDef("System`$ModuleNumber")
	if !mnIsDef {
		return "", false
	}
	mnInteger, mnIsInt := mnExpr.(*atoms.Integer)
	if !mnIsInt {
		return "", false
	}
	mn := mnInteger.Val.Int64()

	// Find the next ModuleNumber to use.
	for {
		toTry := fmt.Sprintf("%v%v%v", context, prefix, mn)
		if !es.IsDef(toTry) {
			es.Define(
				atoms.NewSymbol("System`$ModuleNumber"),
				atoms.NewInteger(big.NewInt(mn+1)),
			)
			return toTry, true
		}
		mn++
	}
}

func applyModuleFn(
	this expreduceapi.ExpressionInterface,
	es expreduceapi.EvalStateInterface,
) (expreduceapi.Ex, bool) {
	// Coarse parsing of arguments.
	if len(this.GetParts()) != 3 {
		return nil, false
	}
	locals, localsIsList := atoms.HeadAssertion(
		this.GetParts()[1],
		"System`List",
	)
	if !localsIsList {
		return nil, false
	}

	// Parse locals into a struct
	type parsedLocal struct {
		sym          *atoms.Symbol
		uniqueName   string
		setValue     expreduceapi.Ex
		isSet        bool
		isSetDelayed bool
	}
	var parsedLocals []parsedLocal
	for _, localEx := range locals.GetParts()[1:] {
		pl := parsedLocal{}
		symEx := localEx
		localSet, localIsSet := atoms.HeadAssertion(localEx, "System`Set")
		pl.isSet = localIsSet
		localSetDelayed, localIsSetDelayed := atoms.HeadAssertion(
			localEx,
			"System`SetDelayed",
		)
		pl.isSetDelayed = localIsSetDelayed
		if localIsSet && len(localSet.GetParts()) == 3 {
			symEx = localSet.GetParts()[1]
			pl.setValue = localSet.GetParts()[2]
		}
		if localIsSetDelayed && len(localSetDelayed.GetParts()) == 3 {
			symEx = localSetDelayed.GetParts()[1]
			pl.setValue = localSetDelayed.GetParts()[2]
		}
		localSym, localIsSym := symEx.(*atoms.Symbol)
		pl.sym = localSym
		if !localIsSym {
			return nil, false
		}
		parsedLocals = append(parsedLocals, pl)
	}

	for i := range parsedLocals {
		unique, ok := snagUnique(parsedLocals[i].sym.Name, "$", es)
		if !ok {
			log.Fatal("Error snagging unique.")
		}
		parsedLocals[i].uniqueName = unique
	}
	toReturn := this.GetParts()[2]
	pm := matcher.EmptyPD()
	for _, pl := range parsedLocals {
		if pl.isSet || pl.isSetDelayed {
			rhs := pl.setValue
			if pl.isSet {
				rhs = es.Eval(rhs)
			}
			es.GetDefinedMap().Set(pl.uniqueName, expreduceapi.Def{
				Downvalues: []expreduceapi.DownValue{
					expreduceapi.DownValue{
						Rule: atoms.NewExpression([]expreduceapi.Ex{
							atoms.NewSymbol("System`Rule"),
							atoms.E(
								atoms.S("HoldPattern"),
								atoms.NewSymbol(pl.uniqueName),
							),
							rhs,
						}),
					},
				},
			})
		} else {
			es.GetDefinedMap().Set(pl.uniqueName, expreduceapi.Def{})
		}
		pm.Define(pl.sym.Name, atoms.NewSymbol(pl.uniqueName))
	}
	toReturn = matcher.ReplacePD(toReturn, es, pm)
	return toReturn, true
}

func parseOutputStream(outputStreamDef expreduceapi.Ex) (string, int64, bool) {
	// Handle string-only stream names like "stdout".
	streamName, ok := outputStreamDef.(*atoms.String)
	if ok {
		// Use -1 as a placeholder for a missing index.
		return streamName.GetValue(), -1, true
	}

	outputStream, isOutputStream := atoms.HeadAssertion(
		outputStreamDef,
		"System`OutputStream",
	)
	if !isOutputStream {
		return "", -1, false
	}
	if outputStream.Len() != 2 {
		return "", -1, false
	}
	streamName, ok = outputStream.GetPart(1).(*atoms.String)
	if !ok {
		return "", -1, false
	}
	streamIndex, ok := outputStream.GetPart(2).(*atoms.Integer)
	if !ok {
		return "", -1, false
	}
	return streamName.GetValue(), streamIndex.Val.Int64(), true
}

func getSystemDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:              "ExpreduceSetLogging",
		Details:           "Logging output prints to the console. There can be a lot of logging output, especially for more complicated pattern matches. Valid levels are `Debug`, `Info`, `Notice`, `Warning`, `Error`, and `Critical`.",
		expreduceSpecific: true,
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			sym, ok := this.GetParts()[1].(*atoms.Symbol)
			if ok {
				if sym.Name == "System`True" {
					errorStr := "Invalid level. Must be one of {Debug, Info, Notice}."
					levelSym, lsOk := this.GetParts()[2].(*atoms.Symbol)
					if !lsOk {
						return atoms.NewExpression(
							[]expreduceapi.Ex{
								atoms.NewSymbol("System`Error"),
								atoms.NewString(errorStr),
							},
						)
					}
					if levelSym.Name == "System`Debug" {
						es.DebugOn(logging.DEBUG)
					} else if levelSym.Name == "System`Info" {
						es.DebugOn(logging.INFO)
					} else if levelSym.Name == "System`Notice" {
						es.DebugOn(logging.NOTICE)
					} else {
						return atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`Error"), atoms.NewString(errorStr)})
					}
					return atoms.NewSymbol("System`Null")
				} else if sym.Name == "System`False" {
					es.DebugOff()
					return atoms.NewSymbol("System`Null")
				}
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceDefinitionTimes",
		Details:           "For timing information to record, debug mode must be enabled through `ExpreduceSetLogging`.",
		expreduceSpecific: true,
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if *mymemprofile != "" {
				f, err := os.Create(*mymemprofile)
				if err != nil {
					log.Fatal(err)
				}
				err = pprof.WriteHeapProfile(f)
				if err != nil {
					log.Fatal(err)
				}
				f.Close()
			}
			fmt.Println(es.GetTimeCounter().String())
			return atoms.NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Attributes",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			sym, isSym := this.GetParts()[1].(*atoms.Symbol)
			if !isSym {
				return this
			}

			def, isDef := es.GetDefinedMap().Get(sym.Name)
			if isDef {
				return atoms.AttrsToSymList(&def.Attributes)
			}
			return atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
			)
		},
	})
	defs = append(defs, Definition{
		Name: "Default",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			sym, isSym := this.GetParts()[1].(*atoms.Symbol)
			if !isSym {
				return this
			}

			def := sym.Default(es.GetDefinedMap())
			if def != nil {
				return def
			}
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Clear",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			for _, arg := range this.GetParts()[1:] {
				es.Debugf("arg: %v", arg)
				sym, isSym := arg.(*atoms.Symbol)
				if isSym {
					es.Clear(sym.Name)
				}
			}
			return atoms.NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Definition",
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 2 {
				return false, ""
			}
			if params.Form != "InputForm" && params.Form != "OutputForm" {
				return false, ""
			}

			sym, ok := this.GetParts()[1].(*atoms.Symbol)
			if !ok {
				return false, ""
			}
			if params.Esi == nil {
				return true, "Definiton[<WITHOUT_CONTEXT>]"
			}
			def, isd := params.Esi.GetDefined(sym.Name)
			if !isd {
				return true, "Null"
			}
			stringParams := params
			stringParams.Context, stringParams.ContextPath =
				definitionComplexityStringFormArgs()
			stringParams.PreviousHead = "<TOPLEVEL>"
			// To prevent things like "Definition[In]" from exploding:
			stringParams.Esi = nil
			return true, stringForm(&def, sym, stringParams)
		},
	})
	defs = append(defs, Definition{
		Name: "DownValues",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			sym, ok := this.GetParts()[1].(*atoms.Symbol)
			if !ok {
				return this
			}
			res := atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
			)
			def, isd := es.GetDefinedMap().Get(sym.Name)
			if !isd {
				return res
			}
			for _, dv := range def.Downvalues {
				_, isLHSExpr := dv.Rule.GetParts()[1].(expreduceapi.ExpressionInterface).GetParts()[1].(expreduceapi.ExpressionInterface)
				if !isLHSExpr {
					continue
				}
				res.AppendEx(atoms.NewExpression([]expreduceapi.Ex{
					atoms.NewSymbol("System`RuleDelayed"),
					dv.Rule.GetParts()[1],
					dv.Rule.GetParts()[2],
				}))
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name:       "Set",
		Usage:      "`lhs = rhs` sets `lhs` to stand for `rhs`.",
		Attributes: []string{"HoldFirst", "SequenceHold"},
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 3 {
				return false, ""
			}
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" = ",
				"System`Set",
				false,
				"",
				"",
				params,
			)
		},
		Bootstrap: true,
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			es.Define(this.GetParts()[1], this.GetParts()[2])
			return this.GetParts()[2]
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
			&TestComment{
				"`Set` has the `HoldFirst` attribute, meaning `rhs` is evaluated before assignment:",
			},
			&SameTest{
				"{HoldFirst, Protected, SequenceHold}",
				"Attributes[Set]",
			},
			&TestComment{
				"`SetDelayed` has the `HoldAll` attribute, meaning `rhs` is not evaluated during assignment:",
			},
			&SameTest{
				"{HoldAll, Protected, SequenceHold}",
				"Attributes[SetDelayed]",
			},
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
		toString: func(this expreduceapi.ExpressionInterface, params expreduceapi.ToStringParams) (bool, string) {
			if len(this.GetParts()) != 3 {
				return false, ""
			}
			return toStringInfixAdvanced(
				this.GetParts()[1:],
				" := ",
				"System`SetDelayed",
				false,
				"",
				"",
				params,
			)
		},
		Bootstrap: true,
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 3 {
				return this
			}

			lhs, lhsIsExpr := this.GetParts()[1].(expreduceapi.ExpressionInterface)
			if lhsIsExpr {
				headSym, headIsSym := &atoms.Symbol{}, false
				if len(lhs.GetParts()) > 0 {
					headSym, headIsSym = lhs.GetParts()[0].(*atoms.Symbol)
				}
				attrs := expreduceapi.Attributes{}
				if headIsSym {
					attrs = headSym.Attrs(es.GetDefinedMap())
				}

				if !(attrs.HoldAll || attrs.HoldAllComplete) {
					for i := range lhs.GetParts() {
						lhs.GetParts()[i] = es.Eval(lhs.GetParts()[i])
					}
				}
				es.Define(lhs, this.GetParts()[2])
			}
			es.Define(this.GetParts()[1], this.GetParts()[2])
			return atoms.NewSymbol("System`Null")
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"`SetDelayed` can be used to define functions:"},
			&SameTest{"Null", "testa[x_] := x*2"},
			&SameTest{"Null", "testa[x_Integer] := x*3"},
			&SameTest{"Null", "testa[x_Real] := x*4"},
			&TestComment{"The more \"specific\" definitions match first:"},
			&SameTest{"8.", "testa[2.]"},
			&SameTest{"6", "testa[2]"},
			&TestComment{
				"There is no specific match for `testa[k]`, so the general case matches:",
			},
			&SameTest{"2 * k", "testa[k]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{
				"`Set` has the `HoldFirst` attribute, meaning `rhs` is evaluated before assignment:",
			},
			&SameTest{
				"{HoldFirst, Protected, SequenceHold}",
				"Attributes[Set]",
			},
			&TestComment{
				"`SetDelayed` has the `HoldAll` attribute, meaning `rhs` is not evaluated during assignment:",
			},
			&SameTest{
				"{HoldAll, Protected, SequenceHold}",
				"Attributes[SetDelayed]",
			},
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

			// Test with HoldAll. We should not evaluate the arguments even
			// when setting.
			&SameTest{
				"Attributes[holdTest]= {HoldAll};holdTest[1+1]:=\"pass\";holdTest[1+1]",
				"\"pass\"",
			},
		},
	})
	defs = append(defs, Definition{
		Name: "Timing",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			start := time.Now()
			res := es.Eval(this.GetParts()[1])
			elapsed := time.Since(start).Seconds()
			return atoms.NewExpression(
				[]expreduceapi.Ex{
					atoms.NewSymbol("System`List"),
					atoms.NewReal(big.NewFloat(elapsed)),
					res,
				},
			)
		},
	})
	defs = append(defs, Definition{
		Name:      "Print",
		Bootstrap: true,
	})
	defs = append(defs, Definition{
		Name: "MessageName",
	})
	defs = append(defs, Definition{
		Name: "Trace",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}

			// TODO: this will prevent nested Trace calls. Figure out a better
			// way.

			// Put system in trace mode:
			es.SetTrace(
				atoms.NewExpression(
					[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
				),
			)
			// Evaluate first argument in trace mode:
			es.Eval(this.GetParts()[1])
			if es.GetTrace() != nil && len(es.GetTrace().GetParts()) > 2 {
				// Take system out of trace mode:
				toReturn := es.GetTrace().DeepCopy()
				es.SetTrace(nil)
				return toReturn
			}
			es.SetTrace(nil)
			return atoms.NewExpression(
				[]expreduceapi.Ex{atoms.NewSymbol("System`List")},
			)
		},
	})
	defs = append(defs, Definition{
		Name: "N",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			return exprToN(es, this.GetParts()[1])
		},
	})
	defs = append(defs, Definition{
		Name: "Listable",
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlatFn",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Attributes:        []string{"Flat"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceOrderlessFn",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Attributes:        []string{"Orderless"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceOneIdentityFn",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Attributes:        []string{"OneIdentity"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlatFn2",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Attributes:        []string{"Flat"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlOrFn",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Attributes:        []string{"Flat", "Orderless"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlOiFn",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Attributes:        []string{"Flat", "OneIdentity"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceFlOrOiFn",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Attributes:        []string{"Flat", "Orderless", "OneIdentity"},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceLikePlus",
		Default:           "0",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Attributes: []string{
			"Flat",
			"Listable",
			"NumericFunction",
			"OneIdentity",
			"Orderless",
		},
	})
	defs = append(defs, Definition{
		Name: "Get",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			fileData, rawPath, ok := tryReadFile(this.GetParts()[1], es)
			if !ok {
				return atoms.NewSymbol("System`$Failed")
			}
			if len(fileData) >= len(exprFileHeader) &&
				bytes.Equal(fileData[:len(exprFileHeader)], exprFileHeader) {

				// TODO: Read as a stream and not a byte string.
				r := bytes.NewReader(fileData[len(exprFileHeader):])
				atoms.RegisterGobAtoms()
				compressedReader, _ := zlib.NewReader(r)
				decoder := gob.NewDecoder(compressedReader)
				definitions := []encodedDef{}
				if err := decoder.Decode(&definitions); err != nil {
					panic(err)
				}
				compressedReader.Close()

				for _, def := range definitions {
					es.SetDefined(def.Name, def.Def)
				}

				return atoms.NewSymbol("System`Null")
			}
			return EvalInterpMany(string(fileData), rawPath, es)
		},
	})
	defs = append(defs, Definition{
		Name: "Save",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if this.Len() != 2 {
				return this
			}

			filenameStr, ok := this.GetPart(1).(*atoms.String)
			if !ok {
				return this
			}
			filename := filenameStr.GetValue()

			definitions := []encodedDef{}
			symList, ok := atoms.HeadAssertion(this.GetPart(2), "System`List")
			if !ok {
				return this
			}
			for _, symEx := range symList.GetParts()[1:] {
				symStr, symIsStr := symEx.(*atoms.String)
				if !symIsStr {
					return this
				}
				symName := symStr.GetValue()
				def, ok := es.GetDefined(symName)
				if !ok {
					return this
				}
				definitions = append(definitions, encodedDef{
					Name: symName,
					Def:  def,
				})
			}
			if len(definitions) == 0 {
				return this
			}

			atoms.RegisterGobAtoms()

			file, err := os.Create(filename)
			if err == nil {
				// Write the header.
				if _, err := file.Write(exprFileHeader); err != nil {
					panic(err)
				}
				compressedWriter := zlib.NewWriter(file)
				encoder := gob.NewEncoder(compressedWriter)
				if err := encoder.Encode(definitions); err != nil {
					panic(err)
				}
				compressedWriter.Close()
			}
			file.Close()

			return atoms.NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Module",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			res, ok := applyModuleFn(this, es)
			if !ok {
				return this
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name:              "Block",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name:              "ESameTest",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Bootstrap:         true,
		Attributes:        []string{"HoldAll", "SequenceHold"},
	})
	defs = append(defs, Definition{
		Name:              "ENearlySameTest",
		OmitDocumentation: true,
		expreduceSpecific: true,
		Bootstrap:         true,
		Attributes:        []string{"HoldAll", "SequenceHold"},
	})
	defs = append(defs, Definition{
		Name: "Hash",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			i := big.NewInt(0)
			i.SetUint64(hashEx(this.GetParts()[1]))
			return atoms.NewInteger(i)
		},
	})
	defs = append(defs, Definition{
		Name: "ReadList",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			fileData, rawPath, ok := tryReadFile(this.GetParts()[1], es)
			if !ok {
				return atoms.NewSymbol("System`$Failed")
			}
			return ReadList(string(fileData), rawPath, es)
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
		Name:              "Quiet",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name:              "TimeConstrained",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{
		Name: "Throw",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			es.Throw(this)
			return this
		},
	})
	defs = append(defs, Definition{
		Name: "Catch",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			res := es.Eval(this.GetParts()[1])
			if es.HasThrown() {
				toReturn := es.Thrown().GetParts()[1]
				es.Throw(nil)
				return toReturn
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name:              "ExpreduceMaskNonConditional",
		OmitDocumentation: true,
		expreduceSpecific: true,
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				return this
			}
			return atoms.NewExpression([]expreduceapi.Ex{
				atoms.NewSymbol("System`Hold"),
				maskNonConditional(this.GetParts()[1]),
			})

		},
	})
	defs = append(defs, Definition{
		Name: "Unique",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) > 3 {
				return this
			}
			prefix := "$"
			if len(this.GetParts()) == 2 {
				asStr, isStr := this.GetParts()[1].(*atoms.String)
				if !isStr {
					return this
				}
				prefix = asStr.Val
			}
			unique, ok := snagUnique("Global`", prefix, es)
			if !ok {
				log.Fatal("Error snagging unique.")
			}
			return atoms.NewSymbol(unique)
		},
	})
	defs = append(defs, Definition{
		Name: "Sow",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				fmt.Println("Unsupported call to Sow.")
				return this
			}
			res := es.Eval(this.GetParts()[1])
			if es.GetReapSown() != nil {
				es.GetReapSown().AppendEx(res)
			}
			return res
		},
	})
	defs = append(defs, Definition{
		Name: "Reap",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if len(this.GetParts()) != 2 {
				fmt.Println("Unsupported call to Reap.")
				return this
			}
			es.SetReapSown(atoms.E(atoms.S("List")))
			res := es.Eval(this.GetParts()[1])
			res = atoms.E(
				atoms.S("List"),
				res,
				atoms.E(atoms.S("List"), es.GetReapSown()),
			)
			// If I set this to nil, Int[((A + B*Cos[x])*(a + b*Sin[x])^-1), x]
			// will not work for an unknown reason.
			es.SetReapSown(atoms.E(atoms.S("List")))
			return res
		},
	})
	defs = append(defs, Definition{
		Name:              "Defer",
		OmitDocumentation: true,
	})
	defs = append(defs, Definition{Name: "Information"})
	defs = append(defs, Definition{Name: "OutputStream"})
	defs = append(defs, Definition{
		Name: "WriteString",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if this.Len() != 2 {
				fmt.Println("Unsupported call to WriteString.")
				return this
			}
			streamName, streamIndex, ok := parseOutputStream(this.GetPart(1))
			if !ok {
				fmt.Println("Failed to parse OutputStream.")
				return this
			}
			str, ok := this.GetPart(2).(*atoms.String)
			if !ok {
				fmt.Println(
					"Failed to convert the second argument of WriteString to a string.",
				)
				return this
			}
			es.GetStreamManager().
				WriteString(streamName, streamIndex, str.GetValue())
			return atoms.NewSymbol("System`Null")
		},
	})
	defs = append(defs, Definition{
		Name: "Streams",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			if this.Len() != 0 {
				fmt.Println("Unsupported call to Streams.")
				return this
			}
			return es.GetStreamManager().AsExpr()
		},
	})
	defs = append(defs, Definition{
		Name: "Names",
		legacyEvalFn: func(this expreduceapi.ExpressionInterface, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
			regex := ""
			if this.Len() == 0 {
				regex = ".*"
			}
			if this.Len() == 1 {
				filter, filterIsString := this.GetPart(1).(*atoms.String)
				if filterIsString {
					replacedVal := strings.Replace(
						filter.GetValue(),
						"*",
						".*",
						-1,
					)
					regex = "^" + replacedVal + "$"
				}
			}
			if regex == "" {
				fmt.Println("Unsupported call to Names.")
				return this
			}
			var namesRegex = regexp.MustCompile(regex)
			names := []string{}
			for _, name := range es.GetDefinedMap().Keys() {
				if namesRegex.MatchString(name) {
					names = append(names, name)
				}
			}
			sort.Strings(names)
			return atoms.NewStringList(names)
		},
	})
	return
}
