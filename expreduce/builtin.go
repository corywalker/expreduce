package expreduce

import (
	"fmt"
	"log"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

type Definition struct {
	// The symbol name, like "Mean", and "Total"
	Name  string
	Usage string
	// Currently used for SetDelayed, since other definitions depend on
	// SetDelayed, we define it first.
	Bootstrap         bool
	OmitDocumentation bool
	ExpreduceSpecific bool
	Details           string

	// Map symbol to Eval() function
	legacyEvalFn    (func(expreduceapi.ExpressionInterface, expreduceapi.EvalStateInterface) expreduceapi.Ex)
	SimpleExamples  []TestInstruction
	FurtherExamples []TestInstruction
	Tests           []TestInstruction
	KnownFailures   []TestInstruction
	KnownDangerous  []TestInstruction

	toString expreduceapi.ToStringFnType

	Attributes []string
	Default    string
}

func ToTestInstructions(tc expreduceapi.ExpressionInterface) []TestInstruction {
	instructions := []TestInstruction{}
	for _, tiEx := range tc.GetParts()[1:] {
		if st, isSt := atoms.HeadAssertion(tiEx, "System`ESameTest"); isSt {
			if len(st.GetParts()) != 3 {
				log.Fatalf("Invalid test case: %v\n", tiEx)
				continue
			}
			instructions = append(instructions, &SameTestEx{
				st.GetParts()[1], st.GetParts()[2]})
			continue
		}
		if st, isSt := atoms.HeadAssertion(tiEx, "System`EStringTest"); isSt {
			if len(st.GetParts()) != 3 {
				log.Fatalf("Invalid test case: %v\n", tiEx)
				continue
			}
			instructions = append(instructions, &StringTest{
				st.GetParts()[1].(*atoms.String).Val, st.GetParts()[2].(*atoms.String).Val})
			continue
		}
		if st, isSt := atoms.HeadAssertion(tiEx, "System`EExampleOnlyInstruction"); isSt {
			if len(st.GetParts()) != 3 {
				log.Fatalf("Invalid test case: %v\n", tiEx)
				continue
			}
			instructions = append(instructions, &ExampleOnlyInstruction{
				st.GetParts()[1].(*atoms.String).Val, st.GetParts()[2].(*atoms.String).Val})
			continue
		}
		if st, isSt := atoms.HeadAssertion(tiEx, "System`EComment"); isSt {
			if len(st.GetParts()) != 2 {
				log.Fatalf("Invalid test case: %v\n", tiEx)
				continue
			}
			comStr, comIsStr := st.GetParts()[1].(*atoms.String)
			if !comIsStr {
				log.Fatalf("Invalid test case: %v\n", tiEx)
				continue
			}
			instructions = append(instructions, &TestComment{
				comStr.Val})
			continue
		}
		if st, isSt := atoms.HeadAssertion(tiEx, "System`EResetState"); isSt {
			if len(st.GetParts()) != 1 {
				log.Fatalf("Invalid test case: %v\n", tiEx)
				continue
			}
			instructions = append(instructions, &ResetState{})
			continue
		}
		if _, isSt := atoms.HeadAssertion(tiEx, "System`List"); isSt {
			fmt.Printf("Ignoring unfilled test: %v\n", tiEx)
			continue
		}
		log.Fatalf("Invalid test case: %v\n", tiEx)
	}
	return instructions
}

func (def *Definition) AnnotateWithDynamicTests(es expreduceapi.EvalStateInterface) {
	tests, testsDef := es.GetSymDef("Tests`" + def.Name)
	if !testsDef {
		return
	}
	testsList, testsIsList := atoms.HeadAssertion(tests, "System`List")
	if !testsIsList {
		return
	}
	for _, testCol := range testsList.GetParts()[1:] {
		testColExpr, testColIsExpr := testCol.(expreduceapi.ExpressionInterface)
		if !testColIsExpr {
			continue
		}
		headSym, headIsSym := testColExpr.GetParts()[0].(*atoms.Symbol)
		if !headIsSym {
			continue
		}
		if headSym.Name == "System`ESimpleExamples" {
			def.SimpleExamples = append(
				def.SimpleExamples,
				ToTestInstructions(testColExpr)...)
		} else if headSym.Name == "System`EFurtherExamples" {
			def.FurtherExamples = append(
				def.FurtherExamples,
				ToTestInstructions(testColExpr)...)
		} else if headSym.Name == "System`ETests" {
			def.Tests = append(
				def.Tests,
				ToTestInstructions(testColExpr)...)
		} else if headSym.Name == "System`EKnownFailures" {
			def.KnownFailures = append(
				def.KnownFailures,
				ToTestInstructions(testColExpr)...)
		} else if headSym.Name == "System`EKnownDangerous" {
			def.KnownDangerous = append(
				def.KnownDangerous,
				ToTestInstructions(testColExpr)...)
		} else {
			log.Fatalf("Invalid test collection: %v\n", testColExpr)
		}
	}
}

func (def *Definition) AnnotateWithDynamicUsage(es expreduceapi.EvalStateInterface) {
	if len(def.Usage) > 0 {
		return
	}
	lhs := atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`MessageName"),
		atoms.NewSymbol("System`" + def.Name),
		atoms.NewString("usage"),
	})

	usage, usageIsDef, _ := es.GetDef("System`MessageName", lhs)
	if !usageIsDef {
		return
	}
	if usageStr, usageIsStr := usage.(*atoms.String); usageIsStr {
		def.Usage = usageStr.Val
	}
}

func (def *Definition) AnnotateWithDynamic(es expreduceapi.EvalStateInterface) {
	def.AnnotateWithDynamicTests(es)
	def.AnnotateWithDynamicUsage(es)
}

type NamedDefSet struct {
	Name string
	Defs []Definition
}

func GetAllDefinitions() (defs []NamedDefSet) {
	defs = append(defs, NamedDefSet{"combinatorics", getCombinatoricsDefinitions()})
	defs = append(defs, NamedDefSet{"calculus", getCalculusDefinitions()})
	defs = append(defs, NamedDefSet{"comparison", getComparisonDefinitions()})
	defs = append(defs, NamedDefSet{"atoms", getAtomsDefinitions()})
	defs = append(defs, NamedDefSet{"functional", getFunctionalDefinitions()})
	defs = append(defs, NamedDefSet{"expression", GetExpressionDefinitions()})
	defs = append(defs, NamedDefSet{"equationdata", GetEquationDataDefinitions()})
	defs = append(defs, NamedDefSet{"solve", GetSolveDefinitions()})
	defs = append(defs, NamedDefSet{"flowcontrol", GetFlowControlDefinitions()})
	defs = append(defs, NamedDefSet{"list", GetListDefinitions()})
	defs = append(defs, NamedDefSet{"matrix", GetMatrixDefinitions()})
	defs = append(defs, NamedDefSet{"arithmetic", getArithmeticDefinitions()})
	defs = append(defs, NamedDefSet{"specialsyms", getSpecialSymsDefinitions()})
	defs = append(defs, NamedDefSet{"power", GetPowerDefinitions()})
	defs = append(defs, NamedDefSet{"random", GetRandomDefinitions()})
	defs = append(defs, NamedDefSet{"replacement", getReplacementDefinitions()})
	defs = append(defs, NamedDefSet{"sort", GetSortDefinitions()})
	defs = append(defs, NamedDefSet{"system", GetSystemDefinitions()})
	defs = append(defs, NamedDefSet{"trig", GetTrigDefinitions()})
	defs = append(defs, NamedDefSet{"plot", GetPlotDefinitions()})
	defs = append(defs, NamedDefSet{"string", GetStringDefinitions()})
	defs = append(defs, NamedDefSet{"time", GetTimeDefinitions()})
	defs = append(defs, NamedDefSet{"pattern", GetPatternDefinitions()})
	defs = append(defs, NamedDefSet{"boolean", GetBooleanDefinitions()})
	defs = append(defs, NamedDefSet{"simplify", GetSimplifyDefinitions()})
	defs = append(defs, NamedDefSet{"numbertheory", GetNumberTheoryDefinitions()})
	defs = append(defs, NamedDefSet{"stats", GetStatsDefinitions()})
	defs = append(defs, NamedDefSet{"manip", GetManipDefinitions()})
	defs = append(defs, NamedDefSet{"rubi", GetRubiDefinitions()})

	// Check for duplicate definitions
	definedNames := make(map[string]bool)
	for _, defSet := range defs {
		for _, def := range defSet.Defs {
			_, alreadyDefined := definedNames[def.Name]
			if alreadyDefined {
				log.Fatalf("Found duplicate definition: %v\n", def.Name)
			}
			definedNames[def.Name] = true
		}
	}
	return
}
