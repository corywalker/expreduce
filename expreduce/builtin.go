//go:generate go-bindata -pkg expreduce -nocompress -nometadata -o resources.go resources/...

package expreduce

import (
	"fmt"
	"log"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

// The Definition struct provides metadata about a builtin function.
type Definition struct {
	// The symbol name, like "Mean", and "Total"
	Name  string
	Usage string
	// Currently used for SetDelayed, since other definitions depend on
	// SetDelayed, we define it first.
	Bootstrap         bool
	OmitDocumentation bool
	expreduceSpecific bool
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

func toTestInstructions(tc expreduceapi.ExpressionInterface) []TestInstruction {
	instructions := []TestInstruction{}
	for _, tiEx := range tc.GetParts()[1:] {
		if st, isSt := atoms.HeadAssertion(tiEx, "System`ESameTest"); isSt {
			if len(st.GetParts()) != 3 {
				log.Fatalf("Invalid test case: %v\n", tiEx)
				continue
			}
			instructions = append(instructions, &SameTestEx{
				st.GetParts()[1], st.GetParts()[2], 0})
			continue
		}
		if st, isSt := atoms.HeadAssertion(tiEx, "System`ENearlySameTest"); isSt {
			if len(st.GetParts()) != 3 {
				log.Fatalf("Invalid test case: %v\n", tiEx)
				continue
			}
			instructions = append(instructions, &SameTestEx{
				st.GetParts()[1], st.GetParts()[2], .01})
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

func (def *Definition) annotateWithDynamicTests(
	es expreduceapi.EvalStateInterface,
) {
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
				toTestInstructions(testColExpr)...)
		} else if headSym.Name == "System`EFurtherExamples" {
			def.FurtherExamples = append(
				def.FurtherExamples,
				toTestInstructions(testColExpr)...)
		} else if headSym.Name == "System`ETests" {
			def.Tests = append(
				def.Tests,
				toTestInstructions(testColExpr)...)
		} else if headSym.Name == "System`EKnownFailures" {
			def.KnownFailures = append(
				def.KnownFailures,
				toTestInstructions(testColExpr)...)
		} else if headSym.Name == "System`EKnownDangerous" {
			def.KnownDangerous = append(
				def.KnownDangerous,
				toTestInstructions(testColExpr)...)
		} else {
			log.Fatalf("Invalid test collection: %v\n", testColExpr)
		}
	}
}

func (def *Definition) annotateWithDynamicUsage(
	es expreduceapi.EvalStateInterface,
) {
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

// AnnotateWithDynamic annotates a Definition with anything else that might have
// been defined dynamically, perhaps through the initialization of the builtin
// function through builtin Expreduce code. Helpful in generating documentation.
func (def *Definition) AnnotateWithDynamic(es expreduceapi.EvalStateInterface) {
	def.annotateWithDynamicTests(es)
	def.annotateWithDynamicUsage(es)
}

// NamedDefSet provides a means of grouping Definitions under a category name.
// This is useful for generating documentation.
type NamedDefSet struct {
	Name string
	Defs []Definition
}

// GetAllDefinitions returns a list of all builtin functions with metadata. The
// function returns a list organized by category.
func GetAllDefinitions() (defs []NamedDefSet) {
	defs = append(
		defs,
		NamedDefSet{"combinatorics", getCombinatoricsDefinitions()},
	)
	defs = append(defs, NamedDefSet{"calculus", getCalculusDefinitions()})
	defs = append(defs, NamedDefSet{"comparison", getComparisonDefinitions()})
	defs = append(defs, NamedDefSet{"atoms", getAtomsDefinitions()})
	defs = append(defs, NamedDefSet{"functional", getFunctionalDefinitions()})
	defs = append(defs, NamedDefSet{"expression", getExpressionDefinitions()})
	defs = append(
		defs,
		NamedDefSet{"equationdata", getEquationDataDefinitions()},
	)
	defs = append(defs, NamedDefSet{"solve", getSolveDefinitions()})
	defs = append(defs, NamedDefSet{"flowcontrol", getFlowControlDefinitions()})
	defs = append(defs, NamedDefSet{"list", getListDefinitions()})
	defs = append(defs, NamedDefSet{"matrix", getMatrixDefinitions()})
	defs = append(defs, NamedDefSet{"arithmetic", getArithmeticDefinitions()})
	defs = append(defs, NamedDefSet{"specialsyms", getSpecialSymsDefinitions()})
	defs = append(defs, NamedDefSet{"power", getPowerDefinitions()})
	defs = append(defs, NamedDefSet{"random", getRandomDefinitions()})
	defs = append(defs, NamedDefSet{"replacement", getReplacementDefinitions()})
	defs = append(defs, NamedDefSet{"sort", getSortDefinitions()})
	defs = append(defs, NamedDefSet{"system", getSystemDefinitions()})
	defs = append(defs, NamedDefSet{"trig", getTrigDefinitions()})
	defs = append(defs, NamedDefSet{"plot", getPlotDefinitions()})
	defs = append(defs, NamedDefSet{"string", getStringDefinitions()})
	defs = append(defs, NamedDefSet{"time", getTimeDefinitions()})
	defs = append(defs, NamedDefSet{"pattern", getPatternDefinitions()})
	defs = append(defs, NamedDefSet{"boolean", getBooleanDefinitions()})
	defs = append(defs, NamedDefSet{"simplify", getSimplifyDefinitions()})
	defs = append(
		defs,
		NamedDefSet{"numbertheory", getNumberTheoryDefinitions()},
	)
	defs = append(defs, NamedDefSet{"stats", getStatsDefinitions()})
	defs = append(defs, NamedDefSet{"manip", getManipDefinitions()})
	defs = append(defs, NamedDefSet{"rubi", getRubiDefinitions()})
	defs = append(defs, NamedDefSet{"tests", getTestsDefinitions()})

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
