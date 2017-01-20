package expreduce

import "log"

type Rule struct {
	Lhs string
	Rhs string
}

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

	// Regular rules to define. This should never include a map, as maps have
	// indeterminate iteration.
	Rules []Rule
	// Map symbol to Eval() function
	legacyEvalFn    (func(*Expression, *EvalState) Ex)
	SimpleExamples  []TestInstruction
	FurtherExamples []TestInstruction
	Tests           []TestInstruction

	toString ToStringFnType

	Attributes []string
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
	defs = append(defs, NamedDefSet{"flowcontrol", GetFlowControlDefinitions()})
	defs = append(defs, NamedDefSet{"list", GetListDefinitions()})
	defs = append(defs, NamedDefSet{"arithmetic", getArithmeticDefinitions()})
	defs = append(defs, NamedDefSet{"specialsyms", getSpecialSymsDefinitions()})
	defs = append(defs, NamedDefSet{"power", GetPowerDefinitions()})
	defs = append(defs, NamedDefSet{"random", GetRandomDefinitions()})
	defs = append(defs, NamedDefSet{"replacement", getReplacementDefinitions()})
	defs = append(defs, NamedDefSet{"sort", GetSortDefinitions()})
	defs = append(defs, NamedDefSet{"system", GetSystemDefinitions()})
	defs = append(defs, NamedDefSet{"string", GetStringDefinitions()})
	defs = append(defs, NamedDefSet{"time", GetTimeDefinitions()})
	defs = append(defs, NamedDefSet{"pattern", GetPatternDefinitions()})

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
