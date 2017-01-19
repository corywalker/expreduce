package expreduce

import "math/big"
import "math/rand"

func GetRandomDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name: "RandomReal",
		Usage: "`RandomReal[]` generates a random floating point from 0 to 1.\n\n" +
			"`RandomReal[max]` generates a random floating point from 0 to `max`.\n\n" +
			"`RandomReal[min, max]` generates a random floating point from `min` to `max.",
		Details: "`SeedRandom[UnixTime[]]` is called automatically upon " +
			"initialization of Expreduce, so random number sequences will not " +
			"repeat over subsequent sessions.",
		Rules: []Rule{
			{"RandomReal[{min_, max_}]", "RandomReal[]*(max - min) + min"},
			{"RandomReal[max_]", "RandomReal[]*max"},
		},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 1 {
				return this
			}

			return &Flt{big.NewFloat(rand.Float64())}
		},
		SimpleExamples: []TestInstruction{
			&ExampleOnlyInstruction{"0.0750914", "RandomReal[]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"Use `SeedRandom` to seed the RNG:"},
			&ExampleOnlyInstruction{"Null", "SeedRandom[3]"},
			&ExampleOnlyInstruction{"0.719983", "RandomReal[]"},
			&ExampleOnlyInstruction{"0.652631", "RandomReal[]"},
			&ExampleOnlyInstruction{"Null", "SeedRandom[3]"},
			&ExampleOnlyInstruction{"0.719983", "RandomReal[]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "SeedRandom",
		Usage: "`SeedRandom[seed]` seeds the internal random number generator with a given integer `seed`.",
		Details: "`SeedRandom[UnixTime[]]` is called automatically upon " +
			"initialization of Expreduce, so random number sequences will not " +
			"repeat over subsequent sessions.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			asInt, isInt := this.Parts[1].(*Integer)
			if isInt {
				rand.Seed(asInt.Val.Int64())
				return &Symbol{"Null"}
			}

			return this
		},
		SimpleExamples: []TestInstruction{
			&ExampleOnlyInstruction{"0.0750914", "RandomReal[]"},
			&ExampleOnlyInstruction{"Null", "SeedRandom[3]"},
			&ExampleOnlyInstruction{"0.719983", "RandomReal[]"},
			&ExampleOnlyInstruction{"0.652631", "RandomReal[]"},
			&ExampleOnlyInstruction{"Null", "SeedRandom[3]"},
			&ExampleOnlyInstruction{"0.719983", "RandomReal[]"},
		},
	})
	return
}
