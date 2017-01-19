package expreduce

import "math/big"
import "time"

func GetTimeDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:       "UnixTime",
		Usage: "`UnixTime[]` returns the integer seconds since the Unix epoch in UTC time.",
		Attributes: []string{"ReadProtected"},
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 1 {
				return this
			}

			return &Integer{big.NewInt(time.Now().UTC().Unix())}
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Get the current Unix timestamp:"},
			&ExampleOnlyInstruction{"1484805639", "UnixTime[]"},
			&TestComment{"`UnixTime` returns an Integer:"},
			&SameTest{"Integer", "UnixTime[] // Head"},
		},
	})
	return
}
