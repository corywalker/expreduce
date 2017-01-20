package expreduce

import (
	"sort"
)

func GetSortDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "Sort",
		Usage: "`Sort[list]` sorts the elements in list according to `Order`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 2 {
				return this
			}

			exp, ok := this.Parts[1].(*Expression)
			if ok {
				sort.Sort(exp)
				return exp
			}
			return this
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"Sort a list of numbers:"},
			&SameTest{"{-5.1, 2, 3.2, 6}", "Sort[{6, 2, 3.2, -5.1}]"},
			&TestComment{"Sort a list of strings:"},
			&SameTest{"{\"a\", \"aa\", \"hello\", \"zzz\"}", "Sort[{\"hello\", \"a\", \"aa\", \"zzz\"}]"},
			&TestComment{"Sort a list of symbols:"},
			&SameTest{"{a, b, c, d}", "Sort[{d, a, b, c}]"},
			&TestComment{"Sort a list of heterogenous expressions:"},
			&SameTest{"{5, h, bar[a^x], foo[y, 2]}", "Sort[{5, h, foo[y, 2], bar[a^x]}]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"The object to sort need not be a list:"},
			&SameTest{"foo[a, b, c, d]", "Sort[foo[d, a, b, c]]"},
		},
	})
	return
}
