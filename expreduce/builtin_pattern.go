package expreduce

import "bytes"

func ToStringBlankType(repr string, parts []Ex, form string) (bool, string) {
	if form == "FullForm" {
		return false, ""
	}
	if len(parts) == 1 {
		return true, repr
	} else if len(parts) == 2 {
		var buffer bytes.Buffer
		buffer.WriteString(repr)
		buffer.WriteString(parts[1].String())
		return true, buffer.String()
	}
	return false, ""
}

func GetPatternDefinitions() (defs []Definition) {
	defs = append(defs, Definition{
		Name:  "MatchQ",
		Usage: "`MatchQ[expr, form]` returns True if `expr` matches `form`, False otherwise.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			if res, _ := IsMatchQ(this.Parts[1], this.Parts[2], EmptyPD(), &es.CASLogger); res {
				return &Symbol{"True"}
			} else {
				return &Symbol{"False"}
			}
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"A `Blank[]` expression matches everything:"},
			&SameTest{"True", "MatchQ[2*x, _]"},
			&TestComment{"Although a more specific pattern would have matched as well:"},
			&SameTest{"True", "MatchQ[2*x, c1_Integer*a_Symbol]"},
			&TestComment{"Since `Times` is `Orderless`, this would work as well:"},
			&SameTest{"True", "MatchQ[x*2, c1_Integer*a_Symbol]"},
			&TestComment{"As would the `FullForm`:"},
			&SameTest{"True", "MatchQ[Times[x, 2], c1_Integer*a_Symbol]"},

			&TestComment{"Named patterns must match the same expression, or the match will fail:"},
			&SameTest{"False", "MatchQ[a + b, x_Symbol + x_Symbol]"},
		},
		FurtherExamples: []TestInstruction{
			&SameTest{"True", "MatchQ[{2^a, a}, {2^x_Symbol, x_Symbol}]"},
			&SameTest{"False", "MatchQ[{2^a, b}, {2^x_Symbol, x_Symbol}]"},
			&TestComment{"`Blank` sequences allow for the matching of multiple objects. `BlankSequence` (__) matches one or more parts of the expression:"},
			&SameTest{"True", "MatchQ[{a, b}, {a, __}]"},
			&SameTest{"False", "MatchQ[{a}, {a, __}]"},
			&TestComment{"`BlankNullSequence` (___) allows for zero or more matches:"},
			&SameTest{"True", "MatchQ[{a}, {a, ___}]"},
		},
		Tests: []TestInstruction{
			&SameTest{"True", "MatchQ[2^x, base_Integer^pow_Symbol]"},
			&SameTest{"True", "MatchQ[2+x, c1_Integer+a_Symbol]"},
			&SameTest{"True", "MatchQ[a + b, x_Symbol + y_Symbol]"},
			&SameTest{"True", "MatchQ[{a,b}, {x_Symbol,y_Symbol}]"},
			&SameTest{"False", "MatchQ[{a,b}, {x_Symbol,x_Symbol}]"},
			// Test speed of OrderlessIsMatchQ
			&SameTest{"Null", "Plus[testa, testb, rest___] := bar + rest"},
			&SameTest{"bar + 1 + a + b + c + d + e + f + g", "Plus[testa,1,testb,a,b,c,d,e,f,g]"},

			&SameTest{"True", "MatchQ[foo[2*x, x], foo[matcha_Integer*matchx_, matchx_]]"},
			&SameTest{"False", "MatchQ[foo[2*x, x], bar[matcha_Integer*matchx_, matchx_]]"},
			&SameTest{"False", "MatchQ[foo[2*x, y], foo[matcha_Integer*matchx_, matchx_]]"},
			&SameTest{"False", "MatchQ[foo[x, 2*y], foo[matcha_Integer*matchx_, matchx_]]"},
		},
	})
	defs = append(defs, Definition{
		Name: "Pattern",
		Usage: "`name{BLANKFORM}` is equivalent to `Pattern[name, {BLANKFORM}]` and can be used in pattern matching to refer to the matched expression as `name`, where `{BLANKFORM}` is one of `{_, __, ___}`.\n\n" +
			"`name{BLANKFORM}head` is equivalent to `Pattern[name, {BLANKFORM}head]` and can be used in pattern matching to refer to the matched expression as `name`, where `{BLANKFORM}` is one of `{_, __, ___}`.",
		Attributes: []string{"HoldFirst"},
		toString: func(this *Expression, form string) (bool, string) {
			if len(this.Parts) != 3 {
				return false, ""
			}
			if form != "InputForm" && form != "OutputForm" {
				return false, ""
			}
			var buffer bytes.Buffer
			buffer.WriteString(this.Parts[1].StringForm(form))
			buffer.WriteString(this.Parts[2].StringForm(form))
			return true, buffer.String()
		},
		SimpleExamples: []TestInstruction{
			&TestComment{"To demonstrate referencing `name` in the replacement RHS:"},
			&SameTest{"2", "foo[2, 1] /. foo[a_, b_] -> a"},
			&TestComment{"If two matches share the same name, they must be equivalent:"},
			&SameTest{"foo[2, 1]", "foo[2, 1] /. foo[a_, a_] -> a"},
			&SameTest{"2", "foo[2, 2] /. foo[a_, a_] -> a"},
			&TestComment{"To demonstrate the head matching capability:"},
			&SameTest{"True", "MatchQ[2, a_Integer]"},
			&SameTest{"False", "MatchQ[2, a_Real]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"To demonstrate patterns matching a sequence of expressions:"},
			&SameTest{"bar[2, 1]", "foo[2, 1] /. foo[a___Integer] -> bar[a]"},
		},
	})
	defs = append(defs, Definition{
		Name: "Blank",
		Usage: "`_` matches any expression.\n\n" +
			"`_head` matches any expression with a `Head` of `head`.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringBlankType("_", this.Parts, form)
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "MatchQ[a + b, _]"},
			&SameTest{"True", "MatchQ[1, _Integer]"},
			&SameTest{"False", "MatchQ[s, _Integer]"},
			&TestComment{"`Blank` works with nonatomic `head`s:"},
			&SameTest{"2", "a*b*c*d /. _Times -> 2"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"For `Orderless` functions, the match engine will attempt to find a match in any order:"},
			&SameTest{"True", "MatchQ[x+3., c1match_Real+matcha_]"},
		},
		Tests: []TestInstruction{
			// Matching patterns
			&SameTest{"True", "MatchQ[s, _Symbol]"},
			&SameTest{"False", "MatchQ[1, _Symbol]"},
			&SameTest{"False", "MatchQ[_Symbol, _Symbol]"},
			&SameTest{"False", "MatchQ[_Integer, _Integer]"},
			&SameTest{"True", "MatchQ[_Symbol, _Blank]"},
			&SameTest{"True", "MatchQ[_Symbol, test_Blank]"},
			&SameTest{"True", "MatchQ[_Symbol, test_Blank]"},
			&SameTest{"False", "MatchQ[_Symbol, test_Symbol]"},
			&SameTest{"False", "MatchQ[name_Symbol, test_Blank]"},
			&SameTest{"True", "MatchQ[name_Symbol, test_Pattern]"},
			&SameTest{"True", "MatchQ[_Symbol, test_Blank]"},
			&SameTest{"False", "MatchQ[_Symbol, test_Pattern]"},
			&SameTest{"False", "MatchQ[1.5, _Integer]"},
			&SameTest{"True", "MatchQ[1.5, _Real]"},
			&SameTest{"True", "_Symbol == _Symbol"},
			&SameTest{"_Symbol == _Integer", "_Symbol == _Integer"},
			&SameTest{"False", "MatchQ[_Symbol, s]"},
			&SameTest{"False", "MatchQ[_Integer, 1]"},
			&SameTest{"_Integer == 1", "_Integer == 1"},
			&SameTest{"1 == _Integer", "1 == _Integer"},

			&SameTest{"False", "_Integer === 1"},
			&SameTest{"False", "1 === _Integer"},
			&SameTest{"True", "_Integer === _Integer"},
			&SameTest{"False", "_Symbol === a"},
			&SameTest{"False", "a === _Symbol"},
			&SameTest{"True", "_Symbol === _Symbol"},

			&SameTest{"a == b", "a == b"},
			&SameTest{"2", "a == b /. _Equal -> 2"},
			&SameTest{"If[1 == k, itstrue, itsfalse]", "If[1 == k, itstrue, itsfalse]"},
			&SameTest{"99", "If[1 == k, itstrue, itsfalse] /. _If -> 99"},
			&SameTest{"False", "MatchQ[kfdsfdsf[], _Function]"},
			&SameTest{"True", "MatchQ[kfdsfdsf[], _kfdsfdsf]"},
			&SameTest{"99", "kfdsfdsf[] /. _kfdsfdsf -> 99"},
			&SameTest{"a + b", "a + b"},
			&SameTest{"2", "a + b /. _Plus -> 2"},
			&SameTest{"2", "a*b /. _Times -> 2"},
			&SameTest{"2", "a^b /. _Power -> 2"},
			&SameTest{"2", "a -> b /. _Rule -> 2"},
			&SameTest{"2", "a*b*c*d /. _Times -> 2"},

			&SameTest{"True", "MatchQ[x*3., c1match_Real*matcha_]"},
			&SameTest{"True", "MatchQ[3.*x, c1match_Real*matcha_]"},
			&SameTest{"True", "MatchQ[x+3., c1match_Real+matcha_]"},
			&SameTest{"True", "MatchQ[3.+x, c1match_Real+matcha_]"},
			&SameTest{"True", "MatchQ[y + x, matcha_]"},
			&SameTest{"True", "MatchQ[y*x, matcha_]"},
		},
	})
	defs = append(defs, Definition{
		Name: "BlankSequence",
		Usage: "`__` matches any sequence of one or more expressions.\n\n" +
			"`__head` matches any sequence of one or more expressions, each with a `Head` of `head`.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringBlankType("__", this.Parts, form)
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "MatchQ[a + b + c, a + b + __]"},
			&SameTest{"False", "MatchQ[a + b + c, a + b + c + __]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"With head assertions:"},
			&SameTest{"False", "MatchQ[a * b, __Symbol]"},
			&SameTest{"False", "MatchQ[a * b, x__Symbol]"},
			&SameTest{"True", "MatchQ[a, __Symbol]"},
			&SameTest{"True", "MatchQ[a * b, x__Times]"},
			&SameTest{"False", "MatchQ[a * b, x__Plus]"},
			&SameTest{"True", "MatchQ[a + b, x__Plus]"},
		},
		Tests: []TestInstruction{
			// Be wary of the false matches - the default is usually false.
			&SameTest{"True", "MatchQ[a, __]"},
			&SameTest{"True", "MatchQ[a + b, __]"},
			&SameTest{"True", "MatchQ[a*b, __]"},
			&SameTest{"False", "MatchQ[a, a*__]"},
			&SameTest{"True", "MatchQ[a + b + c, a + b + __]"},
			&SameTest{"True", "MatchQ[a + b + c + d, a + b + __]"},
			&SameTest{"False", "MatchQ[a*b, __Symbol]"},
			&SameTest{"False", "MatchQ[a*b, x__Symbol]"},
			&SameTest{"True", "MatchQ[a, __Symbol]"},
			&SameTest{"True", "MatchQ[a*b, x__Times]"},
			&SameTest{"False", "MatchQ[a*b, x__Plus]"},
			&SameTest{"True", "MatchQ[a + b, x__Plus]"},
			&SameTest{"True", "MatchQ[a + b + c, a + x__Symbol]"},
			&SameTest{"False", "MatchQ[a + b + c, a + x__Plus]"},
			&SameTest{"True", "MatchQ[a + b, a + x__Symbol]"},
			&SameTest{"False", "MatchQ[a + b, a + x__Plus]"},
			&SameTest{"False", "MatchQ[a + b, a + b + x__Symbol]"},
			&SameTest{"False", "MatchQ[a + b, a + b + x__Plus]"},
			&SameTest{"True", "MatchQ[4*a*b*c*d*e*f, __]"},
			&SameTest{"True", "MatchQ[4*a*b*c*d*e*f, 4*__]"},
			&SameTest{"False", "MatchQ[4*a*b*c*4*d*e*f, 4*__]"},
			&SameTest{"False", "MatchQ[4*a*b*c*4*d*e*f, 4*__]"},
			&SameTest{"True", "MatchQ[a*b*c*4*d*e*f, 4*__]"},
			&SameTest{"True", "MatchQ[a*b*c*4*d*e*f, 4*__]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f, 5*__]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f + 5, 4*__]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f + 5*k, 4*__]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f + 5*k, 4*__]"},
			&SameTest{"True", "MatchQ[a*b*c*4*d*e*f + 5*k, 4*__ + 5*k]"},
			&SameTest{"False", "MatchQ[a*b*c*4*d*e*f + 2 + 5*k, 4*__ + 5*k]"},
			&SameTest{"True", "MatchQ[(a*b*c)^e, __^e]"},
			&SameTest{"False", "MatchQ[(a*b*c)^e, __^f + __^e]"},
			&SameTest{"True", "MatchQ[(a*b*c)^e + (a*b*c)^f, __^f + __^e]"},
			&SameTest{"True", "MatchQ[(a*b*c)^e + (a + b + c)^f, __^f + __^e]"},
			&SameTest{"False", "MatchQ[(a*b*c)^e + (a + b + c)^f, amatch__^f + amatch__^e]"},
			&SameTest{"True", "MatchQ[(a*b*c)^e + (a*b*c)^f, amatch__^f + amatch__^e]"},

			// Warm up for combining like terms
			&SameTest{"True", "MatchQ[bar[1, foo[a, b]], bar[amatch_Integer, foo[cmatch__]]]"},
			&SameTest{"True", "MatchQ[bar[1, foo[a, b, c]], bar[amatch_Integer, foo[cmatch__]]]"},
			&SameTest{"False", "MatchQ[bar[1, foo[]], bar[amatch_Integer, foo[cmatch__]]]"},
			&SameTest{"2", "bar[1, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> 2"},
			&SameTest{"4", "bar[1, foo[a, b]] + bar[5, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> 2"},
			&SameTest{"6 * buzz[a, b]", "bar[1, foo[a, b]] + bar[5, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> amatch*buzz[cmatch]"},
			&SameTest{"bar[3, foo[a, b]]", "bar[1, foo[a, b]] + bar[2, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] + bar[bmatch_Integer, foo[cmatch__]] -> bar[amatch + bmatch, foo[cmatch]]"},

			// Test special case of Orderless sequence matches
			&SameTest{"Null", "fooPlus[Plus[addends__]] := Hold[addends]"},
			&SameTest{"Null", "fooList[List[addends__]] := Hold[addends]"},
			&SameTest{"Null", "fooBlank[_[addends__]] := Hold[addends]"},
			&SameTest{"Hold[a, b, c]", "fooList[List[a, b, c]]"},
			&SameTest{"Hold[a, b, c]", "fooBlank[Plus[a, b, c]]"},

			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[__Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[__]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[__Real]]"},
			&SameTest{"True", "MatchQ[foo[1.], foo[__Real]]"},
			&SameTest{"False", "MatchQ[foo[], foo[__Real]]"},
			&SameTest{"True", "MatchQ[foo[1.], foo[__]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, __Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, 2, __Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, ___Integer]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, 4, ___Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, ___Integer, 3]]"},

			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, a__Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 5]]"},
		},
	})
	defs = append(defs, Definition{
		Name: "BlankNullSequence",
		Usage: "`___` matches any sequence of zero or more expressions.\n\n" +
			"`___head` matches any sequence of zero or more expressions, each with a `Head` of `head`.",
		toString: func(this *Expression, form string) (bool, string) {
			return ToStringBlankType("___", this.Parts, form)
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "MatchQ[a*b, ___]"},
			&SameTest{"True", "MatchQ[a + b, a + b + ___]"},
		},
		FurtherExamples: []TestInstruction{
			&TestComment{"With head assertions:"},
			&SameTest{"True", "MatchQ[a + b + c, a + x___Symbol]"},
			&SameTest{"False", "MatchQ[a + b + c, a + x___Plus]"},
		},
		Tests: []TestInstruction{
			&SameTest{"True", "MatchQ[a*b, ___]"},
			&SameTest{"False", "MatchQ[a, a*___]"},
			&SameTest{"False", "MatchQ[a, a + ___]"},
			&SameTest{"True", "MatchQ[a + b, a + b + ___]"},
			&SameTest{"False", "MatchQ[a*b, ___Integer]"},
			&SameTest{"False", "MatchQ[a*b, ___Symbol]"},
			&SameTest{"True", "MatchQ[a, ___Symbol]"},
			&SameTest{"False", "MatchQ[a + b, ___Symbol]"},
			&SameTest{"True", "MatchQ[a + b + c, a + x___Symbol]"},
			&SameTest{"False", "MatchQ[a + b + c, a + x___Plus]"},
			&SameTest{"True", "MatchQ[a + b, a + b + x___Symbol]"},

			&SameTest{"True", "MatchQ[foo[1.], foo[___]]"},
			&SameTest{"True", "MatchQ[foo[1.], foo[___Real]]"},
			&SameTest{"False", "MatchQ[foo[1.], foo[___Integer]]"},
			&SameTest{"True", "MatchQ[foo[], foo[___Integer]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2]]"},
			&SameTest{"False", "MatchQ[foo[1, 2], foo[1, 2, 3]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, __Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, __Integer, 3]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, __Integer, 5]]"},

			// Make sure some similar cases still work with Patterns, not just Blanks
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, a___Integer]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, 2, 3, 4, a___Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, a___Integer, 3]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3, b__Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[1, a__Integer, 3, b___Integer]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3, 4], foo[1, a__Integer, 3, b___Integer, 4]]"},
		},
	})
	defs = append(defs, Definition{
		Name: "Except",
		Usage: "`Except[pat]` matches all expressions except those that match `pat`.\n\n" +
			"`Except[pat1, pat2]` matches all expressions that match `pat2` but not `pat1`.",
		SimpleExamples: []TestInstruction{
			&SameTest{"{5, 2, x, y, 4}", "Cases[{5, 2, 3.5, x, y, 4}, Except[_Real]]"},
			&SameTest{"{5, 2, x, y, 4}", "Cases[{5, 2, a^b, x, y, 4}, Except[_Symbol^_Symbol]]"},
			&SameTest{"{a, b, 0, foo[1], foo[2], x, y}", "{a, b, 0, 1, 2, x, y} /. Except[0, a_Integer] -> foo[a]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "PatternTest",
		Usage:      "`pat?test` matches when the expression matches `pat` and `test[MATCH]` evaluates to `True`.",
		Attributes: []string{"HoldRest"},
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "MatchQ[1, _?NumberQ]"},
			&SameTest{"False", "MatchQ[a, _?NumberQ]"},
			&SameTest{"True", "MatchQ[1, 1?NumberQ]"},
			&SameTest{"False", "MatchQ[1, 1.5?NumberQ]"},
			&SameTest{"True", "MatchQ[1.5, 1.5?NumberQ]"},
			&SameTest{"{5,2,4.5}", "Cases[{5, 2, a^b, x, y, 4.5}, _?NumberQ]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Condition",
		Usage:      "`pat /; cond` matches an expression if the expression matches `pat`, and if `cond` evaluates to `True` with all the named patterns substituted in.",
		Attributes: []string{"HoldAll"},
		SimpleExamples: []TestInstruction{
			&SameTest{"True", "MatchQ[5, _ /; True]"},
			&SameTest{"False", "MatchQ[5, _ /; False]"},
			&SameTest{"True", "MatchQ[5, y_ /; True]"},
			&SameTest{"False", "MatchQ[5, y_Real /; True]"},
			&SameTest{"True", "MatchQ[5, y_Integer /; True]"},
			&SameTest{"False", "MatchQ[5, y_ /; y == 0]"},
			&SameTest{"True", "MatchQ[5, y_ /; y == 5]"},
			//&SameTest{"{1,2,3,5}", "{3, 5, 2, 1} //. {x___, y_, z_, k___} /; (Order[y, z] == -1) -> {x, z, y, k}"},
		},
	})
	defs = append(defs, Definition{
		Name:  "Alternatives",
		Usage: "`alt1 | alt2 | ...` matches an expression if it matches any pattern in the list of alternatives.",
		SimpleExamples: []TestInstruction{
			&SameTest{"Alternatives[c,d]", "c | d"},
			&SameTest{"False", "MatchQ[b, c | d]"},
			&SameTest{"True", "MatchQ[c, c | d]"},
			&SameTest{"True", "MatchQ[d, c | d]"},
			&SameTest{"{c, 1, 2}", "Cases[{a, b, c, 1, 2}, c | _Integer]"},
			&SameTest{"(1 + List)[1 + a, 1 + b, 1 + c, 1., 3]", "{a, b, c, 1., 2} /. amatch_Symbol | amatch_Integer -> amatch + 1"},
			&SameTest{"{b, c, d, e}", "Cases[{a, b, c, d, e, f}, b | c | d | e]"},
		},
	})
	return
}
