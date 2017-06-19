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

			if res, _ := IsMatchQ(this.Parts[1], this.Parts[2], EmptyPD(), es); res {
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

			&SameTest{"True", "MatchQ[foo[2 * x,2], foo[(p_ * v_), v_]]"},

			&SameTest{"True", "MatchQ[mysolve[m*x + b == 0, x], mysolve[x_*__ + _ == _, x_]]"},
			&SameTest{"False", "MatchQ[mysolve[m*x + b == 0, y], mysolve[x_*__ + _ == _, x_]]"},
			&SameTest{"True", "MatchQ[mysolve[m*x+a, m], mysolve[x_*_+a, x_]]"},
			&SameTest{"True", "MatchQ[bar[foo[a + b] + c + d, c, d, a, b], bar[w_ + x_ + foo[y_ + z_], w_, x_, y_, z_]]"},
			&SameTest{"True", "MatchQ[bar[foo[a + b] + c + d, d, c, b, a], bar[w_ + x_ + foo[y_ + z_], w_, x_, y_, z_]]"},
			&SameTest{"False", "MatchQ[bar[foo[a + b] + c + d, d, a, b, c], bar[w_ + x_ + foo[y_ + z_], w_, x_, y_, z_]]"},

			// Test order of pattern checking
			&SameTest{"Null", "rm[pattern_]:=pattern?((pats=Append[pats,{pattern[[1]],#}];True)&);"},
			&SameTest{"True", "pats={};MatchQ[foo[a,b,c],foo[x_//rm,y_//rm,z_//rm]]"},
			&SameTest{"{{x,a},{y,b},{z,c}}", "pats"},

			// Test pinning in flat
			&SameTest{"{{{a},{c}}}", "pats={};ReplaceList[ExpreduceFlatFn[a,b,c],ExpreduceFlatFn[x___//rm,b//rm,y___//rm]->{{x},{y}}]"},
			&SameTest{"{{x,a},{b[[1]],b},{y,c}}", "pats"},

			&SameTest{"{{{a,a,c}},{{a,a,c}},{{a,a,c}},{{a,a,c}}}", "pats={};ReplaceList[ExpreduceFlOrOiFn[a,a,c],ExpreduceFlOrOiFn[b___//rm,c//rm,a___//rm]->{{a,b,c}}]"},
			&SameTest{"{{{},{a,c}},{{a},{c}},{{c},{a}},{{a,c},{}}}", "pats={};ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[x___//rm,b//rm,y___//rm]->{{x},{y}}]"},
		},
		KnownFailures: []TestInstruction{
			// Test order of pattern checking
			// These probably fail because of my formparsing of PatternTest.
			// Try these without the //rm. They will most likely work.
			&SameTest{"{{c[[1]],c},{b,a},{b,a},{c[[1]],c},{a,a},{b,a},{c[[1]],c},{a,a},{b,a},{c[[1]],c},{a,a},{a,a}}", "pats"},
			// Test pinning in orderless
			&SameTest{"{{b[[1]],b},{y,a},{y,c},{b[[1]],b},{x,a},{y,c},{b[[1]],b},{x,c},{y,a},{b[[1]],b},{x,a},{x,c}}", "pats"},
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
			_, blankOk := HeadAssertion(this.Parts[2], "Blank")
			_, bsOk := HeadAssertion(this.Parts[2], "BlankSequence")
			_, bnsOk := HeadAssertion(this.Parts[2], "BlankNullSequence")
			if blankOk || bsOk || bnsOk {
				buffer.WriteString(this.Parts[1].StringForm(form))
				buffer.WriteString(this.Parts[2].StringForm(form))
			} else {
				buffer.WriteString("(")
				buffer.WriteString(this.Parts[1].StringForm(form))
				buffer.WriteString(") : (")
				buffer.WriteString(this.Parts[2].StringForm(form))
				buffer.WriteString(")")
			}
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
			&SameTest{"{1,2,3,5}", "{3, 5, 2, 1} //. {x___, y_, z_, k___} /; (Order[y, z] == -1) -> {x, z, y, k}"},
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
			&SameTest{"False", "MatchQ[{a, b}, {a_, k | a_}]"},
		},
		Tests: []TestInstruction{
			&SameTest{"False", "MatchQ[c || a || Not[b], Or[___, a_, ___, Not[And[___, a_, ___] | a_], ___]]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "FreeQ",
		Usage:  "`FreeQ[e, var]` returns True if `e` is free from any occurences of `var`.",
		Rules: []Rule{
			{"FreeQ[expr_, val_]", "expr === (expr /. val -> Internal`DummyReplace)"},
		},
		Tests: []TestInstruction{
			&SameTest{"False", "FreeQ[{0, 1, 2}, 1]"},
			&SameTest{"True", "FreeQ[{0, 1, 2}, 3]"},
			&SameTest{"False", "FreeQ[{0, 1, 2}, _Integer]"},
			&SameTest{"True", "FreeQ[{0, 1, 2}, _Real]"},
			&SameTest{"True", "FreeQ[x^2, _Real]"},
			&SameTest{"False", "FreeQ[x^2, _Integer]"},
			&SameTest{"False", "FreeQ[x^2, 2]"},
			&SameTest{"True", "FreeQ[x^2, 3]"},
			&SameTest{"True", "FreeQ[x^2, y]"},
			&SameTest{"True", "FreeQ[x^2, y]"},
			&SameTest{"False", "FreeQ[x^2, x^_Integer]"},
			&SameTest{"True", "FreeQ[x^2, y^_Integer]"},
			&SameTest{"False", "FreeQ[5*foo[x], foo]"},
			&SameTest{"True", "FreeQ[5*foo[x], bar]"},
		},
	})
	defs = append(defs, Definition{
		Name:  "ReplaceList",
		Usage: "`ReplaceList[expr, rule]` returns all the possible replacements using `rule` on `expr`.",
		legacyEvalFn: func(this *Expression, es *EvalState) Ex {
			if len(this.Parts) != 3 {
				return this
			}

			rule, isRule := HeadAssertion(this.Parts[2], "Rule")
			if !isRule {
				return this
			}
			res := NewExpression([]Ex{&Symbol{"List"}})
			mi, cont := NewMatchIter(this.Parts[1], rule.Parts[1], EmptyPD(), es)
			for cont {
				matchq, newPd, done := mi.next()
				cont = !done
				if matchq {
					res.appendEx(ReplacePD(rule.Parts[2], es, newPd))
				}
			}
			return res
		},
		SimpleExamples: []TestInstruction{
			&SameTest{"{{a, b}, {b, a}}", "ReplaceList[a + b, x_ + y_ -> {x, y}]"},
			&SameTest{"{{b, a}}", "ReplaceList[foo[a + b, b], foo[j_ + k_, j_] -> {j, k}]"},
			&SameTest{"{{a, b}, {b, a}}", "ReplaceList[foo[a + b], foo[x_ + y_] -> {x, y}]"},
			&SameTest{"{{a, b, c}, {b, a, c}}", "ReplaceList[bar[foo[a + b] + c], bar[foo[x_ + y_] + z_] -> {x, y, z}]"},
			&SameTest{"{{c, d, a, b}, {c, d, b, a}, {d, c, a, b}, {d, c, b, a}}", "ReplaceList[bar[foo[a + b] + c + d], bar[w_ + x_ + foo[y_ + z_]] -> {w, x, y, z}]"},
			&SameTest{"{}", "ReplaceList[foo[a + b, c], foo[j_ + k_, j_] -> {j, k}]"},
		},
		Tests: []TestInstruction{
			&SameTest{"{{{a},{b}},{{b},{a}}}", "ReplaceList[a+b,x__+y__->{{x},{y}}]"},
			&SameTest{"{}", "ReplaceList[a+b+c,___+a_+___->{a}]"},
			&SameTest{"{{{},{a,b}},{{a},{b}},{{a,b},{}}}", "ReplaceList[foo[a,b],foo[a___,b___]->{{a},{b}}]"},
			&SameTest{"{}", "ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a:Repeated[b_,{2}],rest___]->{{a},{rest}}]"},
			&SameTest{"{{c}}", "ReplaceList[foo[a,b,c],foo[___,a_]->{a}]"},
			&SameTest{"{{a+b+c}}", "ReplaceList[a+b+c,a_->{a}]"},
			&SameTest{"{{{},{a,b},{},{b,c}},{{},{a,b},{b},{c}},{{},{a,b},{b,c},{}},{{a},{b},{},{b,c}},{{a},{b},{b},{c}},{{a},{b},{b,c},{}},{{a,b},{},{},{b,c}},{{a,b},{},{b},{c}},{{a,b},{},{b,c},{}}}", "ReplaceList[foo[a,b,foo[b,c]],foo[a___,b___,foo[c___,d___]]->{{a},{b},{c},{d}}]"},

			&SameTest{"{{a+b+c},{b+c},{a+c},{a+b},{c},{b},{a}}", "ReplaceList[a+b+c,___+a_->{a}]"},
			&SameTest{"{{{},{a,b}},{{a},{b}},{{b},{a}},{{a,b},{}}}", "ReplaceList[a+b,x___+y___->{{x},{y}}]"},
			&SameTest{"{{{a},{b+c}},{{b},{a+c}},{{c},{a+b}},{{a+b},{c}},{{a+c},{b}},{{b+c},{a}}}", "ReplaceList[a+b+c,a_+b_->{{a},{b}}]"},
			&SameTest{"{{{a},{b,c}},{{b},{a,c}},{{c},{a,b}},{{a,b},{c}},{{a,c},{b}},{{b,c},{a}}}", "ReplaceList[a+b+c,a__+b__->{{a},{b}}]"},
			&SameTest{"{{{a},{b,c}},{{b},{a,c}},{{c},{a,b}},{{a,b},{c}},{{a,c},{b}},{{b,c},{a}}}", "ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a__,b__]->{{a},{b}}]"},
			&SameTest{"{{{a,b},{c}},{{a,c},{b}},{{b,c},{a}}}", "ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a:Repeated[_,{2}],rest___]->{{a},{rest}}]"},
			&SameTest{"{{{a,b},{c}},{{a,c},{b}},{{b,c},{a}}}", "ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a:Repeated[_,{2}],rest___]->{{a},{rest}}]"},
			&SameTest{"{{{a,b},{c,d}},{{a,c},{b,d}},{{a,d},{b,c}},{{b,c},{a,d}},{{b,d},{a,c}},{{c,d},{a,b}}}", "ReplaceList[ExpreduceOrderlessFn[a,b,c,d],ExpreduceOrderlessFn[a:Repeated[_,{2}],rest___]->{{a},{rest}}]"},

			&SameTest{"{{a+b+c},{b+c},{a+c},{a+b},{c},{b},{a}}", "ReplaceList[a+b+c,___+a_->{a}]"},
			&SameTest{"{{{},{a,b}},{{a},{b}},{{b},{a}},{{a,b},{}}}", "ReplaceList[ExpreduceOrderlessFn[a,b],ExpreduceOrderlessFn[a___,b___]->{{a},{b}}]"},

			&SameTest{"{{{a},{b},{c}},{{a},{c},{b}},{{b},{a},{c}},{{b},{c},{a}},{{c},{a},{b}},{{c},{b},{a}},{{a},{b+c},{}},{{b},{a+c},{}},{{c},{a+b},{}},{{a+b},{c},{}},{{a+c},{b},{}},{{b+c},{a},{}}}", "ReplaceList[a+b+c,a_+b_+rest___->{{a},{b},{rest}}]"},
			&SameTest{"{{{},{a,b,c}},{{a},{b,c}},{{b},{a,c}},{{c},{a,b}},{{a,b},{c}},{{a,c},{b}},{{b,c},{a}},{{a,b,c},{}}}", "ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a___,b___]->{{a},{b}}]"},
			&SameTest{"{{{a,a},{b,b,c}},{{b,b},{a,a,c}}}", "ReplaceList[ExpreduceOrderlessFn[a,a,b,b,c],ExpreduceOrderlessFn[a:Repeated[b_,{2}],rest___]->{{a},{rest}}]"},
			&SameTest{"{{a,b,c},{b,c},{a,c},{a,b},{c},{b},{a},{}}", "ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[a___,rest___]->{rest}]"},
			&SameTest{"{{{},{a,b},{},{c,d}},{{},{a,b},{c},{d}},{{},{a,b},{d},{c}},{{},{a,b},{c,d},{}},{{a},{b},{},{c,d}},{{a},{b},{c},{d}},{{a},{b},{d},{c}},{{a},{b},{c,d},{}},{{b},{a},{},{c,d}},{{b},{a},{c},{d}},{{b},{a},{d},{c}},{{b},{a},{c,d},{}},{{a,b},{},{},{c,d}},{{a,b},{},{c},{d}},{{a,b},{},{d},{c}},{{a,b},{},{c,d},{}}}", "ReplaceList[ExpreduceOrderlessFn[a,b,ExpreduceOrderlessFn[c,d]],ExpreduceOrderlessFn[a___,b___,ExpreduceOrderlessFn[c___,d___]]->{{a},{b},{c},{d}}]"},
		},
		KnownFailures: []TestInstruction{
			// Orderless has issues. Flat seems to work fine. regular ordered matching seems perfect.
			&SameTest{"{{a},{b},{c}}", "ReplaceList[ExpreduceOrderlessFn[a,b,c],ExpreduceOrderlessFn[___,a_]->{a}]"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Repeated",
		Usage:      "`Repeated[p_]` matches a sequence of expressions that match the pattern `p`.",
		Tests: []TestInstruction{
			&SameTest{"True", "MatchQ[foo[a, a], foo[Repeated[a]]]"},
			&SameTest{"False", "MatchQ[foo[a, b], foo[Repeated[a]]]"},
			&SameTest{"True", "MatchQ[foo[a], foo[Repeated[a]]]"},
			&SameTest{"False", "MatchQ[foo[], foo[Repeated[a]]]"},
			&SameTest{"True", "MatchQ[foo[1, 2, 3], foo[Repeated[_Integer]]]"},
			&SameTest{"False", "MatchQ[foo[1, 2, a], foo[Repeated[_Integer]]]"},
			&SameTest{"2", "foo[1, 2, 3] /. foo[a : (Repeated[_Integer])] -> 2"},
			&SameTest{"matches[1, 2, 3]", "foo[1, 2, 3] /. foo[a : (Repeated[_Integer])] -> matches[a]"},
			&SameTest{"foo[1, 2, 3]", "foo[1, 2, 3] /. foo[a : (Repeated[k_Integer])] -> matches[a]"},
			&SameTest{"matches[1, 1, 1]", "foo[1, 1, 1] /. foo[a : (Repeated[k_Integer])] -> matches[a]"},

			&SameTest{"True", "MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[b, {3}]]]"},
			&SameTest{"False", "MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[b, {a}]]]"},
			&SameTest{"False", "MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[b, {4}]]]"},
			&SameTest{"False", "MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[b, {2}]]]"},
			&SameTest{"False", "MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[a, Repeated[_Integer, {2}]]]"},
			&SameTest{"True", "MatchQ[ExpreduceFlOrOiFn[a, 1, 2], ExpreduceFlOrOiFn[a, Repeated[_Integer, {2}]]]"},
			&SameTest{"False", "MatchQ[ExpreduceFlOrOiFn[a, 1, 2], ExpreduceFlOrOiFn[a, Repeated[k_Integer, {2}]]]"},
			&SameTest{"True", "MatchQ[ExpreduceFlOrOiFn[a, 2, 2], ExpreduceFlOrOiFn[a, Repeated[k_Integer, {2}]]]"},
			&SameTest{"True", "MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[___, Repeated[_Integer, {0}]]]"},
			&SameTest{"False", "MatchQ[ExpreduceFlOrOiFn[a, b, b, b], ExpreduceFlOrOiFn[___, Repeated[_Integer, {-1}]]]"},

			&SameTest{"x", "foo[x, x] /. foo[Repeated[a_, {2}]] -> a"},
		},
	})
	defs = append(defs, Definition{
		Name:       "Optional",
		Usage:      "`Optional[pat, default]` attempts to match `pat` but uses `default` if not present.",
		Tests: []TestInstruction{
			&SameTest{"foo[a]", "foo[a]/.foo[a,b_.]->{a,b}"},
			&SameTest{"{a,b}", "foo[a,b]/.foo[a,b_.]->{a,b}"},
			&SameTest{"{a,c}", "foo[a]/.foo[a,b_:c]->{a,b}"},
			&SameTest{"{a,b}", "foo[a,b]/.foo[a,b_:c]->{a,b}"},
			&SameTest{"{{a},{b}}", "foo[a,b]/.foo[a___,b_.]->{{a},{b}}"},
			&SameTest{"{{a},{b}}", "foo[a,b]/.foo[a___,b_:c]->{{a},{b}}"},
			&SameTest{"{{},{a},{b}}", "foo[a,b]/.foo[a___,b_:c,d_:e]->{{a},{b},{d}}"},
			&SameTest{"{{x},{y},{z}}", "foo[x]/.foo[a_,b_:y,c_:z]->{{a},{b},{c}}"},
			&SameTest{"foo[]", "foo[]/.foo[a_,b_:y,c_:z]->{{a},{b},{c}}"},
			&SameTest{"{{x},{i},{j}}", "foo[x,i,j]/.foo[a_,b_:y,c_:z]->{{a},{b},{c}}"},

			&SameTest{"a", "a /. foo[a, c_.] -> {{c}}"},
			// This match succeeds because Plus has both a Default and has
			// OneIdentity
			&SameTest{"{{0}}", "a /. a + c_. -> {{c}}"},
			&SameTest{"False", "MatchQ[a,foo[a,c_.]]"},
			&SameTest{"True", "MatchQ[a,a+c_.]"},
			&SameTest{"False", "MatchQ[foo[a],a+c_.]"},
			&SameTest{"{{0},{0}}", "a/.a+c_.+d_.->{{c},{d}}"},
			&SameTest{"{{0},{5}}", "a/.a+c_.+d_:5->{{c},{d}}"},
			&SameTest{"{{5},{a}}", "5*a/.Optional[c1_?NumberQ]*a_->{{c1},{a}}"},
			&SameTest{"{{1},{a}}", "a/.Optional[c1_?NumberQ]*a_->{{c1},{a}}"},

			&SameTest{"False", "MatchQ[foo[a,b],foo[c1__?NumberQ]]"},
			&SameTest{"True", "MatchQ[foo[1,2],foo[c1__?NumberQ]]"},
			&SameTest{"False", "MatchQ[foo[1,2],foo[Optional[c1__?NumberQ]]]"},
			&SameTest{"True", "MatchQ[foo[1],foo[Optional[c1__?NumberQ]]]"},
		},
		KnownFailures: []TestInstruction{
			&SameTest{"foo[a,b]", "foo[a,b]/.foo[a___,b_.,d_.]->{{a},{b},{d}}"},
		},
	})
	return
}
