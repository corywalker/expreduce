package expreduce

import (
	"fmt"
	"testing"

	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/stretchr/testify/assert"
)

func TestInterp(t *testing.T) {
	fmt.Println("Testing interp")

	es := NewEvalState()

	casAssertSame(t, es, "2*x", "2x")
	casAssertSame(t, es, "2*x+5*y", "2x+5y")
	casAssertSame(t, es, "2*x+5*y", "2 x+5 y")
	casAssertSame(t, es, "2*x+5*foo[x]", "2x+5foo[x]")
	casAssertSame(t, es, "2*x+5*foo[x]", "2x+5 foo[x]")

	casAssertSame(
		t,
		es,
		"{x, x, g[x], g[x]}",
		"{f[f[x]], f[x], g[f[x]], f[g[f[x]]]} //. f[xmatch_] -> xmatch",
	)
	casAssertSame(
		t,
		es,
		"foo[{x, x, g[x], g[x]}]",
		"{f[f[x]], f[x], g[f[x]], f[g[f[x]]]} //. f[xmatch_] -> xmatch // foo",
	)
	casAssertSame(t, es, "3[P[1[2]]]", "P@1@2//3")
	// TODO: Currently does not work:
	//casAssertSame(t, es, "(x^2)*y", "x^2 y")

	// Test Slots
	casAssertSame(t, es, "Slot[1]", "#")
	casAssertSame(t, es, "Slot[2]", "#2")
	casAssertSame(t, es, "3*Slot[2]", "3#2")

	// Test PatternTest
	casAssertSame(t, es, "PatternTest[a,b]", "a?b")
	//casAssertSame(t, es, "PatternTest[foo[a], bar][b]", "foo[a]?bar[b]")
	casAssertSame(t, es, "PatternTest[foo[a], bar[b]]", "foo[a]?(bar[b])")
	casAssertSame(
		t,
		es,
		"PatternTest[Pattern[a, Blank[Integer]], NumberQ]",
		"a_Integer?NumberQ",
	)
	casAssertSame(
		t,
		es,
		"PatternTest[Pattern[a, Blank[Integer]], Function[Divisible[Slot[1], 7]]]",
		"a_Integer?(Function[Divisible[#, 7]])",
	)

	// Test precedence of equality, rules, and ReplaceAll
	casAssertSame(
		t,
		es,
		"Hold[ReplaceAll[Equal[1, 2], Rule[2, Equal[3, x]]]]",
		"Hold[1 == 2 /. 2 -> 3 == x]",
	)

	// Test Condition
	casAssertSame(t, es, "Condition[a,b]", "a/;b")
	casAssertSame(t, es, "Hold[Condition[a,b]]", "Hold[a/;b]")
	//casAssertSame(t, es, "Hold[CompoundExpression[Condition[a,b],Condition[a,b]]]", "Hold[a/;b ; a/;b]")
	casAssertSame(
		t,
		es,
		"Hold[Condition[List[Pattern[x, Blank[]], Pattern[x, Blank[]]], Equal[Plus[x, x], 2]]]",
		"Hold[{x_,x_}/;x+x==2]",
	)
	casAssertSame(
		t,
		es,
		"Hold[SetDelayed[foo[Pattern[x, Blank[]]], Condition[bar[x], Equal[x, 0]]]]",
		"Hold[foo[x_] := bar[x] /; x == 0]",
	)
	casAssertSame(
		t,
		es,
		"Hold[ReplaceAll[List[5, 0, -5], Rule[Condition[Pattern[y, Blank[]], Equal[y, 0]], z]]]",
		"Hold[{5, 0, -5} /. y_ /; y == 0 -> z]",
	)

	// Test MessageName
	casAssertSame(t, es, "Hold[MessageName[a,\"b\"]]", "Hold[a::b]")
	casAssertSame(t, es, "MessageName[a,\"b\"]", "a::b")

	// Test StringJoin
	casAssertSame(
		t,
		es,
		"StringJoin[\"a\", \" world\", \"hi\"]",
		"\"a\" <> \" world\" <> \"hi\"",
	)

	// Test Not and Factorial
	casAssertSame(t, es, "Factorial[a]", "a!")
	casAssertSame(t, es, "Not[a]", "!a")
	casAssertSame(t, es, "Factorial[a]*b", "a!b")

	// Test Optional and Pattern
	// Currently disabled because issue #79
	//casAssertSame(t, es, "Plus[a,Pattern[a,5]]", "a + a : 5")
	//casAssertSame(t, es, "Plus[a,Optional[Pattern[a,Blank[]],5]]", "a + a_ : 5")
	//casAssertSame(t, es, "Plus[Times[2,a],Optional[Pattern[a,Blank[]],5]]", "a + a_ : 5 + a")

	// Test newline handling
	stringParams := ActualStringFormArgsFull("InputForm", es)
	assert.Equal(
		t,
		"CompoundExpression[a, b]",
		parser.Interp("a;b\n", es).StringForm(stringParams),
	)
	//assert.Equal(t, "Sequence[a, b]", parser.Interp("a\nb\n", es).StringForm(stringParams))
	assert.Equal(
		t,
		"c = a*b",
		parser.Interp("c = (a\nb)\n", es).StringForm(stringParams),
	)
	assert.Equal(
		t,
		"c = a*b",
		parser.Interp("c = (a\n\nb)\n", es).StringForm(stringParams),
	)
}
