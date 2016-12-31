package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestInterp(t *testing.T) {
	fmt.Println("Testing interp")

	es := NewEvalState()

	assert.Equal(t, "(1 + 2)", Interp("1  + 2").String())
	assert.Equal(t, "3", Interp("  1  + 2 ").Eval(es).String())
	assert.Equal(t, "3", EvalInterp("  1  + 2 ", es).String())
	assert.Equal(t, "4", EvalInterp("1+2-3+4", es).String())
	// Test that multiplication takes precedence to addition
	assert.Equal(t, "8", EvalInterp("1+2*3+1", es).String())
	assert.Equal(t, "6", EvalInterp("1+2*3-1", es).String())
	assert.Equal(t, "-6", EvalInterp("1-2*3-1", es).String())

	// Test proper behavior of unary minus sign
	assert.Equal(t, "-15", EvalInterp("5*-3", es).String())
	assert.Equal(t, "15", EvalInterp("-5*-3", es).String())
	CasAssertSame(t, es, "2*x", "2x")
	CasAssertSame(t, es, "2*x+5*y", "2x+5y")
	CasAssertSame(t, es, "2*x+5*y", "2 x+5 y")
	CasAssertSame(t, es, "2*x+5*foo[x]", "2x+5foo[x]")
	CasAssertSame(t, es, "2*x+5*foo[x]", "2x+5 foo[x]")

	CasAssertSame(t, es, "{x, x, g[x], g[x]}", "{f[f[x]], f[x], g[f[x]], f[g[f[x]]]} //. f[xmatch_] -> xmatch")
	CasAssertSame(t, es, "foo[{x, x, g[x], g[x]}]", "{f[f[x]], f[x], g[f[x]], f[g[f[x]]]} //. f[xmatch_] -> xmatch // foo")
	CasAssertSame(t, es, "3[P[1[2]]]", "P@1@2//3")
	// Currently does not work:
	//CasAssertSame(t, es, "(x^2)*y", "x^2 y")

	// Test Slots
	CasAssertSame(t, es, "Slot[1]", "#")
	CasAssertSame(t, es, "Slot[2]", "#2")
	CasAssertSame(t, es, "3*Slot[2]", "3#2")

	// Test PatternTest
	CasAssertSame(t, es, "PatternTest[a,b]", "a?b")
	//CasAssertSame(t, es, "PatternTest[foo[a], bar][b]", "foo[a]?bar[b]")
	CasAssertSame(t, es, "PatternTest[foo[a], bar[b]]", "foo[a]?(bar[b])")
	CasAssertSame(t, es, "PatternTest[Pattern[a, Blank[Integer]], NumberQ]", "a_Integer?NumberQ")
	CasAssertSame(t, es, "PatternTest[Pattern[a, Blank[Integer]], Function[Divisible[Slot[1], 7]]]", "a_Integer?(Function[Divisible[#, 7]])")

	// Test precedence of equality, rules, and ReplaceAll
	CasAssertSame(t, es, "Hold[ReplaceAll[Equal[1, 2], Rule[2, Equal[3, x]]]]", "Hold[1 == 2 /. 2 -> 3 == x]")

	// Test Condition
	CasAssertSame(t, es, "Condition[a,b]", "a/;b")
	CasAssertSame(t, es, "Hold[Condition[a,b]]", "Hold[a/;b]")
	//CasAssertSame(t, es, "Hold[CompoundExpression[Condition[a,b],Condition[a,b]]]", "Hold[a/;b ; a/;b]")
	CasAssertSame(t, es, "Hold[Condition[List[Pattern[x, Blank[]], Pattern[x, Blank[]]], Equal[Plus[x, x], 2]]]", "Hold[{x_,x_}/;x+x==2]")
	CasAssertSame(t, es, "Hold[SetDelayed[foo[Pattern[x, Blank[]]], Condition[bar[x], Equal[x, 0]]]]", "Hold[foo[x_] := bar[x] /; x == 0]")
	CasAssertSame(t, es, "Hold[ReplaceAll[List[5, 0, -5], Rule[Condition[Pattern[y, Blank[]], Equal[y, 0]], z]]]", "Hold[{5, 0, -5} /. y_ /; y == 0 -> z]")

	// Test MessageName
	CasAssertSame(t, es, "Hold[MessageName[a,b]]", "Hold[a::b]")
	CasAssertSame(t, es, "MessageName[a,\"b\"]", "a::b")
}
