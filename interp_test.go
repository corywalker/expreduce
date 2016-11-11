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
}
