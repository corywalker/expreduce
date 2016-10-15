package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestFlowControl(t *testing.T) {
	fmt.Println("Testing flowcontrol")

	es := NewEvalState()

	assert.Equal(t, "True", EvalInterp("t=True", es).String())
	assert.Equal(t, "True", EvalInterp("t", es).String())
	assert.Equal(t, "False", EvalInterp("f=False", es).String())
	assert.Equal(t, "False", EvalInterp("f", es).String())

	// Basic functionality
	assert.Equal(t, "True", EvalInterp("If[t, True, False]", es).String())
	assert.Equal(t, "False", EvalInterp("If[f, True, False]", es).String())
	assert.Equal(t, "False", EvalInterp("If[t, False, True]", es).String())
	assert.Equal(t, "True", EvalInterp("If[f, False, True]", es).String())

	// Test evaluation
	assert.Equal(t, "9", EvalInterp("x=9", es).String())
	assert.Equal(t, "18", EvalInterp("If[x+3==12, x*2, x+3]", es).String())
	assert.Equal(t, "12", EvalInterp("If[x+3==11, x*2, x+3]", es).String())

	// Test replacement
	CasAssertSame(t, es, "itsfalse", "If[1 == 2, itstrue, itsfalse]")
	CasAssertSame(t, es, "itsfalse", "If[1 == 2, itstrue, itsfalse] /. (2 -> 1)")
	CasAssertSame(t, es, "itstrue", "If[1 == k, itstrue, itsfalse] /. (k -> 1)")
	CasAssertSame(t, es, "If[1 == k, itstrue, itsfalse]", "If[1 == k, itstrue, itsfalse]")
}
