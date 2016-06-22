
package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
)

func TestFlowControl(t *testing.T) {
	fmt.Println("Testing flowcontrol")

	es := NewEvalState()

	assert.Equal(t, "True", EvalInterp("t=True", es).ToString())
	assert.Equal(t, "True", EvalInterp("t", es).ToString())
	assert.Equal(t, "False", EvalInterp("f=False", es).ToString())
	assert.Equal(t, "False", EvalInterp("f", es).ToString())

	// Basic functionality
	assert.Equal(t, "True", EvalInterp("If[t, True, False]", es).ToString())
	assert.Equal(t, "False", EvalInterp("If[f, True, False]", es).ToString())
	assert.Equal(t, "False", EvalInterp("If[t, False, True]", es).ToString())
	assert.Equal(t, "True", EvalInterp("If[f, False, True]", es).ToString())

	// Test evaluation
	assert.Equal(t, "9", EvalInterp("x=9", es).ToString())
	assert.Equal(t, "18", EvalInterp("If[x+3==12, x*2, x+3]", es).ToString())
	assert.Equal(t, "12", EvalInterp("If[x+3==11, x*2, x+3]", es).ToString())
}
