package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestInterp(t *testing.T) {
	fmt.Println("Testing interp")

	es := NewEvalState()

	assert.Equal(t, "3", EasyRun("x=1+2", es))
	assert.Equal(t, "3", EasyRun("x", es))
	assert.Equal(t, "4", EasyRun("x+1", es))
	// To make sure the result does not change
	assert.Equal(t, "4", EasyRun("x+1", es))

	assert.Equal(t, "3", EasyRun("x=1+2", es))
	assert.Equal(t, "6", EasyRun("x*2", es))
	// To make sure the result does not change
	assert.Equal(t, "6", EasyRun("x=x*2", es))
	assert.Equal(t, "36", EasyRun("x=x*x", es))

	assert.Equal(t, "(a * a)", EasyRun("y=a*a", es))
	assert.Equal(t, "(a * a * a * a)", EasyRun("y=y*y", es))
	assert.Equal(t, "2", EasyRun("a=2", es))
	assert.Equal(t, "16", EasyRun("y", es))
}
