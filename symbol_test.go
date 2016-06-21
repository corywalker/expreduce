package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
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
}
