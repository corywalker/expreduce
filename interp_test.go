package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
)

func TestSymbol(t *testing.T) {
	fmt.Println("Testing symbol")

	es := NewEvalState()

	assert.Equal(t, "(1 + 2)", Interp("1  + 2").ToString())
	assert.Equal(t, "3", Interp("  1  + 2 ").Eval(es).ToString())
	assert.Equal(t, "3", EvalInterp("  1  + 2 ", es).ToString())
	assert.Equal(t, "4", EvalInterp("1+2-3+4", es).ToString())
	// Test that multiplication takes precedence to addition
	assert.Equal(t, "8", EvalInterp("1+2*3+1", es).ToString())
	assert.Equal(t, "6", EvalInterp("1+2*3-1", es).ToString())
	assert.Equal(t, "-6", EvalInterp("1-2*3-1", es).ToString())
}
