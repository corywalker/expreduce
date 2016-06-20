package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
)

func TestInterp(t *testing.T) {
	fmt.Println("Testing interp")

	assert.Equal(t, "(1 + 2)", Interp("1  + 2").ToString())
	assert.Equal(t, "3", Interp("  1  + 2 ").Eval().ToString())
	assert.Equal(t, "3", EvalInterp("  1  + 2 ").ToString())
}
