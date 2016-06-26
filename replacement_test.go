package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
)

func TestReplacement(t *testing.T) {

	fmt.Println("Testing replacement")

	es := NewEvalState()

	assert.Equal(t, "True", EvalInterp("9*x==x*9", es).ToString())
}
