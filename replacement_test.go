package cas

import (
	"testing"
	"fmt"
	"github.com/stretchr/testify/assert"
)

func TestReplacement(t *testing.T) {

	fmt.Println("Testing replacement")

	es := NewEvalState()

	assert.Equal(t, "((1) == ((2 * 5^-1))) /. (((2) -> (3)) == (x))", Interp("1 == 2/5 /. 2 -> 3 == x").ToString())
	assert.Equal(t, "2^(y+1)", EvalInterp("2^(x^2+1) /. x^2->y", es).ToString())
}
