package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestReplacement(t *testing.T) {

	fmt.Println("Testing replacement")

	es := NewEvalState()

	assert.Equal(t, "((1) == ((2 * 5^-1))) /. (((2) -> (3)) == (x))", Interp("1 == 2/5 /. 2 -> 3 == x").ToString())
	assert.Equal(t, "2^(y+1)", EvalInterp("2^(x^2+1) /. x^2->y", es).ToString())
	//CasAssertSame(t, es, "b + c + d", "a + b + c + c^2 /. c^2 + a -> d")
	//CasAssertSame(t, es, "a b c", "a*b*c /. c + a -> d")
	//CasAssertSame(t, es, "b d", "a*b*c /. c*a -> d")
	//CasAssertSame(t, es, "2 a + b + c + c^2", "2 a + b + c + c^2 /. c^2 + a -> d")
	//CasAssertSame(t, es, "2 a + b + c + c^2", "a + a + b + c + c^2 /. c^2 + a -> d")
	//CasAssertSame(t, es, "a b c + a b^2 c", "(a*b*c) + (a*b^2*c)")
	//CasAssertSame(t, es, "b d + b^2 d", "(a*b*c) + (a*b^2*c) /. c*a -> d")
	//CasAssertSame(t, es, "a + b + c", "a + b + c /. c + a -> c + a")
}
