package cas

import (
	"fmt"
	"testing"
)

func TestReplacement(t *testing.T) {

	fmt.Println("Testing replacement")

	es := NewEvalState()

	CasAssertSame(t, es, "((1) == ((2 * 5^-1))) /. (((2) -> (3)) == (x))", "1 == 2/5 /. 2 -> 3 == x")
	CasAssertSame(t, es, "2^(y+1)", "2^(x^2+1) /. x^2->y")
	CasAssertSame(t, es, "b + c + d", "a + b + c + c^2 /. c^2 + a -> d")
	CasAssertSame(t, es, "a * b * c", "a*b*c /. c + a -> d")
	CasAssertSame(t, es, "b * d", "a*b*c /. c*a -> d")
	CasAssertSame(t, es, "2 * a + b + c + c^2", "2 * a + b + c + c^2 /. c^2 + a -> d")
	CasAssertSame(t, es, "a^2 + b + c + d", "a^2 + a + b + c + c^2 /. c^2 + a -> d")
	CasAssertSame(t, es, "a * b * c + a * b^2 * c", "(a*b*c) + (a*b^2*c)")
	CasAssertSame(t, es, "b * d + b^2 * d", "(a*b*c) + (a*b^2*c) /. c*a -> d")
	CasAssertSame(t, es, "b * d + b^2 * d", "(a*b*c) + (a*b^2*c) /. a*c -> d")
	CasAssertSame(t, es, "a + b + c", "a + b + c /. c + a -> c + a")
	CasAssertSame(t, es, "d", "a*b*c /. c*a*b -> d")
	CasAssertSame(t, es, "a * b * c", "a*b*c /. c*a*b*d -> d")
}
