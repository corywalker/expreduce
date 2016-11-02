package cas

import (
	"fmt"
	//"github.com/stretchr/testify/assert"
	"testing"
)

func TestCalculus(t *testing.T) {

	fmt.Println("Testing calculus")

	es := NewEvalState()

	CasAssertSame(t, es, "1", "D[x,x]")
	CasAssertSame(t, es, "1", "D[foo,foo]")
	CasAssertSame(t, es, "0", "D[foo,bar]")
	CasAssertSame(t, es, "2", "D[bar+foo+bar,bar]")
	CasAssertSame(t, es, "2x", "D[x^2,x]")
	CasAssertSame(t, es, "2x+3x^2", "D[x^2+x^3,x]")
	CasAssertSame(t, es, "-4x^3", "D[-x^4,x]")
	CasAssertSame(t, es, "-n x^(-1 - n) + n x^(-1 + n)", "D[x^n+x^(-n),x]")
	CasAssertSame(t, es, "4 x (1 + x^2)", "D[(x^2 + 1)^2, x]")
	// All of these are correct, just not in the same form as the interpreted
	// answer.
	CasAssertSame(t, es, "1 + x + x^2/2 + x^3/6", "D[1 + x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4, x]")
	CasAssertSame(t, es, "-(10/x^3) - 7/x^2", "D[1 + 7/x + 5/(x^2), x]")
	CasAssertSame(t, es, "Sqrt[x] + x^(3/2)", "D[2/3*x^(3/2) + 2/5*x^(5/2), x]")
}
