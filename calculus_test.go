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
}
