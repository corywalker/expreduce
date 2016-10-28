package cas

import (
	"fmt"
	"testing"
)

func TestTimes(t *testing.T) {

	fmt.Println("Testing times")

	es := NewEvalState()

	// Test that we do not delete all the multiplicands
	CasAssertSame(t, es, "1", "1*1")
	CasAssertSame(t, es, "1", "5*1/5*1")

	// Test empty Times expressions
	CasAssertSame(t, es, "1", "Times[]")

	// Test fraction simplification
	//CasAssertSame(t, es, "25", "50/2")
	//CasAssertSame(t, es, "50", "100/2")
	//CasAssertSame(t, es, "50", "1/2*100")
	//CasAssertSame(t, es, "1/4", "1/2*1/2")
	//CasAssertSame(t, es, "5/4", "1/2*5/2")
	//CasAssertSame(t, es, "a/(b*c*d)", "a/b/c/d")

	// Test factorial
	CasAssertSame(t, es, "2432902008176640000", "Factorial[20]")
	CasAssertSame(t, es, "1", "Factorial[1]")
	CasAssertSame(t, es, "1", "Factorial[0]")
	CasAssertSame(t, es, "ComplexInfinity", "Factorial[-1]")
	CasAssertSame(t, es, "1", "Factorial[-0]")
	CasAssertSame(t, es, "ComplexInfinity", "Factorial[-10]")
	CasAssertSame(t, es, "120", "Factorial[5]")

	es.ClearAll()
}
