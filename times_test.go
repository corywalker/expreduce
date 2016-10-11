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

	es.ClearAll()
}
