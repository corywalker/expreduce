package cas

import (
	"fmt"
	"testing"
)

func TestSystem(t *testing.T) {
	fmt.Println("Testing system")

	es := NewEvalState()

	CasAssertSame(t, es, "1", "1")
}
