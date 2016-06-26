package cas

import (
	"testing"
	"fmt"
)

func TestPattern(t *testing.T) {

	fmt.Println("Testing pattern")

	es := NewEvalState()

	CasAssertSame(t, es, "5.5", "1+1.5+3")
}
