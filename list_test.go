package cas

import (
	"fmt"
	"testing"
)

func TestList(t *testing.T) {

	fmt.Println("Testing list")

	es := NewEvalState()

	CasAssertSame(t, es, "10", "Total[{1,2,3,4}]")
	// Use full List expression because the interpreter cannot currently
	// parse "{}"
	CasAssertSame(t, es, "0", "Total[List[]]")
	CasAssertSame(t, es, "4", "Length[{1,2,3,4}]")
	CasAssertSame(t, es, "0", "Length[List[]]")
	CasAssertSame(t, es, "1", "Length[{5}]")
	CasAssertSame(t, es, "11/2", "Mean[{5,6}]")
}
