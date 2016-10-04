package cas

import (
	"fmt"
	"testing"
)

func TestSequence(t *testing.T) {

	fmt.Println("Testing sequences")

	es := NewEvalState()

	//CasAssertSame(t, es, "Sequence[2]", "Sequence[2]")
	//CasAssertSame(t, es, "Sequence[2, 3]", "Sequence[2, 3]")
	CasAssertSame(t, es, "14", "Sequence[2, 3] + Sequence[5, 4]")
	CasAssertSame(t, es, "120", "Sequence[2, 3]*Sequence[5, 4]")
	CasAssertSame(t, es, "foo[2, 3]", "foo[Sequence[2, 3]]")
	CasAssertSame(t, es, "foo[2]", "foo[Sequence[2]]")
	CasAssertSame(t, es, "foo[]", "foo[Sequence[]]")
	CasAssertSame(t, es, "foo[14]", "foo[Sequence[2, 3] + Sequence[5, 4]]")
	CasAssertSame(t, es, "foo[2, 3, 5, 4]", "foo[Sequence[2, 3], Sequence[5, 4]]")
	// The following tests will fail until the rewrite is complete.
	//CasAssertSame(t, es, "False", "Sequence[2, 3] == Sequence[2, 3]")
	//CasAssertSame(t, es, "True", "Sequence[2, 2] == Sequence[2]")
	//CasAssertSame(t, es, "False", "Sequence[2, 3] === Sequence[2, 3]")
	//CasAssertSame(t, es, "True", "Sequence[2, 2] === Sequence[2]")
}
