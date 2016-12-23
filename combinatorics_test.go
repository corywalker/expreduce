package cas

import (
	"fmt"
	"testing"
)

func TestCombinatorics(t *testing.T) {
	fmt.Println("Testing combinatorics")

	es := NewEvalState()

	CasAssertSame(t, es, "{{5}, {4, 1}, {3, 2}, {3, 1, 1}, {2, 2, 1}, {2, 1, 1, 1}, {1, 1, 1, 1, 1}}", "IntegerPartitions[5]")
	CasAssertSame(t, es, "{{1}}", "IntegerPartitions[1]")
	CasAssertSame(t, es, "{{}}", "IntegerPartitions[0]")
	CasAssertSame(t, es, "{}", "IntegerPartitions[-1]")
	CasAssertSame(t, es, "{}", "IntegerPartitions[-5]")
	CasAssertSame(t, es, "IntegerPartitions[.5]", "IntegerPartitions[.5]")
}
