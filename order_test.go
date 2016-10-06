package cas

import (
	"fmt"
	"testing"
)

func TestOrder(t *testing.T) {

	fmt.Println("Testing order")

	es := NewEvalState()

	// Symbol ordering
	CasAssertSame(t, es, "0", "Order[a, a]")
	CasAssertSame(t, es, "1", "Order[a, b]")
	CasAssertSame(t, es, "-1", "Order[b, a]")
	CasAssertSame(t, es, "1", "Order[a, aa]")
	CasAssertSame(t, es, "1", "Order[aa, aab]")
	CasAssertSame(t, es, "-1", "Order[aab, aa]")
	CasAssertSame(t, es, "-1", "Order[aa, a]")
	CasAssertSame(t, es, "-1", "Order[ab, aa]")

	// Number ordering
	CasAssertSame(t, es, "-1", "Order[2, 1.]")
	CasAssertSame(t, es, "1", "Order[1, 2]")
	CasAssertSame(t, es, "0", "Order[1, 1]")
	CasAssertSame(t, es, "0", "Order[1., 1.]")
	CasAssertSame(t, es, "1", "Order[1, 1.]")
	CasAssertSame(t, es, "-1", "Order[1., 1]")
}
