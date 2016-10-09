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

	// Symbols vs numbers
	CasAssertSame(t, es, "-1", "Order[ab, 1]")
	CasAssertSame(t, es, "1", "Order[1, ab]")

	// Sort expressions
	CasAssertSame(t, es, "-1", "Order[foo[x, y], bar[x, y]]")
	CasAssertSame(t, es, "1", "Order[bar[x, y], foo[x, y]]")
	CasAssertSame(t, es, "0", "Order[bar[x, y], bar[x, y]]")
	CasAssertSame(t, es, "1", "Order[bar[x, y], bar[x, y, z]]")
	CasAssertSame(t, es, "1", "Order[bar[x, y], bar[x, y, a]]")
	CasAssertSame(t, es, "1", "Order[bar[x, y], bar[y, z]]")
	CasAssertSame(t, es, "-1", "Order[bar[x, y], bar[w, x]]")
	CasAssertSame(t, es, "-1", "Order[fizz[foo[x, y]], fizz[bar[x, y]]]")
	CasAssertSame(t, es, "1", "Order[fizz[bar[x, y]], fizz[foo[x, y]]]")
	CasAssertSame(t, es, "0", "Order[fizz[bar[x, y]], fizz[bar[x, y]]]")
	CasAssertSame(t, es, "1", "Order[fizz[bar[x, y]], fizz[bar[x, y, z]]]")
	CasAssertSame(t, es, "1", "Order[fizz[bar[x, y]], fizz[bar[x, y, a]]]")
	CasAssertSame(t, es, "1", "Order[fizz[bar[x, y]], fizz[bar[y, z]]]")
	CasAssertSame(t, es, "-1", "Order[fizz[bar[x, y]], fizz[bar[w, x]]]")
	CasAssertSame(t, es, "-1", "Order[fizz[foo[x, y]], fizz[bar[a, y]]]")
	CasAssertSame(t, es, "-1", "Order[fizz[foo[x, y]], fizz[bar[z, y]]]")

	CasAssertSame(t, es, "1", "Order[1, a[b]]")
	CasAssertSame(t, es, "1", "Order[1., a[b]]")
	CasAssertSame(t, es, "-1", "Order[a[b], 1]")
	CasAssertSame(t, es, "-1", "Order[a[b], 1.]")
	CasAssertSame(t, es, "1", "Order[x, y[a]]")
	CasAssertSame(t, es, "1", "Order[x, w[a]]")
	CasAssertSame(t, es, "-1", "Order[w[a], x]")
	CasAssertSame(t, es, "-1", "Order[y[a], x]")
	CasAssertSame(t, es, "-1", "Order[y[], x]")
	CasAssertSame(t, es, "-1", "Order[y, x]")
	CasAssertSame(t, es, "-1", "Order[w[], x]")
	CasAssertSame(t, es, "1", "Order[w, x]")
}
