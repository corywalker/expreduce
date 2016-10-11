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

	//CasAssertSame(t, es, "{-1, -1., -0.1, 0, 0.1, 0.11, 2, 2, 2., 0.5^x, 2^x, x, 2*x, x^2, x^x, x^(2*x), X, xX, xxx, 2*y}", "Sort[{-1, -1., 0.1, 0.11, 2., -.1, 2, 0, 2, 2*x, 2*y, x, xxx, 2^x, x^2, x^x, x^(2*x), X, xX, .5^x}]")
	//CasAssertSame(t, es, "{x, 2*x, 2*x^2, y, 2*y, 2*y^2}", "Sort[{x, 2*x, y, 2*y, 2*y^2, 2*x^2}]")
}
