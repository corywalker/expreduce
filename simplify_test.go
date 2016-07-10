package cas

import (
	"fmt"
	"testing"
)

func TestSimplify(t *testing.T) {

	fmt.Println("Testing simplify")

	es := NewEvalState()

	// Test combining monomials of degree 1
	intLikeTermsRule := "(c1_Integer*matcha_Symbol) + (c2_Integer*matcha_Symbol) -> (c1+c2)*matcha"
	CasAssertSame(t, es, "a+7*b", "a + 2*b + 5*b /. "+intLikeTermsRule)

	// Test a more general version
	likeTermsRule := "(c1_Integer*matcha_) + (c2_Integer*matcha_) -> (c1+c2)*matcha"
	CasAssertSame(t, es, "a+7*b", "a + 2*b + 5*b /. "+likeTermsRule)
	CasAssertDiff(t, es, "a+7*b", "a + 2*b^2 + 5*b^2 /. "+likeTermsRule)
	CasAssertSame(t, es, "a+7*b^2", "a + 2*b^2 + 5*b^2 /. "+likeTermsRule)
	CasAssertSame(t, es, "a+3*b^2", "a - 2*b^2 + 5*b^2 /. "+likeTermsRule)

	// Test using terms without a coefficient
	CasAssertSame(t, es, "a+6*b^2", "a + b^2 + 5*b^2 /. matcha_ + (matchc_Integer*matcha_) -> (1+matchc)*matcha")

	// Test additive identity
	CasAssertSame(t, es, "a", "a+0")
	CasAssertSame(t, es, "a+b", "(a+b)+0")

	// Test additive inverse
	additiveInverseRule := "amatch_ - amatch_ -> 0"
	CasAssertSame(t, es, "0", "a-a /. "+additiveInverseRule)
	CasAssertSame(t, es, "0", "-a + a /. "+additiveInverseRule)
	// Perhaps expanding negations would help here
	CasAssertSame(t, es, "0", "(a+b)-(a+b) /. "+additiveInverseRule)
	CasAssertSame(t, es, "0", "-(a+b)+(a+b) /. "+additiveInverseRule)
	CasAssertSame(t, es, "0", "2*a^2-2*a^2 /. "+additiveInverseRule)

	es.ClearAll()
}
