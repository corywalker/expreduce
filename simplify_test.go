package cas

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestSimplify(t *testing.T) {

	fmt.Println("Testing simplify")

	es := NewEvalState()

	// https://www.quia.com/jg/332021list.html

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
	additiveInverseRule := " /. amatch_ - amatch_ -> 0"
	CasAssertSame(t, es, "0", "a-a"+additiveInverseRule)
	CasAssertSame(t, es, "0", "-a + a"+additiveInverseRule)
	// Perhaps expanding negations would help here
	CasAssertSame(t, es, "0", "(a+b)-(a+b)"+additiveInverseRule+additiveInverseRule)
	CasAssertSame(t, es, "0", "-(a+b)+(a+b)"+additiveInverseRule+additiveInverseRule)
	repAdditiveInverseRule := " //. amatch_ - amatch_ -> 0"
	CasAssertSame(t, es, "0", "(a+b)-(a+b)"+repAdditiveInverseRule)
	CasAssertSame(t, es, "0", "-(a+b)+(a+b)"+repAdditiveInverseRule)

	// Test multiplicative identity
	assert.Equal(t, "5", EasyRun("5*1", es))
	assert.Equal(t, "a", EasyRun("1*a", es))
	assert.Equal(t, "(1. * a)", EasyRun("1.*a", es))

	// Test multiplicative inverse
	multInvRule := " /. amatch_ / amatch_ -> 1"
	assert.Equal(t, "1", EasyRun("8*1/8"+multInvRule, es))
	assert.Equal(t, "1", EasyRun("a*1/a"+multInvRule, es))
	assert.Equal(t, "1", EasyRun("1/a*a"+multInvRule, es))

	// Test multiplicative property of zero
	CasAssertSame(t, es, "3/2", "(((3 + (x^2 * 0)) * 2^-1)) /. (((amatch_ * 0)) -> (0))")
	es.ClearAll()

	// Test basic simplifications
	CasAssertSame(t, es, "d", "(a+b)-(a+b)+c-c+d")
	CasAssertSame(t, es, "((5 * c^a) + (3 * d))", "(a+b)-(a+b)+c-c+2*c^a+2*d+5*d+d-5*d+3*c^a")
	CasAssertSame(t, es, "87.5 + 3 * x", "((x + 80. + 3. + x) + 2. + x + 2.5)")
	CasAssertSame(t, es, "87.5 + (7. * x)", "((x + 80. + 3. + x) + 2. + (x * 2. * 2.) + (0. * 3. * x) + x + 2.5)")
	CasAssertSame(t, es, "a^(2+c)", "a^2*a^c")
	CasAssertSame(t, es, "m^4", "m^2*m^2")
	CasAssertSame(t, es, "m^2", "m*m")
	CasAssertSame(t, es, "1", "m/m")
	CasAssertSame(t, es, "1", "m^2/m^2")

	// Exponent simplifications
	CasAssertSame(t, es, "m^4", "(m^2)^2")
	CasAssertSame(t, es, "(m^2)^2.", "(m^2)^2.")
	CasAssertSame(t, es, "(m^2.)^2.", "(m^2.)^2.")
	CasAssertSame(t, es, "m^4.", "(m^2.)^2")

	// Build up algebra system by feeding simplification problems
	// Next up, solving and calculus
	CasAssertSame(t, es, "-3 * m - 10 * n", "-9 * n - n - 3 * m")
	//CasAssertSame(t, es, "7*a * b - 2*a * c", "3*a*b - 2*a*c + 4*a*b")
	// For the next two, currently having trouble combining 3ab+4ab, etc
	//CasAssertSame(t, es, "-3*a - 2*b + 3*a*b", "2*a - 4*b + 3*a*b - 5*a + 2*b")
	//CasAssertSame(t, es, "7*x - 11*y + x*y", "8*x - 9*y - 3*x*y - 2*y - x + 4*x*y")
	//CasAssertSame(t, es, "-3*a*b*c*d*e*f", "4*a*b*c*d*e*f + -7*a*b*c*d*e*f")
	//CasAssertSame(t, es, "-3*a*b*c*d*e*f", "a*b*c*4*d*e*f + -a*b*c*d*e*f*7")
	//CasAssertSame(t, es, "-3*a*b*c*d*e*f", "a*b*2*c*2*d*e*f + -a*b*c*d*e*f*7")

	//CasAssertSame(t, es, "2 r + 2 t", "2 r - 3 s - t + 3 t + 3 s")
	//CasAssertSame(t, es, "3 (x - 2 y) - 4 x y + 2 (-1 + x y)", "2 (x*y - 1) + 3 (x - 2 y) - 4 x*y")
	//CasAssertSame(t, es, "-2 + x (3 - 2 y) - 6 y", "2 (x*y - 1) + 3 (x - 2 y) - 4 x*y // BasicSimplify")
	//CasAssertSame(t, es, "-4 s + 4 r s - 3 (1 + r s)", "4 r*s - 2 s - 3 (r*s + 1) - 2 s")
	//CasAssertSame(t, es, "-3 + (-4 + r) s", "4 r*s - 2 s - 3 (r*s + 1) - 2 s // BasicSimplify")
	//CasAssertSame(t, es, "7 y - z + 3 y z", "8 y - 2 z - (y - z) + 3 y*z")
	//CasAssertSame(t, es, "-z + y (7 + 3 z)", "8 y - 2 z - (y - z) + 3 y*z // BasicSimplify")

	CasAssertSame(t, es, "Infinity", "Infinity - 1")
	CasAssertSame(t, es, "Infinity", "Infinity - 990999999")
	CasAssertSame(t, es, "Infinity", "Infinity - 990999999.")
	CasAssertSame(t, es, "Indeterminate", "Infinity - Infinity")
	// I can't simplify this type of infinity until I have ;/ rules
	//CasAssertSame(t, es, "Infinity", "Infinity*2")
	CasAssertSame(t, es, "-Infinity", "Infinity*-1")
	CasAssertSame(t, es, "-Infinity", "-Infinity + 1")
	CasAssertSame(t, es, "-Infinity", "-Infinity + 999")
	CasAssertSame(t, es, "Infinity", "-Infinity*-1")
	CasAssertSame(t, es, "0", "1/Infinity")
}
