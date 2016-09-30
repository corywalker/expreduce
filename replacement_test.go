package cas

import (
	"fmt"
	"testing"
)

func TestReplacement(t *testing.T) {

	fmt.Println("Testing replacement")

	es := NewEvalState()

	CasAssertSame(t, es, "((1) == ((2 * 5^-1))) /. (((2) -> (3)) == (x))", "1 == 2/5 /. 2 -> 3 == x")
	CasAssertSame(t, es, "2^(y+1)", "2^(x^2+1) /. x^2->y")
	CasAssertSame(t, es, "b + c + d", "a + b + c + c^2 /. c^2 + a -> d")
	CasAssertSame(t, es, "a * b * c", "a*b*c /. c + a -> d")
	CasAssertSame(t, es, "b * d", "a*b*c /. c*a -> d")
	CasAssertSame(t, es, "2 * a + b + c + c^2", "2 * a + b + c + c^2 /. c^2 + a -> d")
	CasAssertSame(t, es, "a^2 + b + c + d", "a^2 + a + b + c + c^2 /. c^2 + a -> d")
	CasAssertSame(t, es, "a * b * c + a * b^2 * c", "(a*b*c) + (a*b^2*c)")
	CasAssertSame(t, es, "b * d + b^2 * d", "(a*b*c) + (a*b^2*c) /. c*a -> d")
	CasAssertSame(t, es, "b * d + b^2 * d", "(a*b*c) + (a*b^2*c) /. a*c -> d")
	CasAssertSame(t, es, "a + b + c", "a + b + c /. c + a -> c + a")
	CasAssertSame(t, es, "d", "a*b*c /. c*a*b -> d")
	CasAssertSame(t, es, "a * b * c", "a*b*c /. c*a*b*d -> d")
	CasAssertSame(t, es, "a*b*c*d*e", "a*b*c*d*e /. a*b*f -> z")
	CasAssertSame(t, es, "z*d*e", "a*b*c*d*e /. a*b*c -> z")
	CasAssertSame(t, es, "z*a*b", "a*b*c*d*e /. e*d*c -> z")
	CasAssertSame(t, es, "z*a*b", "a*b*c*d*e /. c*e*d -> z")

	// Using named placeholders
	CasAssertSame(t, es, "a^b", "a + b /. x_Symbol + y_Symbol -> x^y")
	CasAssertSame(t, es, "2", "x = 2")
	CasAssertSame(t, es, "2^b", "a + b /. x_Symbol + y_Symbol -> x^y")
	CasAssertSame(t, es, "2", "x")
	//CasAssertSame(t, es, "a^b", "a == b /. j_Symbol == k_Symbol -> j^k")
	CasAssertSame(t, es, "2", "a == b /. j_Equal -> 2")
	CasAssertSame(t, es, "(a == b)^k", "a == b /. j_Equal -> j^k")
	CasAssertSame(t, es, "3^k", "2^k /. base_Integer -> base + 1")
	CasAssertSame(t, es, "3^k", "2^k /. base_Integer^exp_ -> (base + 1)^exp")
	CasAssertSame(t, es, "(2 + k)^k", "2^k /. base_Integer^exp_ -> (base + exp)^exp")
	CasAssertSame(t, es, "(2 + k)^k", "2^k /. base_Integer^exp_Symbol -> (base + exp)^exp")
	CasAssertSame(t, es, "1 + (2 + k)^k", "2^k + 1 /. base_Integer^exp_Symbol -> (base + exp)^exp")
	CasAssertSame(t, es, "a^c + b", "a^c + b /. test_Symbol^test_Symbol + test_Symbol -> test + 1")
	CasAssertSame(t, es, "1 + a", "a^a + a /. test_Symbol^test_Symbol + test_Symbol -> test + 1")
	CasAssertSame(t, es, "a^a", "a^a /. (test_Symbol^test) -> 2")
	CasAssertSame(t, es, "2", "a^a /. (test_Symbol^test_Symbol) -> 2")
	CasAssertSame(t, es, "a^a", "a^a /. (test^test_Symbol) -> 2")
	CasAssertSame(t, es, "2", "test^a /. (test^test_Symbol) -> 2")
	CasAssertSame(t, es, "2", "a^test /. (test_Symbol^test) -> 2")

	es.ClearAll()
	CasAssertSame(t, es, "testa*testb", "testa*testb /. a_Symbol*a_Symbol -> 5")
	CasAssertSame(t, es, "False", "MatchQ[testa*testb, a_Symbol*a_Symbol]")
	CasAssertSame(t, es, "testa+testb", "testa+testb /. a_Symbol+a_Symbol -> 5")
	CasAssertSame(t, es, "5", "testa*testb /. a_Symbol*b_Symbol -> 5")
	CasAssertSame(t, es, "a+b", "a + b /. (b_Symbol + b_Symbol) -> 2")

	// Test matching/replacement contexts
	es.ClearAll()
	CasAssertSame(t, es, "99^k", "test = 99^k")
	CasAssertSame(t, es, "2", "99^k /. test -> 2")
	CasAssertSame(t, es, "2", "99^k /. test_ -> 2")
	CasAssertSame(t, es, "3", "test2 = 3")
	CasAssertSame(t, es, "3", "99 /. test2_Integer -> test2")

	CasAssertSame(t, es, "a^b", "a^b /. test3_Symbol^test3_Symbol -> k")
	CasAssertSame(t, es, "5", "test3 = 5")
	CasAssertSame(t, es, "a^b", "a^b /. test3_Symbol^test3_Symbol -> k")

	es.ClearAll()
	CasAssertSame(t, es, "a + 99 * b + 99 * c", "a + 2*b + 5*c /. (c1_Integer*a_Symbol) -> 99*a")
	CasAssertSame(t, es, "a + 99 * b + 5 * c", "a + 2*b + 5*c /. (2*a_Symbol) -> 99*a")
	CasAssertSame(t, es, "a + 99 * b + 99 * c", "a + 2*b + 2*c /. (2*a_Symbol) -> 99*a")
	CasAssertSame(t, es, "a + 99 * b + 99 * c + 99 * d", "a + 2*b + 3*c + 3*d /. (cl_Integer*a_Symbol) -> 99*a")

	// Work way up to combining like terms
	es.ClearAll()
	CasAssertSame(t, es, "a + 99 * b + 99 * c", "a + 2*b + 5*c /. (c1_Integer*a_Symbol) -> 99*a")
	CasAssertSame(t, es, "a + 99 * b", "a + 2*b + 5*c /. (c1_Integer*matcha_Symbol) + (c2_Integer*matchb_Symbol) -> 99*matcha")
	CasAssertSame(t, es, "a + (2 * b) + (5 * c)", "a + 2*b + 5*c /. (c1_Integer*matcha_Symbol) + (c2_Integer*matcha_Symbol) -> (c1+c2)*matcha")
	CasAssertSame(t, es, "(a + (7 * b))", "a + 2*b + 5*b /. (c1_Integer*matcha_Symbol) + (c2_Integer*matcha_Symbol) -> (c1+c2)*matcha")

	es.ClearAll()
	CasAssertSame(t, es, "2", "a + b /. (d_Symbol + c_Symbol) -> 2")
	CasAssertSame(t, es, "2 + c", "a + b + c /. (d_Symbol + c_Symbol) -> 2")
	CasAssertSame(t, es, "2 + c + d", "a + b + c + d /. (d_Symbol + c_Symbol) -> 2")
	//CasAssertSame(t, es, "99 + a + c + d", "a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch + 99")
	CasAssertSame(t, es, "b+99+c+d", "a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch + 99")
	// Causes stack overflow
	//CasAssertSame(t, es, "99 + a + b + c + d", "a + b + c + d /. (d_Symbol + c_Symbol) -> c + 99 + d")
	CasAssertSame(t, es, "a * b + c + d", "a + b + c + d /. (d_Symbol + c_Symbol) -> c*d")
	CasAssertSame(t, es, "98", "d = 98")
	//CasAssertSame(t, es, "98 + 98 * a + c", "a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch*dmatch")
	CasAssertSame(t, es, "c+98+(b*a)", "a + b + c + d /. (dmatch_Symbol + cmatch_Symbol) -> cmatch*dmatch")

	es.ClearAll()
	CasAssertSame(t, es, "2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. matcha_ - matchb_ -> 2")
	CasAssertSame(t, es, "3 * a^2 + 5 * b^2", "2 * a^2 - 2 * b^2 /. 2*matcha_ - 2*matchb_ -> 3*matcha + 5*matchb")
	CasAssertSame(t, es, "2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. _Integer*matcha_ - _Integer*matchb_ -> 2")
	CasAssertSame(t, es, "2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. _*matcha_ - _*matchb_ -> 2")
	CasAssertSame(t, es, "2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. _ - _ -> 2")
	//CasAssertSame(t, es, "2 * a^2 - 2 * b^2", "2 * a^2 - 2 * b^2 /. _ - 2*_ -> 2")

	// Test replacing functions
	CasAssertSame(t, es, "test[]", "kfdsfdsf[] /. _Symbol -> test")
	CasAssertSame(t, es, "11", "(x + 2)[5, 6] /. (2 + x) -> Plus")
	//CasAssertSame(t, es, "2", "foo[2*x, x] /. foo[matcha_Integer*matchx_, matchx_] -> matcha")

	// Test replacing with BlankSequence
	//CasAssertSame(t, es, "foo[]", "a + b /. a + b + amatch___ -> foo[amatch]")
	//CasAssertSame(t, es, "foo[b, c, d]", "a + b + c + d /. a + amatch___ -> foo[amatch]")
	//CasAssertSame(t, es, "foo[a + b + c + d]", "a + b + c + d /. amatch___ -> foo[amatch]")
	//CasAssertSame(t, es, "a + b", "a + b /. a + b + amatch__ -> foo[amatch]")
	//CasAssertSame(t, es, "foo[b, c, d]", "a + b + c + d /. a + amatch__ -> foo[amatch]")
	//CasAssertSame(t, es, "foo[a + b + c + d]", "a + b + c + d /. amatch__ -> foo[amatch]")
}
