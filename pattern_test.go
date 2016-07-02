package cas

import (
	"fmt"
	"testing"
)

func TestPattern(t *testing.T) {

	fmt.Println("Testing pattern")

	es := NewEvalState()

	// Matching patterns
	CasAssertSame(t, es, "True", "MatchQ[1, _Integer]")
	CasAssertSame(t, es, "False", "MatchQ[s, _Integer]")
	CasAssertSame(t, es, "True", "MatchQ[s, _Symbol]")
	CasAssertSame(t, es, "False", "MatchQ[1, _Symbol]")
	CasAssertSame(t, es, "False", "MatchQ[_Symbol, _Symbol]")
	CasAssertSame(t, es, "False", "MatchQ[_Integer, _Integer]")
	CasAssertSame(t, es, "True", "MatchQ[_Symbol, _Blank]")
	CasAssertSame(t, es, "True", "MatchQ[_Symbol, test_Blank]")
	CasAssertSame(t, es, "True", "MatchQ[_Symbol, test_Blank]")
	CasAssertSame(t, es, "False", "MatchQ[_Symbol, test_Symbol]")
	CasAssertSame(t, es, "False", "MatchQ[name_Symbol, test_Blank]")
	CasAssertSame(t, es, "True", "MatchQ[name_Symbol, test_Pattern]")
	CasAssertSame(t, es, "True", "MatchQ[_Symbol, test_Blank]")
	CasAssertSame(t, es, "False", "MatchQ[_Symbol, test_Pattern]")
	CasAssertSame(t, es, "False", "MatchQ[1.5, _Integer]")
	CasAssertSame(t, es, "True", "MatchQ[1.5, _Real]")
	CasAssertSame(t, es, "True", "_Symbol == _Symbol")
	CasAssertSame(t, es, "_Symbol == _Integer", "_Symbol == _Integer")
	CasAssertSame(t, es, "False", "MatchQ[_Symbol, s]")
	CasAssertSame(t, es, "False", "MatchQ[_Integer, 1]")
	CasAssertSame(t, es, "_Integer == 1", "_Integer == 1")
	CasAssertSame(t, es, "1 == _Integer", "1 == _Integer")

	CasAssertSame(t, es, "False", "_Integer === 1")
	CasAssertSame(t, es, "False", "1 === _Integer")
	CasAssertSame(t, es, "True", "_Integer === _Integer")
	CasAssertSame(t, es, "False", "_Symbol === a")
	CasAssertSame(t, es, "False", "a === _Symbol")
	CasAssertSame(t, es, "True", "_Symbol === _Symbol")

	CasAssertSame(t, es, "a == b", "a == b")
	CasAssertSame(t, es, "2", "a == b /. _Equal -> 2")
	CasAssertSame(t, es, "If[1 == k, itstrue, itsfalse]", "If[1 == k, itstrue, itsfalse]")
	CasAssertSame(t, es, "99", "If[1 == k, itstrue, itsfalse] /. _If -> 99")
	CasAssertSame(t, es, "False", "MatchQ[kfdsfdsf[], _Function]")
	CasAssertSame(t, es, "True", "MatchQ[kfdsfdsf[], _kfdsfdsf]")
	CasAssertSame(t, es, "99", "kfdsfdsf[] /. _kfdsfdsf -> 99")
	CasAssertSame(t, es, "a + b", "a + b")
	CasAssertSame(t, es, "2", "a + b /. _Plus -> 2")
	CasAssertSame(t, es, "2", "a*b /. _Times -> 2")
	CasAssertSame(t, es, "2", "a^b /. _Power -> 2")
	CasAssertSame(t, es, "2", "a -> b /. _Rule -> 2")
	CasAssertSame(t, es, "2", "a*b*c*d /. _Times -> 2")

}
