package cas

import (
	"fmt"
	"testing"
	"github.com/stretchr/testify/assert"
)

func TestString(t *testing.T) {
	fmt.Println("Testing string")

	es := NewEvalState()

	assert.Equal(t, "\"Plus[a, b, InputForm[Plus[c, d, FullForm[Plus[e, f]]]]]\"", EasyRun("FullForm[a + b + InputForm[c + d + FullForm[e + f]]] // ToString", es))
	assert.Equal(t, "\"a + b + InputForm[c + d + FullForm[e + f]]\"", EasyRun("InputForm[a + b + InputForm[c + d + FullForm[e + f]]] // ToString", es))
	assert.Equal(t, "\"FullForm[(a + b + InputForm[(c + d + FullForm[(e + f)])])]\"", EasyRun("ToString[FullForm[a + b + InputForm[c + d + FullForm[e + f]]], InputForm]", es))
	assert.Equal(t, "\"InputForm[(a + b + InputForm[(c + d + FullForm[(e + f)])])]\"", EasyRun("ToString[InputForm[a + b + InputForm[c + d + FullForm[e + f]]], InputForm]", es))
	assert.Equal(t, "ToString[InputForm[(a + b + InputForm[(c + d + FullForm[(e + f)])])], FullForm]", EasyRun("ToString[InputForm[a + b + InputForm[c + d + FullForm[e + f]]], FullForm]", es))

	assert.Equal(t, "\"FullForm[(a + b + InputForm[(c + d + FullForm[(e + f)])])]\"", EasyRun("ToString[FullForm[a + b + InputForm[c + d + FullForm[e + f]]], InputForm]", es))
	assert.Equal(t, "\"InputForm[(a + b + InputForm[(c + d + FullForm[(e + f)])])]\"", EasyRun("ToString[InputForm[a + b + InputForm[c + d + FullForm[e + f]]], InputForm]", es))
	assert.Equal(t, "\"Plus[a, b, InputForm[Plus[c, d, FullForm[Plus[e, f]]]]]\"", EasyRun("ToString[FullForm[a + b + InputForm[c + d + FullForm[e + f]]], OutputForm]", es))
	assert.Equal(t, "\"a + b + InputForm[c + d + FullForm[e + f]]\"", EasyRun("ToString[InputForm[a + b + InputForm[c + d + FullForm[e + f]]], OutputForm]", es))

	CasAssertSame(t, es, "\"a + b + InputForm[c + d + FullForm[e + f]]\"", "InputForm[a + b + InputForm[c + d + FullForm[e + f]]] // ToString")
	CasAssertSame(t, es, "\"a + b + InputForm[c + d + FullForm[e + f]]\"", "ToString[InputForm[a + b + InputForm[c + d + FullForm[e + f]]], OutputForm]")
	CasAssertSame(t, es, "\"InputForm[a + b + InputForm[c + d + FullForm[e + f]]]\"", "ToString[InputForm[a + b + InputForm[c + d + FullForm[e + f]]], InputForm]")
	CasAssertSame(t, es, "\"a + b + c + d + FullForm[e + f]\"", "ToString[OutputForm[a + b + InputForm[c + d + FullForm[e + f]]], OutputForm]")
	CasAssertSame(t, es, "\"Plus[a, b, InputForm[Plus[c, d, FullForm[Plus[e, f]]]]]\"", "ToString[FullForm[a + b + InputForm[c + d + FullForm[e + f]]], OutputForm]")
	CasAssertSame(t, es, "\"a + b + c + d + FullForm[e + f]\"", "ToString[OutputForm[a + b + InputForm[c + d + FullForm[e + f]]], InputForm]")
	CasAssertSame(t, es, "\"Hold[{\"a\", b, {}}]\"", "ToString[Hold[{\"a\", b, {}}], InputForm]")
	CasAssertSame(t, es, "\"Hold[{a, b, {}}]\"", "ToString[Hold[{\"a\", b, {}}], OutputForm]")
	CasAssertSame(t, es, "ToString[Hold[{\"a\", b, {}}], FullForm]", "ToString[Hold[{\"a\", b, {}}], FullForm]")
	CasAssertSame(t, es, "\"FullForm[Hold[{\"a\", b, {a + b}}]]\"", "ToString[Hold[{\"a\", b, {a + b}}] // FullForm, InputForm]")
	CasAssertSame(t, es, "\"List[\"a\", b, List[Plus[a, b]]]\"", "ToString[{\"a\", b, {a + b}} // FullForm]")
}
