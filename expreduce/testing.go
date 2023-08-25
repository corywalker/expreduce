package expreduce

import (
	"bytes"
	"math"
	"testing"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/stretchr/testify/assert"
)

type testDesc struct {
	module string
	def    Definition
	desc   string
}

type TestInstruction interface {
	run(t *testing.T, es expreduceapi.EvalStateInterface, td testDesc) bool
}

type SameTest struct {
	Out string
	In  string
}

func (test *SameTest) run(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	td testDesc,
) bool {
	return casAssertDescSame(t, es, test.Out, test.In, td.desc)
}

type StringTest struct {
	Out string
	In  string
}

func (test *StringTest) run(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	td testDesc,
) bool {
	return assert.Equal(t, test.Out, EasyRun(test.In, es), td.desc)
}

type ExampleOnlyInstruction struct {
	Out string
	In  string
}

func (test *ExampleOnlyInstruction) run(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	td testDesc,
) bool {
	return true
}

type ResetState struct{}

func (test *ResetState) run(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	td testDesc,
) bool {
	es.ClearAll()
	return true
}

type TestComment struct {
	Comment string
}

func (test *TestComment) run(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	td testDesc,
) bool {
	return true
}

type SameTestEx struct {
	Out expreduceapi.Ex
	In  expreduceapi.Ex
	// The pecent difference we are willing to tolerate.
	floatTolerance float64
}

func (test *SameTestEx) run(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	td testDesc,
) bool {
	stringParams := ActualStringFormArgsFull("InputForm", es)
	succ, s := casTestInner(
		es,
		es.Eval(test.In),
		es.Eval(test.Out),
		test.In.StringForm(stringParams),
		true,
		td.desc,
		test.floatTolerance,
	)
	assert.True(t, succ, s)
	return succ
}

func casTestInner(
	es expreduceapi.EvalStateInterface,
	inTree expreduceapi.Ex,
	outTree expreduceapi.Ex,
	inStr string,
	test bool,
	desc string,
	floatTolerance float64,
) (succ bool, s string) {

	context, contextPath := definitionComplexityStringFormArgs()
	var buffer bytes.Buffer
	buffer.WriteString("(")
	buffer.WriteString(
		inTree.StringForm(
			expreduceapi.ToStringParams{
				Form:        "InputForm",
				Context:     context,
				ContextPath: contextPath,
				Esi:         es,
			},
		),
	)
	if test {
		buffer.WriteString(") != (")
	} else {
		buffer.WriteString(") == (")
	}
	buffer.WriteString(
		outTree.StringForm(
			expreduceapi.ToStringParams{
				Form:        "InputForm",
				Context:     context,
				ContextPath: contextPath,
				Esi:         es,
			},
		),
	)
	buffer.WriteString(")")
	buffer.WriteString("\n\tInput was: ")
	buffer.WriteString(inStr)
	if len(desc) != 0 {
		buffer.WriteString("\n\tDesc: ")
		buffer.WriteString(desc)
	}

	outFloat, outIsFloat := outTree.(*atoms.Flt)
	inFloat, inIsFloat := inTree.(*atoms.Flt)
	if floatTolerance > 0 && outIsFloat && inIsFloat {
		if outFloat.Val.Sign() == inFloat.Val.Sign() &&
			outFloat.Val.Sign() != 0 {
			inVal, _ := inFloat.Val.Float64()
			outVal, _ := outFloat.Val.Float64()
			pctDiff := (inVal - outVal) / ((inVal + outVal) / 2)
			pctDiff = math.Abs(pctDiff) * 100
			return pctDiff < floatTolerance, buffer.String()
		}
	}

	theTestTree := atoms.NewExpression([]expreduceapi.Ex{
		atoms.NewSymbol("System`SameQ"),
		atoms.NewExpression(
			[]expreduceapi.Ex{atoms.NewSymbol("System`Hold"), inTree},
		),
		atoms.NewExpression(
			[]expreduceapi.Ex{atoms.NewSymbol("System`Hold"), outTree},
		),
	})

	theTest := es.Eval(theTestTree)

	resSym, resIsSym := theTest.(*atoms.Symbol)
	if !resIsSym {
		return false, buffer.String()
	}
	if test {
		return resSym.Name == "System`True", buffer.String()
	}
	return resSym.Name == "System`False", buffer.String()
}

func casAssertSame(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	out string,
	in string,
) bool {
	succ, s := casTestInner(
		es,
		es.Eval(parser.Interp(in, es)),
		es.Eval(parser.Interp(out, es)),
		in,
		true,
		"",
		0,
	)
	assert.True(t, succ, s)
	return succ
}

func casAssertDiff(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	out string,
	in string,
) bool {
	succ, s := casTestInner(
		es,
		es.Eval(parser.Interp(in, es)),
		es.Eval(parser.Interp(out, es)),
		in,
		false,
		"",
		0,
	)
	assert.True(t, succ, s)
	return succ
}

func casAssertDescSame(
	t *testing.T,
	es expreduceapi.EvalStateInterface,
	out string,
	in string,
	desc string,
) bool {
	succ, s := casTestInner(
		es,
		es.Eval(parser.Interp(in, es)),
		es.Eval(parser.Interp(out, es)),
		in,
		true,
		desc,
		0,
	)
	assert.True(t, succ, s)
	return succ
}
