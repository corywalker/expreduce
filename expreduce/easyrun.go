package expreduce

import (
	"bytes"
	"fmt"
	"strings"

	"github.com/corywalker/expreduce/expreduce/atoms"
	"github.com/corywalker/expreduce/expreduce/parser"
	"github.com/corywalker/expreduce/pkg/expreduceapi"
)

func EvalInterp(
	src string,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	return es.Eval(parser.Interp(src, es))
}

// EasyRun evaluates a string of Expreduce code and returns the result as a
// string.
func EasyRun(in string, es expreduceapi.EvalStateInterface) string {
	context, contextPath := actualStringFormArgs(es)
	stringParams := expreduceapi.ToStringParams{
		Form:        "InputForm",
		Context:     context,
		ContextPath: contextPath,
		Esi:         es,
	}
	return EvalInterp(in, es).StringForm(stringParams)
}

func EvalInterpMany(
	doc string,
	fn string,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	doc = parser.ReplaceSyms(doc)
	buf := bytes.NewBufferString(doc)
	var lastExpr expreduceapi.Ex = atoms.NewSymbol("System`Null")
	expr, err := parser.InterpBuf(buf, fn, es)
	for err == nil {
		lastExpr = es.Eval(expr)
		expr, err = parser.InterpBuf(buf, fn, es)
	}
	if !strings.HasSuffix(err.Error(), "unexpected EOF, invalid empty input") {
		fmt.Printf(
			"Syntax::sntx: %v.\nWhile parsing: %v\n\n\n",
			err,
			buf.String()[:100],
		)
	}
	return lastExpr
}

func ReadList(
	doc string,
	fn string,
	es expreduceapi.EvalStateInterface,
) expreduceapi.Ex {
	buf := bytes.NewBufferString(doc)
	l := atoms.NewExpression([]expreduceapi.Ex{atoms.NewSymbol("System`List")})
	expr, err := parser.InterpBuf(buf, fn, es)
	for err == nil {
		l.AppendEx(es.Eval(expr))
		expr, err = parser.InterpBuf(buf, fn, es)
	}
	if !strings.HasSuffix(err.Error(), "unexpected EOF, invalid empty input") {
		fmt.Printf(
			"Syntax::sntx: %v.\nWhile parsing: %v\n\n\n",
			err,
			buf.String()[:100],
		)
	}
	return l
}
