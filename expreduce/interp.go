package expreduce

import (
	"math/big"
	"strings"
	"go/token"
	"os"
	"log"
	"bytes"
	"fmt"
	"github.com/corywalker/wl"
)

func fullyAssoc(op string, lhs Ex, rhs Ex) Ex {
	opExpr, isOp := HeadAssertion(lhs, op)
	if isOp {
		opExpr.Parts = append(opExpr.Parts, rhs)
		return opExpr
	}
	return NewExpression([]Ex{&Symbol{op}, lhs, rhs})
}

func rightFullyAssoc(op string, lhs Ex, rhs Ex) Ex {
	opExpr, isOp := HeadAssertion(rhs, op)
	if isOp {
		opExpr.Parts = append([]Ex{opExpr.Parts[0], lhs}, opExpr.Parts[1:]...)
		return opExpr
	}
	return NewExpression([]Ex{&Symbol{op}, lhs, rhs})
}

func addContextAndDefine(e Ex, context string, contextPath []string, es *EvalState) {
	if sym, isSym := e.(*Symbol); isSym {
		if !strings.Contains(sym.Name, "`") {
		    for _, toTry := range contextPath {
			    if es.IsDef(toTry + sym.Name) {
					sym.Name = toTry + sym.Name
					return
				}
			}
			sym.Name = context + sym.Name
		}
		es.MarkSeen(sym.Name)
	}
	expr, isExpr := e.(*Expression)
	if isExpr {
		for _, part := range expr.Parts {
			addContextAndDefine(part, context, contextPath, es)
		}
	}
}

func ParserTokenConv(tk wl.Token) Ex {
	fmt.Println(tk)
	switch tk.Rune {
	case wl.IDENT:
		return &Symbol{tk.Val}
	case wl.INT:
		base := 10
		tmpi := big.NewInt(0)
		_, ok := tmpi.SetString(tk.Val, base)
		if !ok {
			log.Fatal("Failed in integer parsing.")
		}
		return &Integer{tmpi}
	case wl.FLOAT:
		tmpf := big.NewFloat(0)
		_, ok := tmpf.SetString(tk.Val)
		if !ok {
			log.Fatal("Failed in float parsing.")
		}
		return &Flt{tmpf}
	case wl.STRING:
		return &String{tk.Val[1:len(tk.Val)-1]}
	default:
		return &Symbol{"System`UnParsedToken"}
	}
	return &Symbol{"System`UnParsedToken"}
}

func ParserTagConv(tag *wl.Tag) Ex {
	return ParserTokenConv(tag.Token)
}

func ParserTermConv(term *wl.Term) Ex {
	if term.Token2.Rune > 0 {
		switch term.Token2.Rune {
		case wl.MESSAGE:
			return NewExpression([]Ex{
				&Symbol{"System`MessageName"},
				ParserTokenConv(term.Token),
				&String{ParserTagConv(term.Tag).(*Symbol).Name},
			})
		default:
			return &Symbol{"System`UnParsedTermWithToken2"}
		}
	}
	if term.Token.Rune > 0 {
		return ParserTokenConv(term.Token)
	}
	return &Symbol{"System`UnParsedTerm"}
}

func ParserFactorConv(fact *wl.Factor) Ex {
	if fact.Term != nil {
		return ParserTermConv(fact.Term)
	}
	return &Symbol{"System`UnParsedFactor"}
}

var binaryOps = map[rune]string{
	'=': "Set",
	wl.SET_DELAYED: "SetDelayed",
}

var fullyAssocOps = map[rune]string{
	'+': "Plus",
	'*': "Times",
}

func ParserExprConv(expr *wl.Expression) Ex {
	if expr.Factor != nil {
		return ParserFactorConv(expr.Factor)
	}
	for r, head := range binaryOps {
		if expr.Token.Rune == r {
			return NewExpression([]Ex{
				&Symbol{"System`" + head},
				ParserExprConv(expr.Expression),
				ParserExprConv(expr.Expression2),
			})
		}
	}
	for r, head := range fullyAssocOps {
		if expr.Token.Rune == r {
			return fullyAssoc(
				"System`" + head,
				ParserExprConv(expr.Expression),
				ParserExprConv(expr.Expression2),
			)
		}
	}
	return &Symbol{"System`UnParsed"}
}

func Interp(src string, es *EvalState) Ex {
	buf := bytes.NewBufferString(src)
	in, err := wl.NewInput(buf, true)
	if err != nil {
		return &Symbol{"System`Null"}
	}
	expr, err := in.ParseExpression(token.NewFileSet().AddFile(os.Stdin.Name(), -1, 1e6))
	if err != nil {
		return &Symbol{"System`Null"}
	}
	parsed := ParserExprConv(expr)
	context := es.GetStringDef("System`$Context", "")
	contextPathEx := es.GetListDef("System`$ContextPath")
	contextPath := []string{}
	for _, pathPart := range contextPathEx.Parts[1:] {
		contextPath = append(contextPath, pathPart.(*String).Val)
	}
	addContextAndDefine(parsed, context, contextPath, es)
	return parsed
}

func EvalInterp(src string, es *EvalState) Ex {
	return Interp(src, es).Eval(es)
}

func EvalInterpMany(doc string, es *EvalState) Ex {
	var last Ex
	for _, expr := range strings.Split(doc, "\n\n\n") {
		if len(strings.TrimSpace(expr)) == 0 {
			continue
		}
		last = EvalInterp(expr, es)
	}
	return last
}

func EasyRun(src string, es *EvalState) string {
	context, contextPath := ActualStringFormArgs(es)
	return EvalInterp(src, es).StringForm("InputForm", context, contextPath)
}
