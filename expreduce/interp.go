package expreduce

import (
	"math/big"
	"strings"
	"go/token"
	"os"
	//"fmt"
	"log"
	"bytes"
	"github.com/cznic/wl"
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

func parsePattern(buf string) Ex {
	delim := "_"
	blankType := &Symbol{"System`Blank"}
	if strings.Contains(buf, "___") {
		delim = "___"
		blankType = &Symbol{"System`BlankNullSequence"}
	} else if strings.Contains(buf, "__") {
		delim = "__"
		blankType = &Symbol{"System`BlankSequence"}
	}
	parts := strings.Split(buf, delim)
	if len(parts) == 1 {
		return NewExpression([]Ex{&Symbol{"System`Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})
	}
	if len(parts) == 2 {
		if parts[0] == "" {
			if parts[1] == "" {
				return NewExpression([]Ex{blankType})
			} else if delim == "_" && parts[1] == "." {
				return NewExpression([]Ex{&Symbol{"System`Optional"}, NewExpression([]Ex{blankType})})
			}
			return NewExpression([]Ex{blankType, &Symbol{parts[1]}})
		} else {
			if parts[1] == "" {
				return NewExpression([]Ex{&Symbol{"System`Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})
			} else if delim == "_" && parts[1] == "." {
				return NewExpression([]Ex{&Symbol{"System`Optional"}, NewExpression([]Ex{&Symbol{"System`Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType})})})
			}
			return NewExpression([]Ex{&Symbol{"System`Pattern"}, &Symbol{parts[0]}, NewExpression([]Ex{blankType, &Symbol{parts[1]}})})
		}
	}
	return NewExpression([]Ex{&Symbol{"System`Error"}, &String{"Pattern parse error."}})
}

func ParserTokenConv(tk wl.Token) Ex {
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
		return &String{tk.Val}
	case wl.PATTERN:
		return parsePattern(tk.Val)
	case wl.SLOT:
		tmpi := big.NewInt(1)
		if tk.Val != "#" {
			_, ok := tmpi.SetString(tk.Val[1:], 10)
			if !ok {
				log.Fatal("Failed in integer parsing.")
			}
		}
		return NewExpression([]Ex{
			&Symbol{"System`Slot"},
			&Integer{tmpi},
		})

	default:
		return &Symbol{"System`UnParsedToken"}
	}
	return &Symbol{"System`UnParsedToken"}
}

func ParserTagConv(tag *wl.Tag) Ex {
	return ParserTokenConv(tag.Token)
}

func ParserExprListConv(l *wl.ExprList) (res []Ex) {
	for l != nil {
		if l.Expression != nil {
			res = append(res, ParserExprConv(l.Expression))
		} else {
			res = append(res, ParserTokenConv(l.Token))
		}
		l = l.ExprList
	}
	return
}

func ParserTermConv(term *wl.Term) Ex {
	if term.Token2.Rune > 0 {
		switch term.Token2.Rune {
		case wl.MESSAGE_NAME:
			return NewExpression([]Ex{
				&Symbol{"System`MessageName"},
				ParserTokenConv(term.Token),
				&String{ParserTagConv(term.Tag).(*Symbol).Name},
			})
		case wl.RPART:
			e := NewExpression([]Ex{
				&Symbol{"System`Part"},
				ParserTermConv(term.Term),
			})
			e.appendExArray(ParserExprListConv(term.ExprList))
			return e
		case ']':
			e := NewExpression([]Ex{
				ParserTermConv(term.Term),
			})
			e.appendExArray(ParserExprListConv(term.ExprList))
			return e
		case '}':
			e := NewExpression([]Ex{
				&Symbol{"System`List"},
			})
			e.appendExArray(ParserExprListConv(term.ExprList))
			return e
		case ')':
			return ParserExprConv(term.Expression)
		default:
			return &Symbol{"System`UnParsedTermWithToken2"}
		}
	}
	if term.Token.Rune > 0 {
		switch term.Token.Rune {
		case '!':
			return NewExpression([]Ex{
				&Symbol{"System`Factorial"},
				ParserTermConv(term.Term),
			})
		case '&':
			return NewExpression([]Ex{
				&Symbol{"System`Function"},
				ParserTermConv(term.Term),
			})
		}
		return ParserTokenConv(term.Token)
	}
	return &Symbol{"System`UnParsedTerm"}
}

func ParserFactorConv(fact *wl.Factor) Ex {
	if fact.Term != nil {
		tv := ParserTermConv(fact.Term)
		if fact.Factor != nil {
			return NewExpression([]Ex{
				&Symbol{"System`Times"},
				tv,
				ParserFactorConv(fact.Factor),
			})
		}
		return tv
	}
	return &Symbol{"System`UnParsedFactor"}
}

var binaryOps = map[int]string{
	44: "Set",
	19: "SetDelayed",
	15: "ReplaceRepeated",
	13: "ReplaceAll",
	11: "Rule",
	20: "RuleDelayed",
	48: "Power",
	46: "PatternTest",
	17: "Condition",
	28: "Apply",
	18: "Map",
}

var fullyAssocOps = map[int]string{
	36: "Plus",
	35: "Times",
	24: "Equal",
	70: "Unequal",
	25: "SameQ",
	23: "UnsameQ",
	22: "StringJoin",
	43: "Less",
	21: "LessEqual",
	45: "Greater",
	26: "GreaterEqual",
	34: "Or",
	8: "And",
	38: "Dot",
	49: "Alternatives",
}

func ParserExprConv(expr *wl.Expression) Ex {
	if expr.Factor != nil {
		return ParserFactorConv(expr.Factor)
	}
	for c, head := range binaryOps {
		if expr.Case == c {
			return NewExpression([]Ex{
				&Symbol{"System`" + head},
				ParserExprConv(expr.Expression),
				ParserExprConv(expr.Expression2),
			})
		}
	}
	for c, head := range fullyAssocOps {
		if expr.Case == c {
			return fullyAssoc(
				"System`" + head,
				ParserExprConv(expr.Expression),
				ParserExprConv(expr.Expression2),
			)
		}
	}
	switch expr.Case {
	case 14:
		return NewExpression([]Ex{
			ParserExprConv(expr.Expression2),
			ParserExprConv(expr.Expression),
		})
	case 47:
		return NewExpression([]Ex{
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
		})
	case 6:
		return NewExpression([]Ex{
			&Symbol{"System`Not"},
			ParserExprConv(expr.Expression),
		})
	case 41:
		return fullyAssoc(
			"System`CompoundExpression",
			ParserExprConv(expr.Expression),
			&Symbol{"System`Null"},
		)
	case 42:
		return fullyAssoc(
			"System`CompoundExpression",
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
		)
	case 37:
		return fullyAssoc(
			"System`Plus",
			ParserExprConv(expr.Expression),
			NewExpression([]Ex{
				&Symbol{"System`Times"},
				ParserExprConv(expr.Expression2),
				&Integer{big.NewInt(-1)},
			}),
		)
	case 7:
		e := ParserExprConv(expr.Expression)
		if integer, isInteger := e.(*Integer); isInteger {
			return &Integer{integer.Val.Neg(integer.Val)}
		} else if flt, isFlt := e.(*Flt); isFlt {
			return &Flt{flt.Val.Neg(flt.Val)}
		}
		return NewExpression([]Ex{
			&Symbol{"System`Times"},
			ParserExprConv(expr.Expression),
			&Integer{big.NewInt(-1)},
		})
	case 39:
		return NewExpression([]Ex{
			&Symbol{"System`Times"},
			ParserExprConv(expr.Expression),
			NewExpression([]Ex{
				&Symbol{"System`Power"},
				ParserExprConv(expr.Expression2),
				&Integer{big.NewInt(-1)},
			}),
		})
	case 40:
		e := ParserExprConv(expr.Expression)
		if _, isPat := HeadAssertion(e, "System`Pattern"); isPat {
			return NewExpression([]Ex{
				&Symbol{"System`Optional"},
				e,
				ParserExprConv(expr.Expression2),
			})
		}
		return NewExpression([]Ex{
			&Symbol{"System`Pattern"},
			e,
			ParserExprConv(expr.Expression2),
		})
	}
	return &Symbol{"System`UnParsed"}
}

func Interp(src string, es *EvalState) Ex {
	//fmt.Printf("Parsing %s\n", src)
	buf := bytes.NewBufferString(src)
	// TODO(corywalker): use the interactive mode for proper newline handling.
	in, err := wl.NewInput(buf, false)
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
	//fmt.Printf("result %s\n", parsed)
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
