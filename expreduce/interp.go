package expreduce

import (
	"math/big"
	"strings"
	"go/token"
	"os"
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

func removeParens(ex Ex) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		for i := range expr.Parts {
			parens, isParens := NewEmptyExpression(), true
			for isParens {
				parens, isParens = HeadAssertion(expr.Parts[i], "Internal`Parens")
				if isParens {
					expr.Parts[i] = parens.Parts[1]
				}
			}
			removeParens(expr.Parts[i])
		}
	}
	return
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
		log.Fatalf("System`UnParsedToken")
	}
	log.Fatalf("System`UnParsedToken")
	return nil
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

var terminals = map[int]bool{
	138: true,  // FLOAT
	139: true,  // IDENT
	142: true,  // INT
	144: true,  // PATTERN
	145: true,  // SLOT
	146: true,  // STRING
}

var unaryOps = map[int]string{
	13: "Not",
	115: "Factorial",
	117: "Function",
}

var binaryOps = map[int]string{
	128: "Set",
	39: "SetDelayed",
	33: "ReplaceRepeated",
	31: "ReplaceAll",
	27: "Rule",
	40: "RuleDelayed",
	134: "Power",
	130: "PatternTest",
	36: "Condition",
	52: "Apply",
	38: "Map",
}

var fullyAssocOps = map[int]string{
	125: "CompoundExpression",
	119: "Plus",
	118: "Times",
	46: "Equal",
	19: "Unequal",
	47: "SameQ",
	45: "UnsameQ",
	44: "StringJoin",
	126: "Less",
	43: "LessEqual",
	129: "Greater",
	48: "GreaterEqual",
	113: "Or",
	20: "And",
	121: "Dot",
	135: "Alternatives",
}

func ParserExprConv(expr *wl.Expression) Ex {
	if _, ok := terminals[expr.Case]; ok {
		return ParserTokenConv(expr.Token)
	}
	if head, ok := binaryOps[expr.Case]; ok {
		return NewExpression([]Ex{
			&Symbol{"System`" + head},
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
		})
	}
	if head, ok := fullyAssocOps[expr.Case]; ok {
		return fullyAssoc(
			"System`" + head,
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
		)
	}
	if head, ok := unaryOps[expr.Case]; ok {
		return NewExpression([]Ex{
			&Symbol{"System`" + head},
			ParserExprConv(expr.Expression),
		})
	}

	// Special handling.
	switch expr.Case {
	case 124:
		return fullyAssoc(
			"System`CompoundExpression",
			ParserExprConv(expr.Expression),
			&Symbol{"System`Null"},
		)
	case 123:
		// TODO(corywalker): Fix parsing of "a + a_:5 + a". It should contain
		// the expression Optional[a_, 5].
		e := ParserExprConv(expr.Expression)
		head := "System`Pattern"
		if _, isPat := HeadAssertion(e, "System`Pattern"); isPat {
			head = "System`Optional"
		}
		return NewExpression([]Ex{
			&Symbol{head},
			e,
			ParserExprConv(expr.Expression2),
		})
	case 140:
		return NewExpression([]Ex{
			&Symbol{"System`MessageName"},
			ParserTokenConv(expr.Token),
			&String{ParserTagConv(expr.Tag).(*Symbol).Name},
		})
	case 132:  // a[]
		return NewExpression([]Ex{
			ParserExprConv(expr.Expression),
		})
	case 133:  // a[b]
		e := NewExpression([]Ex{
			ParserExprConv(expr.Expression),
		})
		e.appendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 17:  // {}
		return NewExpression([]Ex{
			&Symbol{"System`List"},
		})
	case 18:  // {a}
		e := NewExpression([]Ex{
			&Symbol{"System`List"},
		})
		e.appendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 14:  // (a)
		// Internal`Parens are a placeholder to prevent fullyAssoc from
		// translating "(x==2) == (x==2)" to "x == 2 == (x == 2)"
		return NewExpression([]Ex{
			&Symbol{"Internal`Parens"},
			ParserExprConv(expr.Expression),
		})
	case 54:  // a[[b]]
		e := NewExpression([]Ex{
			&Symbol{"System`Part"},
			ParserExprConv(expr.Expression),
		})
		e.appendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 16:
		e := ParserExprConv(expr.Expression)
		if integer, isInteger := e.(*Integer); isInteger {
			return &Integer{integer.Val.Neg(integer.Val)}
		} else if flt, isFlt := e.(*Flt); isFlt {
			return &Flt{flt.Val.Neg(flt.Val)}
		}
		return NewExpression([]Ex{
			&Symbol{"System`Times"},
			e,
			&Integer{big.NewInt(-1)},
		})
	case 122:
		return NewExpression([]Ex{
			&Symbol{"System`Times"},
			ParserExprConv(expr.Expression),
			NewExpression([]Ex{
				&Symbol{"System`Power"},
				ParserExprConv(expr.Expression2),
				&Integer{big.NewInt(-1)},
			}),
		})
	case 120:
		return fullyAssoc(
			"System`Plus",
			ParserExprConv(expr.Expression),
			NewExpression([]Ex{
				&Symbol{"System`Times"},
				ParserExprConv(expr.Expression2),
				&Integer{big.NewInt(-1)},
			}),
		)
	case 32:
		return NewExpression([]Ex{
			ParserExprConv(expr.Expression2),
			ParserExprConv(expr.Expression),
		})
	case 131:
		return NewExpression([]Ex{
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
		})
	}
	log.Fatalf("System`UnParsed: %+v %+v %+v", expr.Token, expr.Case, expr)
	return nil
}

func Interp(src string, es *EvalState) Ex {
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

	// Remove outer parens
	parens, isParens := NewEmptyExpression(), true
	for isParens {
		parens, isParens = HeadAssertion(parsed, "Internal`Parens")
		if isParens {
			parsed = parens.Parts[1]
		}
	}
	// Remove inner parens
	removeParens(parsed)

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
