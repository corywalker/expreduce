package expreduce

import (
	"bytes"
	"fmt"
	"github.com/cznic/wl"
	"go/token"
	"log"
	"math/big"
	"strings"
)

func fullyAssoc(op string, lhs Ex, rhs Ex) Ex {
	opExpr, isOp := HeadAssertion(lhs, op)
	if isOp {
		opExpr.Parts = append(opExpr.Parts, rhs)
		return opExpr
	}
	return NewExpression([]Ex{NewSymbol(op), lhs, rhs})
}

func rightFullyAssoc(op string, lhs Ex, rhs Ex) Ex {
	opExpr, isOp := HeadAssertion(rhs, op)
	if isOp {
		opExpr.Parts = append([]Ex{opExpr.Parts[0], lhs}, opExpr.Parts[1:]...)
		return opExpr
	}
	return NewExpression([]Ex{NewSymbol(op), lhs, rhs})
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
	blankType := NewSymbol("System`Blank")
	if strings.Contains(buf, "___") {
		delim = "___"
		blankType = NewSymbol("System`BlankNullSequence")
	} else if strings.Contains(buf, "__") {
		delim = "__"
		blankType = NewSymbol("System`BlankSequence")
	}
	parts := strings.Split(buf, delim)
	if len(parts) == 1 {
		return NewExpression([]Ex{NewSymbol("System`Pattern"), NewSymbol(parts[0]), NewExpression([]Ex{blankType})})
	}
	if len(parts) == 2 {
		if parts[0] == "" {
			if parts[1] == "" {
				return NewExpression([]Ex{blankType})
			} else if delim == "_" && parts[1] == "." {
				return NewExpression([]Ex{NewSymbol("System`Optional"), NewExpression([]Ex{blankType})})
			}
			return NewExpression([]Ex{blankType, NewSymbol(parts[1])})
		} else {
			if parts[1] == "" {
				return NewExpression([]Ex{NewSymbol("System`Pattern"), NewSymbol(parts[0]), NewExpression([]Ex{blankType})})
			} else if delim == "_" && parts[1] == "." {
				return NewExpression([]Ex{NewSymbol("System`Optional"), NewExpression([]Ex{NewSymbol("System`Pattern"), NewSymbol(parts[0]), NewExpression([]Ex{blankType})})})
			}
			return NewExpression([]Ex{NewSymbol("System`Pattern"), NewSymbol(parts[0]), NewExpression([]Ex{blankType, NewSymbol(parts[1])})})
		}
	}
	return NewExpression([]Ex{NewSymbol("System`Error"), NewString("Pattern parse error.")})
}

func ParserTokenConv(tk wl.Token) Ex {
	switch tk.Rune {
	case wl.IDENT:
		return NewSymbol(tk.Val)
	case wl.INT:
		base := 10
		tmpi := big.NewInt(0)
		_, ok := tmpi.SetString(tk.Val, base)
		if !ok {
			log.Fatal("Failed in integer parsing.")
		}
		return NewInteger(tmpi)
	case wl.FLOAT:
		tmpf := big.NewFloat(0)
		_, ok := tmpf.SetString(tk.Val)
		if !ok {
			log.Fatal("Failed in float parsing.")
		}
		return NewReal(tmpf)
	case wl.STRING:
		return NewString(tk.Val)
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
			NewSymbol("System`Slot"),
			NewInteger(tmpi),
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
	138: true, // FLOAT
	139: true, // IDENT
	142: true, // INT
	144: true, // PATTERN
	145: true, // SLOT
	146: true, // STRING
}

var unaryOps = map[int]string{
	13:  "Not",
	115: "Factorial",
	117: "Function",
	15:  "Plus",
}

var binaryOps = map[int]string{
	128: "Set",
	39:  "SetDelayed",
	33:  "ReplaceRepeated",
	31:  "ReplaceAll",
	27:  "Rule",
	40:  "RuleDelayed",
	134: "Power",
	130: "PatternTest",
	36:  "Condition",
	52:  "Apply",
	38:  "Map",
}

var fullyAssocOps = map[int]string{
	125: "CompoundExpression",
	119: "Plus",
	118: "Times",
	46:  "Equal",
	19:  "Unequal",
	47:  "SameQ",
	45:  "UnsameQ",
	44:  "StringJoin",
	126: "Less",
	43:  "LessEqual",
	129: "Greater",
	48:  "GreaterEqual",
	113: "Or",
	20:  "And",
	121: "Dot",
	135: "Alternatives",
	42:  "Span",
}

func ParserExprConv(expr *wl.Expression) Ex {
	if _, ok := terminals[expr.Case]; ok {
		return ParserTokenConv(expr.Token)
	}
	if head, ok := binaryOps[expr.Case]; ok {
		return NewExpression([]Ex{
			NewSymbol("System`" + head),
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
		})
	}
	if head, ok := fullyAssocOps[expr.Case]; ok {
		return fullyAssoc(
			"System`"+head,
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
		)
	}
	if head, ok := unaryOps[expr.Case]; ok {
		return NewExpression([]Ex{
			NewSymbol("System`" + head),
			ParserExprConv(expr.Expression),
		})
	}

	// Special handling.
	switch expr.Case {
	case 124:
		return fullyAssoc(
			"System`CompoundExpression",
			ParserExprConv(expr.Expression),
			NewSymbol("System`Null"),
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
			NewSymbol(head),
			e,
			ParserExprConv(expr.Expression2),
		})
	case 140:
		return NewExpression([]Ex{
			NewSymbol("System`MessageName"),
			ParserTokenConv(expr.Token),
			NewString(ParserTagConv(expr.Tag).(*Symbol).Name),
		})
	case 132: // a[]
		return NewExpression([]Ex{
			ParserExprConv(expr.Expression),
		})
	case 133: // a[b]
		e := NewExpression([]Ex{
			ParserExprConv(expr.Expression),
		})
		e.appendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 17: // {}
		return NewExpression([]Ex{
			NewSymbol("System`List"),
		})
	case 18: // {a}
		e := NewExpression([]Ex{
			NewSymbol("System`List"),
		})
		e.appendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 14: // (a)
		// Internal`Parens are a placeholder to prevent fullyAssoc from
		// translating "(x==2) == (x==2)" to "x == 2 == (x == 2)"
		return NewExpression([]Ex{
			NewSymbol("Internal`Parens"),
			ParserExprConv(expr.Expression),
		})
	case 54: // a[[b]]
		e := NewExpression([]Ex{
			NewSymbol("System`Part"),
			ParserExprConv(expr.Expression),
		})
		e.appendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 16:
		e := ParserExprConv(expr.Expression)
		if integer, isInteger := e.(*Integer); isInteger {
			return NewInteger(integer.Val.Neg(integer.Val))
		} else if flt, isFlt := e.(*Flt); isFlt {
			return NewReal(flt.Val.Neg(flt.Val))
		}
		return NewExpression([]Ex{
			NewSymbol("System`Times"),
			e,
			NewInteger(big.NewInt(-1)),
		})
	case 122:
		return NewExpression([]Ex{
			NewSymbol("System`Times"),
			ParserExprConv(expr.Expression),
			NewExpression([]Ex{
				NewSymbol("System`Power"),
				ParserExprConv(expr.Expression2),
				NewInteger(big.NewInt(-1)),
			}),
		})
	case 120:
		return fullyAssoc(
			"System`Plus",
			ParserExprConv(expr.Expression),
			NewExpression([]Ex{
				NewSymbol("System`Times"),
				ParserExprConv(expr.Expression2),
				NewInteger(big.NewInt(-1)),
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
	case 35:
		set := ParserExprConv(expr.Expression2).(*Expression)
		head := "System`TagSet"
		if _, isDelayed := HeadAssertion(set, "System`SetDelayed"); isDelayed {
			head = "System`TagSetDelayed"
		}
		e := NewExpression([]Ex{
			NewSymbol(head),
			ParserExprConv(expr.Expression),
			set.Parts[1],
			set.Parts[2],
		})
		return e
	case 137:
		return NewExpression([]Ex{
			NewExpression([]Ex{
				NewSymbol("System`Derivative"),
				NewInt(1),
			}),
			ParserExprConv(expr.Expression),
		})
	}
	log.Fatalf("System`UnParsed: %+v %+v %+v", expr.Token, expr.Case, expr)
	return nil
}

func InterpBuf(buf *bytes.Buffer, fn string, es *EvalState) (Ex, error) {
	// TODO(corywalker): use the interactive mode for proper newline handling.
	in, err := wl.NewInput(buf, true)
	if err != nil {
		panic(err)
	}
	expr, err := in.ParseExpression(token.NewFileSet().AddFile(fn, -1, 1e6))
	if err != nil {
		return NewSymbol("System`Null"), err
	}
	parsed := ParserExprConv(expr)
	//fmt.Println(parsed)

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
	return parsed, nil
}

func Interp(src string, es *EvalState) Ex {
	buf := bytes.NewBufferString(src)
	expr, err := InterpBuf(buf, "nofile", es)
	if err != nil {
		fmt.Printf("Syntax::sntx: %v.\n\n\n", err)
		return NewSymbol("System`Null")
	}
	return expr
}

func EvalInterp(src string, es *EvalState) Ex {
	return Interp(src, es).Eval(es)
}

func EvalInterpMany(doc string, fn string, es *EvalState) Ex {
	buf := bytes.NewBufferString(doc)
	var lastExpr Ex = NewSymbol("System`Null")
	expr, err := InterpBuf(buf, fn, es)
	for err == nil {
		lastExpr = expr.Eval(es)
		expr, err = InterpBuf(buf, fn, es)
	}
	if !strings.HasSuffix(err.Error(), "unexpected EOF, invalid empty input") {
		fmt.Printf("Syntax::sntx: %v.\nWhile parsing: %v\n\n\n", err, buf.String()[:100])
	}
	return lastExpr
}

func ReadList(doc string, fn string, es *EvalState) Ex {
	buf := bytes.NewBufferString(doc)
	l := NewExpression([]Ex{NewSymbol("System`List")})
	expr, err := InterpBuf(buf, fn, es)
	for err == nil {
		l.appendEx(expr.Eval(es))
		expr, err = InterpBuf(buf, fn, es)
	}
	if !strings.HasSuffix(err.Error(), "unexpected EOF, invalid empty input") {
		fmt.Printf("Syntax::sntx: %v.\nWhile parsing: %v\n\n\n", err, buf.String()[:100])
	}
	return l
}

func EasyRun(src string, es *EvalState) string {
	context, contextPath := ActualStringFormArgs(es)
	return EvalInterp(src, es).StringForm(ToStringParams{"InputForm", context, contextPath})
}
