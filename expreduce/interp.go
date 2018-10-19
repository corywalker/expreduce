package expreduce

import (
	"bytes"
	"fmt"
	"go/token"
	"log"
	"math/big"
	"strings"

	"github.com/corywalker/expreduce/pkg/expreduceapi"
	"github.com/cznic/wl"
)

var inequalityOps = map[string]bool{
	"System`Equal":        true,
	"System`Unequal":      true,
	"System`Less":         true,
	"System`LessEqual":    true,
	"System`Greater":      true,
	"System`GreaterEqual": true,
}

func convertToInequality(expr expreduceapi.ExpressionInterface) expreduceapi.ExpressionInterface {
	res := E(S("Inequality"))
	for i, e := range expr.GetParts()[1:] {
		if i != 0 {
			res.AppendEx(expr.GetParts()[0])
		}
		res.AppendEx(e)
	}
	return res
}

func fullyAssoc(op string, lhs expreduceapi.Ex, rhs expreduceapi.Ex) expreduceapi.Ex {
	_, opIsIneq := inequalityOps[op]
	if opIsIneq {
		lhsEx, lhsIsEx := lhs.(expreduceapi.ExpressionInterface)
		if lhsIsEx {
			lhsHead := lhsEx.HeadStr()
			_, lhsIsIneq := inequalityOps[lhsHead]
			lhsIsIneq = lhsIsIneq || lhsHead == "System`Inequality"
			if lhsIsIneq && op != lhsHead {
				res := lhsEx
				if lhsHead != "System`Inequality" {
					res = convertToInequality(lhsEx)
				}
				res.AppendEx(NewSymbol(op))
				res.AppendEx(rhs)
				return res
			}
		}
	}
	opExpr, isOp := HeadAssertion(lhs, op)
	if isOp {
		opExpr.AppendEx(rhs)
		return opExpr
	}
	return NewExpression([]expreduceapi.Ex{NewSymbol(op), lhs, rhs})
}

func removeParens(ex expreduceapi.Ex) {
	expr, isExpr := ex.(expreduceapi.ExpressionInterface)
	if isExpr {
		for i := range expr.GetParts() {
			parens, isParens := NewEmptyExpression(), true
			for isParens {
				parens, isParens = HeadAssertion(expr.GetParts()[i], "Internal`Parens")
				if isParens {
					expr.GetParts()[i] = parens.GetParts()[1]
				}
			}
			removeParens(expr.GetParts()[i])
		}
	}
	return
}

func addContextAndDefine(e expreduceapi.Ex, context string, ContextPath []string, es expreduceapi.EvalStateInterface) {
	if sym, isSym := e.(*Symbol); isSym {
		if !strings.Contains(sym.Name, "`") {
			for _, toTry := range ContextPath {
				if es.IsDef(toTry + sym.Name) {
					sym.Name = toTry + sym.Name
					return
				}
			}
			sym.Name = context + sym.Name
		}
		es.MarkSeen(sym.Name)
	}
	expr, isExpr := e.(expreduceapi.ExpressionInterface)
	if isExpr {
		for _, part := range expr.GetParts() {
			addContextAndDefine(part, context, ContextPath, es)
		}
	}
}

func parsePattern(buf string) expreduceapi.Ex {
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
		return NewExpression([]expreduceapi.Ex{NewSymbol("System`Pattern"), NewSymbol(parts[0]), NewExpression([]expreduceapi.Ex{blankType})})
	}
	if len(parts) == 2 {
		if parts[0] == "" {
			if parts[1] == "" {
				return NewExpression([]expreduceapi.Ex{blankType})
			} else if delim == "_" && parts[1] == "." {
				return NewExpression([]expreduceapi.Ex{NewSymbol("System`Optional"), NewExpression([]expreduceapi.Ex{blankType})})
			}
			return NewExpression([]expreduceapi.Ex{blankType, NewSymbol(parts[1])})
		} else {
			if parts[1] == "" {
				return NewExpression([]expreduceapi.Ex{NewSymbol("System`Pattern"), NewSymbol(parts[0]), NewExpression([]expreduceapi.Ex{blankType})})
			} else if delim == "_" && parts[1] == "." {
				return NewExpression([]expreduceapi.Ex{NewSymbol("System`Optional"), NewExpression([]expreduceapi.Ex{NewSymbol("System`Pattern"), NewSymbol(parts[0]), NewExpression([]expreduceapi.Ex{blankType})})})
			}
			return NewExpression([]expreduceapi.Ex{NewSymbol("System`Pattern"), NewSymbol(parts[0]), NewExpression([]expreduceapi.Ex{blankType, NewSymbol(parts[1])})})
		}
	}
	return NewExpression([]expreduceapi.Ex{NewSymbol("System`Error"), NewString("Pattern parse error.")})
}

var unicodeRedefineMap = map[string]string{
	"π": "Pi",
}

func ParserTokenConv(tk wl.Token) expreduceapi.Ex {
	switch tk.Rune {
	case wl.IDENT:
		redefined, isRedefined := unicodeRedefineMap[tk.Val]
		if isRedefined {
			return NewSymbol(redefined)
		}
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
		return NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Slot"),
			NewInteger(tmpi),
		})

	default:
		log.Fatalf("System`UnParsedToken")
	}
	log.Fatalf("System`UnParsedToken")
	return nil
}

func ParserTagConv(tag *wl.Tag) expreduceapi.Ex {
	return ParserTokenConv(tag.Token)
}

func ParserExprListConv(l *wl.ExprList) (res []expreduceapi.Ex) {
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

// TODO: the following maps are tightly coupled to the parser generation in
// cznic/wl. Small modifications to wl might change all these values. Fix this
// situation.

var terminals = map[wl.ExpressionCase]bool{
	wl.ExpressionFloat:   true, // FLOAT
	wl.ExpressionIdent:   true, // IDENT
	wl.ExpressionInteger: true, // INT
	wl.ExpressionPattern: true, // PATTERN
	wl.ExpressionSlot:    true, // SLOT
	wl.ExpressionString:  true, // STRING
}

var unaryOps = map[wl.ExpressionCase]string{
	13:  "Not",
	115: "Factorial",
	117: "Function",
	15:  "Plus",
	23:  "Increment",
	25:  "Decrement",
	0:   "PreIncrement",
	1:   "PreDecrement",
}

var binaryOps = map[wl.ExpressionCase]string{
	wl.ExpressionAssign: "Set",
	39:                  "SetDelayed",
	33:                  "ReplaceRepeated",
	31:                  "ReplaceAll",
	27:                  "Rule",
	40:                  "RuleDelayed",
	134:                 "Power",
	130:                 "PatternTest",
	36:                  "Condition",
	52:                  "Apply",
	38:                  "Map",
	24:                  "AddTo",
	26:                  "SubtractFrom",
	78:                  "Element",
}

var fullyAssocOps = map[wl.ExpressionCase]string{
	125:               "CompoundExpression",
	wl.ExpressionAdd:  "Plus",
	wl.ExpressionMul:  "Times",
	wl.ExpressionEq:   "Equal",
	wl.ExpressionNe:   "Unequal",
	47:                "SameQ",
	45:                "UnsameQ",
	44:                "StringJoin",
	wl.ExpressionLt:   "Less",
	wl.ExpressionLe:   "LessEqual",
	wl.ExpressionGt:   "Greater",
	48:                "GreaterEqual",
	wl.ExpressionLOr:  "Or",
	wl.ExpressionLAnd: "And",
	121:               "Dot",
	wl.ExpressionOr:   "Alternatives",
	42:                "Span",
}

var headsToTokens = map[string]int{
	"System`Alternatives":       124,
	"System`And":                57347,
	"System`Apply":              57348,
	"System`CompoundExpression": 59,
	"System`Condition":          57359,
	"System`Dot":                46,
	"System`Equal":              57380,
	"System`Factorial":          33,
	"System`Function":           38,
	"System`Greater":            62,
	"System`GreaterEqual":       57388,
	"System`Less":               60,
	"System`LessEqual":          57399,
	"System`Map":                57401,
	"System`Not":                33,
	"System`Or":                 57412,
	"System`PatternTest":        63,
	"System`Plus":               43,
	"System`Power":              94,
	"System`ReplaceAll":         57428,
	"System`ReplaceRepeated":    57429,
	"System`Rule":               57433,
	"System`RuleDelayed":        57434,
	"System`SameQ":              57435,
	"System`Set":                61,
	"System`SetDelayed":         57436,
	"System`Span":               57439,
	"System`StringJoin":         57445,
	"System`Times":              42,
	"System`Unequal":            57462,
	"System`UnsameQ":            57464,
}

func ParserExprConv(expr *wl.Expression) expreduceapi.Ex {
	if _, ok := terminals[expr.Case]; ok {
		return ParserTokenConv(expr.Token)
	}
	if head, ok := binaryOps[expr.Case]; ok {
		return NewExpression([]expreduceapi.Ex{
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
		return NewExpression([]expreduceapi.Ex{
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
		return NewExpression([]expreduceapi.Ex{
			NewSymbol(head),
			e,
			ParserExprConv(expr.Expression2),
		})
	case wl.ExpressionMessageName:
		return NewExpression([]expreduceapi.Ex{
			NewSymbol("System`MessageName"),
			ParserTokenConv(expr.Token),
			NewString(ParserTagConv(expr.Tag).(*Symbol).Name),
		})
	case 132: // a[]
		return NewExpression([]expreduceapi.Ex{
			ParserExprConv(expr.Expression),
		})
	case 133: // a[b]
		e := NewExpression([]expreduceapi.Ex{
			ParserExprConv(expr.Expression),
		})
		e.AppendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 17: // {}
		return NewExpression([]expreduceapi.Ex{
			NewSymbol("System`List"),
		})
	case 18: // {a}
		e := NewExpression([]expreduceapi.Ex{
			NewSymbol("System`List"),
		})
		e.AppendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 14: // (a)
		// Internal`Parens are a placeholder to prevent fullyAssoc from
		// translating "(x==2) == (x==2)" to "x == 2 == (x == 2)"
		return NewExpression([]expreduceapi.Ex{
			NewSymbol("Internal`Parens"),
			ParserExprConv(expr.Expression),
		})
	case 54: // a[[b]]
		e := NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Part"),
			ParserExprConv(expr.Expression),
		})
		e.AppendExArray(ParserExprListConv(expr.ExprList))
		return e
	case 16:
		e := ParserExprConv(expr.Expression)
		if integer, isInteger := e.(*Integer); isInteger {
			return NewInteger(integer.Val.Neg(integer.Val))
		} else if flt, isFlt := e.(*Flt); isFlt {
			return NewReal(flt.Val.Neg(flt.Val))
		}
		return NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Times"),
			e,
			NewInteger(big.NewInt(-1)),
		})
	case 122:
		return NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Times"),
			ParserExprConv(expr.Expression),
			NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Power"),
				ParserExprConv(expr.Expression2),
				NewInteger(big.NewInt(-1)),
			}),
		})
	case 120:
		return fullyAssoc(
			"System`Plus",
			ParserExprConv(expr.Expression),
			NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Times"),
				ParserExprConv(expr.Expression2),
				NewInteger(big.NewInt(-1)),
			}),
		)
	case 32:
		return NewExpression([]expreduceapi.Ex{
			ParserExprConv(expr.Expression2),
			ParserExprConv(expr.Expression),
		})
	case 131:
		return NewExpression([]expreduceapi.Ex{
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
		})
	case 53:
		return NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Apply"),
			ParserExprConv(expr.Expression),
			ParserExprConv(expr.Expression2),
			E(S("List"), NewInt(1)),
		})
	case 35:
		set := ParserExprConv(expr.Expression2).(expreduceapi.ExpressionInterface)
		head := "System`TagSet"
		if _, isDelayed := HeadAssertion(set, "System`SetDelayed"); isDelayed {
			head = "System`TagSetDelayed"
		}
		e := NewExpression([]expreduceapi.Ex{
			NewSymbol(head),
			ParserExprConv(expr.Expression),
			set.GetParts()[1],
			set.GetParts()[2],
		})
		return e
	case 137:
		return NewExpression([]expreduceapi.Ex{
			NewExpression([]expreduceapi.Ex{
				NewSymbol("System`Derivative"),
				NewInt(1),
			}),
			ParserExprConv(expr.Expression),
		})
	case 11:
		return NewExpression([]expreduceapi.Ex{
			NewSymbol("System`Sqrt"),
			ParserExprConv(expr.Expression),
		})
	case wl.ExpressionInfo:
		return E(
			S("Information"),
			ParserTagConv(expr.Tag),
		)
	case wl.ExpressionInfoShort:
		return E(
			S("Information"),
			ParserTagConv(expr.Tag),
			E(S("Rule"), S("LongForm"), S("False")),
		)
	case 145:
		if expr.Token.Val == "%" {
			return E(
				S("Out"),
				E(S("Plus"), S("$Line"), NewInt(-1)),
			)
		} else if expr.Token.Val == "%%" {
			return E(
				S("Out"),
				E(S("Plus"), S("$Line"), NewInt(-2)),
			)
		}
	}
	log.Fatalf("System`UnParsed: %+v %+v %+v", expr.Token, expr.Case, expr)
	return nil
}

func InterpBuf(buf *bytes.Buffer, fn string, es expreduceapi.EvalStateInterface) (expreduceapi.Ex, error) {
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
			parsed = parens.GetParts()[1]
		}
	}
	// Remove inner parens
	removeParens(parsed)

	context := es.GetStringDef("System`$Context", "")
	contextPathEx := es.GetListDef("System`$ContextPath")
	ContextPath := []string{}
	for _, pathPart := range contextPathEx.GetParts()[1:] {
		ContextPath = append(ContextPath, pathPart.(*String).Val)
	}
	addContextAndDefine(parsed, context, ContextPath, es)
	return parsed, nil
}

func Interp(src string, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
	buf := bytes.NewBufferString(src)
	expr, err := InterpBuf(buf, "nofile", es)
	if err != nil {
		fmt.Printf("Syntax::sntx: %v.\n\n\n", err)
		return NewSymbol("System`Null")
	}
	return expr
}

func EvalInterp(src string, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
	return Interp(src, es).Eval(es)
}

func EvalInterpMany(doc string, fn string, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
	buf := bytes.NewBufferString(doc)
	var lastExpr expreduceapi.Ex = NewSymbol("System`Null")
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

func ReadList(doc string, fn string, es expreduceapi.EvalStateInterface) expreduceapi.Ex {
	buf := bytes.NewBufferString(doc)
	l := NewExpression([]expreduceapi.Ex{NewSymbol("System`List")})
	expr, err := InterpBuf(buf, fn, es)
	for err == nil {
		l.AppendEx(expr.Eval(es))
		expr, err = InterpBuf(buf, fn, es)
	}
	if !strings.HasSuffix(err.Error(), "unexpected EOF, invalid empty input") {
		fmt.Printf("Syntax::sntx: %v.\nWhile parsing: %v\n\n\n", err, buf.String()[:100])
	}
	return l
}

func EasyRun(src string, es expreduceapi.EvalStateInterface) string {
	context, ContextPath := ActualStringFormArgs(es)
	stringParams := expreduceapi.ToStringParams{
		Form:        "InputForm",
		Context:     context,
		ContextPath: ContextPath,
		Esi:         es,
	}
	return EvalInterp(src, es).StringForm(stringParams)
}
