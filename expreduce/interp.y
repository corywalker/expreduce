%{

package expreduce

import (
	"math/big"
	"strings"
	/*"fmt"*/
)

%}

// fields inside this union end up as the fields in a structure known
// as ${PREFIX}SymType, of which a reference is passed to the lexer.
%union{
	val Ex
	valSeq []Ex
}

// any non-terminal which returns a value needs a type, which is
// really a field name in the above union struct
%type <val> expr
%type <val> term
%type <val> factor
%type <valSeq> exprseq

// same for terminals
%token <val> FLOAT INTEGER STRING LPARSYM RPARSYM COMMASYM SEMISYM LBRACKETSYM RBRACKETSYM LCURLYSYM RCURLYSYM NAME PATTERN

/*Adding some of the tokens above to this precedence list can decrease the*/
/*number of conflicts*/
%left SEMISYM /* TODO: fully associative, handles a Null at the end */
%right FUNCTIONSYM
%right SETDELAYEDSYM
%right SETSYM
%left POSTFIXSYM
%left REPLACEREPSYM
%left REPLACEALLSYM
%right RULEDELAYEDSYM
%right RULESYM
%left CONDITIONSYM
%left COLONSYM
%left ALTSYM
%left REPEATEDSYM
%left REPEATEDNULLSYM
%left ORSYM
%left ANDSYM
%left UNSAMESYM
%left SAMESYM
%left LESSEQUALSYM
%left LESSSYM
%left GREATEREQUALSYM
%left GREATERSYM
%left UNEQUALSYM
%left EQUALSYM
%left SPANSYM
%left PLUSSYM /* Plus and minus seem to be reversed according to the table. Investigate this. */
%left MINUSSYM
%left MULTSYM
%left DIVSYM /* does not need to be fully associative */
%left DOTSYM
%right EXPSYM
%left STRINGJOINSYM
%left EXCLAMATIONSYM
%right APPLYSYM
%right MAPSYM
%right FUNCAPPSYM
%left PATTESTSYM
%left GETSYM
%nonassoc PATTERN
%nonassoc SLOTSYM
%left MESSAGENAMESYM /* This might as well be part of the symbol. Use a very
high precedence. */
%nonassoc STRING
%nonassoc NAME
%nonassoc FLOAT
%nonassoc INTEGER

%nonassoc LBRACKETSYM RBRACKETSYM
%nonassoc LCURLYSYM RCURLYSYM
%nonassoc LPARSYM RPARSYM

%nonassoc COMMASYM


%%

stmt	:
	expr {yylex.(*Calclexer).expr = $1}
	| error {yylex.(*Calclexer).expr = &Symbol{"System`Null"}}
	;

expr	:
	/*|    INTEGER NAME*/
		/*{ $$  =  NewExpression([]Ex{&Symbol{"System`Times"}, $1, $2}) }*/
	/*Lower precedence than times*/
	expr SEMISYM expr
		{ $$  =  fullyAssoc("System`CompoundExpression", $1, $3) }
	|    expr SEMISYM
		{ $$  =  fullyAssoc("System`CompoundExpression", $1, &Symbol{"System`Null"}) }
	|    expr SETSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Set"}, $1, $3}) }
	|    expr SETDELAYEDSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"System`SetDelayed"}, $1, $3}) }
	|    EXCLAMATIONSYM expr %prec ANDSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Not"}, $2}) }
	|    expr FUNCTIONSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Function"}, $1}) }
	|    expr PLUSSYM expr
		{ $$  =  fullyAssoc("System`Plus", $1, $3) }
	|    expr MINUSSYM expr
		{ $$  =  fullyAssoc("System`Plus", $1, NewExpression([]Ex{&Symbol{"System`Times"}, $3, &Integer{big.NewInt(-1)}})) }

	/*Don't know about the precedence here... */
	|    LCURLYSYM exprseq RCURLYSYM
		{
			ex := NewEmptyExpression()
			ex.Parts = []Ex{&Symbol{"System`List"}}
			ex.Parts = append(ex.Parts, $2...)
			$$ = ex
		}


	|    expr POSTFIXSYM expr
		{ $$  =  NewExpression([]Ex{$3, $1}) }
	|    expr REPLACEREPSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"System`ReplaceRepeated"}, $1, $3}) }
	|    expr REPLACEALLSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"System`ReplaceAll"}, $1, $3}) }
	|    expr RULEDELAYEDSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"System`RuleDelayed"}, $1, $3}) }
	|    expr RULESYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Rule"}, $1, $3}) }
	|    expr CONDITIONSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Condition"}, $1, $3}) }
	|    PATTERN COLONSYM INTEGER
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Optional"}, $1, $3}) }
	|    PATTERN COLONSYM NAME
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Optional"}, $1, $3}) }
	|    NAME COLONSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Pattern"}, $1, $3}) }
	|    expr ALTSYM expr
		{ $$  =  fullyAssoc("System`Alternatives", $1, $3) }
	|    expr REPEATEDSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Repeated"}, $1}) }
	|    expr REPEATEDNULLSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"System`RepeatedNull"}, $1}) }
	|    expr ORSYM expr
		{ $$  =  fullyAssoc("System`Or", $1, $3) }
	|    expr ANDSYM expr
		{ $$  =  fullyAssoc("System`And", $1, $3) }
	|    expr UNSAMESYM expr
		{ $$  =  fullyAssoc("System`UnsameQ", $1, $3) }
	|    expr SAMESYM expr
		{ $$  =  fullyAssoc("System`SameQ", $1, $3) }
	|    expr LESSSYM expr
		{ $$  =  fullyAssoc("System`Less", $1, $3) }
	|    expr LESSEQUALSYM expr
		{ $$  =  fullyAssoc("System`LessEqual", $1, $3) }
	|    expr GREATERSYM expr
		{ $$  =  fullyAssoc("System`Greater", $1, $3) }
	|    expr GREATEREQUALSYM expr
		{ $$  =  fullyAssoc("System`GreaterEqual", $1, $3) }
	|    expr EQUALSYM expr
		{ $$  =  fullyAssoc("System`Equal", $1, $3) }
	|    expr UNEQUALSYM expr
		{ $$  =  fullyAssoc("System`Unequal", $1, $3) }
	|    expr SPANSYM expr
		{ $$  =  fullyAssoc("System`Span", $1, $3) }
	|    MINUSSYM expr
		{
			if integer, isInteger := $2.(*Integer); isInteger {
				$$  =  &Integer{integer.Val.Neg(integer.Val)}
			} else if flt, isFlt := $2.(*Flt); isFlt {
				$$  =  &Flt{flt.Val.Neg(flt.Val)}
			} else {
				$$  =  NewExpression([]Ex{&Symbol{"System`Times"}, $2, &Integer{big.NewInt(-1)}})
			}
		}
	|    expr MULTSYM expr
		{ $$  =  fullyAssoc("System`Times", $1, $3) }
	|    expr DIVSYM expr
		{ $$  =  NewExpression([]Ex{
		           &Symbol{"System`Times"},
				   $1,
				   NewExpression([]Ex{
				     &Symbol{"System`Power"},
				     $3,
					 &Integer{big.NewInt(-1)},
				   }),
			     })
		}
	| factor
	;

factor  :
	term
	/*Same precedence!!*/
		/*I have foundthe source of all rr conflicts:*/
	|    factor term
		{ $$  =  fullyAssoc("System`Times", $1, $2) }
	;



	/*Higher precedence than multiplication*/
term	:

	/*from way up*/
	term LBRACKETSYM LBRACKETSYM exprseq RBRACKETSYM RBRACKETSYM
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{&Symbol{"System`Part"}, $1}, $4...)
			$$ = ex
		}
	|    term LBRACKETSYM exprseq RBRACKETSYM
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{$1}, $3...)
			$$ = ex
		}
	|    term DOTSYM term
		{ $$  =  fullyAssoc("System`Dot", $1, $3) }
	|    term EXPSYM term
		{ $$  =  NewExpression([]Ex{
		           &Symbol{"System`Power"},
				   $1,
				   $3,
				 })
		}
	|    term FUNCAPPSYM term
		{ $$  =  NewExpression([]Ex{$1, $3}) }
	|    term PATTESTSYM term
		{ $$  =  NewExpression([]Ex{&Symbol{"System`PatternTest"}, $1, $3}) }
	|    term APPLYSYM term
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Apply"}, $1, $3}) }
	|    term MAPSYM term
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Map"}, $1, $3}) }

	/*in same order*/
	|    term EXCLAMATIONSYM %prec APPLYSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Factorial"}, $1}) }
	|    SLOTSYM %prec PLUSSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Slot"}, &Integer{big.NewInt(1)}}) }
	|    SLOTSYM INTEGER %prec DIVSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Slot"}, $2}) }
	|    GETSYM term
		{ $$  =  NewExpression([]Ex{&Symbol{"System`Get"}, $2}) }
	|    term MESSAGENAMESYM term
		{
			if sym, isSym := $3.(*Symbol); isSym {
				$$  =  fullyAssoc("System`MessageName", $1, &String{sym.Name})
			} else {
				$$  =  fullyAssoc("System`MessageName", $1, $3)
			}
		}
	|    term STRINGJOINSYM term
		{ $$  =  fullyAssoc("System`StringJoin", $1, $3) }
	|    PATTERN
		{ $$  =  $1 }
	|    NAME
		{ $$  =  $1 }
	|    STRING
		{ $$  =  $1 }
	|    FLOAT
		{ $$  =  $1 }
	|    INTEGER
		{ $$  =  $1 }
	 | LPARSYM term RPARSYM
		/*This sentinel expression could be removed by attaching metadata to*/
		/*either the val object or the Expression object.*/
		{ $$  =  NewExpression([]Ex{&Symbol{"Internal`Parens"}, $2}) }
	;
exprseq:
	/* empty */
		{ $$ = []Ex{} }
	| expr
	    { $$ = append($$, $1) }
	| exprseq COMMASYM expr
	    { $$ = append($$, $3) }
	| exprseq COMMASYM
	    { $$ = append($$, &Symbol{"System`Null"}) }
	;

%%      /*  start  of  programs  */

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

func Interp(line string, es *EvalState) Ex {
	// If we want the ability to parse multiple statements without the need
	// for them to be separated by newlines, perhaps we should start with the
	// first line and evaluate it. If it produces an error, then we should
	// evaluate the first and second lines together, and so on. Once the
	// lines finally produce a valid expression, we can add that parsed
	// expression to the list of statements. Actually, we should read until the
	// lines no longer produce a valid expression or until we reach EOF.
	/*fmt.Println(line)*/
	lex := newLexer(line + "\n")
	CalcParse(lex)

	parsed := lex.expr
	/*fmt.Printf("%v\n", parsed)*/
	// This can happen when we only enter a comment.
	if parsed == nil {
		return &Symbol{"System`Null"}
	}
	// Remove outer parens
	parens, isParens := NewEmptyExpression(), true
	for isParens {
		parens, isParens = HeadAssertion(parsed, "Internal`Parens")
		if isParens {
			parsed = parens.Parts[1]
		}
	}
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

func EvalInterp(line string, es *EvalState) Ex {
	return Interp(line, es).Eval(es)
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

func EasyRun(line string, es *EvalState) string {
	context, contextPath := ActualStringFormArgs(es)
	return EvalInterp(line, es).StringForm("InputForm", context, contextPath)
}
