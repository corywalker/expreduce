%{

package expreduce

import (
	"math/big"
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
%type <valSeq> exprseq

// same for terminals
%token <val> FLOAT INTEGER STRING LPARSYM RPARSYM COMMASYM SEMISYM LBRACKETSYM RBRACKETSYM LCURLYSYM RCURLYSYM REPLACEREPSYM REPLACEALLSYM CONDITIONSYM PLUSSYM MINUSSYM MULTSYM DIVSYM EXPSYM RULESYM RULEDELAYEDSYM POSTFIXSYM FUNCAPPSYM APPLYSYM MAPSYM PATTESTSYM ALTSYM SAMESYM EQUALSYM UNEQUALSYM SETSYM SETDELAYEDSYM SLOTSYM NAME PATTERN MESSAGENAMESYM STRINGJOINSYM EXCLAMATIONSYM FUNCTIONSYM SPANSYM LESSEQUALSYM LESSSYM GREATEREQUALSYM GREATERSYM ORSYM ANDSYM COLONSYM GETSYM UNSAMESYM

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
%nonassoc EXCLAMATIONSYM
%right APPLYSYM
%right MAPSYN
%right FUNCAPPSYM
%nonassoc PATTESTSYM
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

list	: /* empty */
	| list expr {Calcrcvr.lval.val = $2}
	| list error {Calcrcvr.lval.val = &Symbol{"Null"}}
	;

expr	:    LPARSYM expr RPARSYM
		/*This sentinel expression could be removed by attaching metadata to*/
		/*either the val object or the Expression object.*/
		{ $$  =  NewExpression([]Ex{&Symbol{"Internal`Parens"}, $2}) }
	/*|    INTEGER NAME*/
		/*{ $$  =  NewExpression([]Ex{&Symbol{"Times"}, $1, $2}) }*/
	|    expr SEMISYM expr
		{ $$  =  fullyAssoc("CompoundExpression", $1, $3) }
	|    expr SEMISYM
		{ $$  =  fullyAssoc("CompoundExpression", $1, &Symbol{"Null"}) }
	|    expr EXCLAMATIONSYM expr
		{ $$  =  NewExpression([]Ex{
		             &Symbol{"Times"},
		             NewExpression([]Ex{
			             &Symbol{"Factorial"},
						 $1,
					 }),
					 $3,
			      })
		}
	|    expr EXCLAMATIONSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"Factorial"}, $1}) }
	|    EXCLAMATIONSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"Not"}, $2}) }
	|    expr FUNCTIONSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"Function"}, $1}) }
	|    expr LBRACKETSYM LBRACKETSYM exprseq RBRACKETSYM RBRACKETSYM
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{&Symbol{"Part"}, $1}, $4...)
			$$ = ex
		}
	|    expr LBRACKETSYM exprseq RBRACKETSYM
		{
			ex := NewEmptyExpression()
			ex.Parts = append([]Ex{$1}, $3...)
			$$ = ex
		}
	|    LCURLYSYM exprseq RCURLYSYM
		{
			ex := NewEmptyExpression()
			ex.Parts = []Ex{&Symbol{"List"}}
			ex.Parts = append(ex.Parts, $2...)
			$$ = ex
		}
	|    expr PLUSSYM expr
		{ $$  =  fullyAssoc("Plus", $1, $3) }
	|    expr MINUSSYM expr
		{ $$  =  fullyAssoc("Plus", $1, NewExpression([]Ex{&Symbol{"Times"}, $3, &Integer{big.NewInt(-1)}})) }
	|    expr MULTSYM expr
		{ $$  =  fullyAssoc("Times", $1, $3) }
	|    expr expr %prec MULTSYM
		{ $$  =  fullyAssoc("Times", $1, $2) }
	|    expr DIVSYM expr
		{ $$  =  NewExpression([]Ex{
		           &Symbol{"Times"},
				   $1,
				   NewExpression([]Ex{
				     &Symbol{"Power"},
				     $3,
					 &Integer{big.NewInt(-1)},
				   }),
			     })
		}
	|    expr EXPSYM expr
		{ $$  =  NewExpression([]Ex{
		           &Symbol{"Power"},
				   $1,
				   $3,
				 })
		}
	|    expr POSTFIXSYM expr
		{ $$  =  NewExpression([]Ex{$3, $1}) }
	|    expr FUNCAPPSYM expr
		{ $$  =  NewExpression([]Ex{$1, $3}) }
	|    expr PATTESTSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"PatternTest"}, $1, $3}) }
	|    expr ALTSYM expr
		{ $$  =  fullyAssoc("Alternatives", $1, $3) }
	|    expr REPEATEDSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"Repeated"}, $1}) }
	|    expr REPEATEDNULLSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"RepeatedNull"}, $1}) }
	|    expr APPLYSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"Apply"}, $1, $3}) }
	|    expr MAPSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"Map"}, $1, $3}) }
	|    expr RULESYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"Rule"}, $1, $3}) }
	|    expr RULEDELAYEDSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"RuleDelayed"}, $1, $3}) }
	|    expr REPLACEREPSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"ReplaceRepeated"}, $1, $3}) }
	|    expr REPLACEALLSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"ReplaceAll"}, $1, $3}) }
	|    expr CONDITIONSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"Condition"}, $1, $3}) }
	|    PATTERN COLONSYM INTEGER
		{ $$  =  NewExpression([]Ex{&Symbol{"Optional"}, $1, $3}) }
	|    PATTERN COLONSYM NAME
		{ $$  =  NewExpression([]Ex{&Symbol{"Optional"}, $1, $3}) }
	|    NAME COLONSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"Pattern"}, $1, $3}) }
	|    expr SETSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"Set"}, $1, $3}) }
	|    expr SETDELAYEDSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"SetDelayed"}, $1, $3}) }
	|    expr SAMESYM expr
		{ $$  =  fullyAssoc("SameQ", $1, $3) }
	|    expr UNSAMESYM expr
		{ $$  =  fullyAssoc("UnsameQ", $1, $3) }
	|    expr EQUALSYM expr
		{ $$  =  fullyAssoc("Equal", $1, $3) }
	|    expr UNEQUALSYM expr
		{ $$  =  fullyAssoc("Unequal", $1, $3) }
	|    expr LESSSYM expr
		{ $$  =  fullyAssoc("Less", $1, $3) }
	|    expr LESSEQUALSYM expr
		{ $$  =  fullyAssoc("LessEqual", $1, $3) }
	|    expr GREATERSYM expr
		{ $$  =  fullyAssoc("Greater", $1, $3) }
	|    expr GREATEREQUALSYM expr
		{ $$  =  fullyAssoc("GreaterEqual", $1, $3) }
	|    expr SPANSYM expr
		{ $$  =  fullyAssoc("Span", $1, $3) }
	|    expr DOTSYM expr
		{ $$  =  fullyAssoc("Dot", $1, $3) }
	|    expr ANDSYM expr
		{ $$  =  fullyAssoc("And", $1, $3) }
	|    expr ORSYM expr
		{ $$  =  fullyAssoc("Or", $1, $3) }
	|    MINUSSYM expr
		{
			if integer, isInteger := $2.(*Integer); isInteger {
				$$  =  &Integer{integer.Val.Neg(integer.Val)}
			} else if flt, isFlt := $2.(*Flt); isFlt {
				$$  =  &Flt{flt.Val.Neg(flt.Val)}
			} else {
				$$  =  NewExpression([]Ex{&Symbol{"Times"}, $2, &Integer{big.NewInt(-1)}})
			}
		}
	|    SLOTSYM
		{ $$  =  NewExpression([]Ex{&Symbol{"Slot"}, &Integer{big.NewInt(1)}}) }
	|    SLOTSYM INTEGER
		{ $$  =  NewExpression([]Ex{&Symbol{"Slot"}, $2}) }
	|    GETSYM expr
		{ $$  =  NewExpression([]Ex{&Symbol{"Get"}, $2}) }
	|    expr MESSAGENAMESYM expr
		{
			if sym, isSym := $3.(*Symbol); isSym {
				$$  =  fullyAssoc("MessageName", $1, &String{sym.Name})
			} else {
				$$  =  fullyAssoc("MessageName", $1, $3)
			}
		}
	|    expr STRINGJOINSYM expr
		{ $$  =  fullyAssoc("StringJoin", $1, $3) }
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
	;
exprseq:
	/* empty */
		{ $$ = []Ex{} }
	| expr
	    { $$ = append($$, $1) }
	| exprseq COMMASYM expr
	    { $$ = append($$, $3) }
	| exprseq COMMASYM
	    { $$ = append($$, &Symbol{"Null"}) }
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

func removeParens(ex Ex) {
	expr, isExpr := ex.(*Expression)
	if isExpr {
		for i := range expr.Parts {
			parens, isParens := HeadAssertion(expr.Parts[i], "Internal`Parens")
			if isParens {
				expr.Parts[i] = parens.Parts[1]
			}
			removeParens(expr.Parts[i])
		}
	}
	return
}

func Interp(line string) Ex {
	// If we want the ability to parse multiple statements without the need
	// for them to be separated by newlines, perhaps we should start with the
	// first line and evaluate it. If it produces an error, then we should
	// evaluate the first and second lines together, and so on. Once the
	// lines finally produce a valid expression, we can add that parsed
	// expression to the list of statements. Actually, we should read until the
	// lines no longer produce a valid expression or until we reach EOF.
	lex := newLexer(line + "\n")
	var parser CalcParser = CalcNewParser()
	parser.Parse(lex)

	parsed := parser.(*CalcParserImpl).lval.val
	// Remove outer parens
	parens, isParens := NewEmptyExpression(), true
	for isParens {
		parens, isParens = HeadAssertion(parsed, "Internal`Parens")
		if isParens {
			parsed = parens.Parts[1]
		}
	}
	removeParens(parsed)
	return parsed
}

func EvalInterp(line string, es *EvalState) Ex {
	return Interp(line).Eval(es)
}

func EasyRun(line string, es *EvalState) string {
	return EvalInterp(line, es).StringForm("InputForm")
}
