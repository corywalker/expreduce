%{

package cas

import (
	"math/big"
)

%}

// fields inside this union end up as the fields in a structure known
// as ${PREFIX}SymType, of which a reference is passed to the lexer.
%union{
	val Ex
	valSeq []Ex
	compExpr []Ex
}

// any non-terminal which returns a value needs a type, which is
// really a field name in the above union struct
%type <val> expr
%type <valSeq> exprseq
%type <compExpr> compexpr

// same for terminals
%token <val> FLOAT INTEGER STRING LPARSYM RPARSYM COMMASYM SEMISYM LBRACKETSYM RBRACKETSYM LCURLYSYM RCURLYSYM REPLACEREPSYM REPLACEALLSYM CONDITIONSYM PLUSSYM MINUSSYM MULTSYM DIVSYM EXPSYM RULESYM RULEDELAYEDSYM POSTFIXSYM FUNCAPPSYM APPLYSYM MAPSYM PATTESTSYM ALTSYM SAMESYM EQUALSYM SETSYM SETDELAYEDSYM SLOTSYM NAME PATTERN MESSAGENAMESYM STRINGJOINSYM

/*Adding some of the tokens above to this precedence list can decrease the*/
/*number of conflicts*/
%left POSTFIXSYM APPLYSYM MAPSYM
%left SETSYM SETDELAYEDSYM
%left REPLACEREPSYM REPLACEALLSYM
%left RULESYM RULEDELAYEDSYM
%left CONDITIONSYM ALTSYM
%left SAMESYM EQUALSYM
%left PLUSSYM MINUSSYM
%left MULTSYM DIVSYM
%left EXPSYM
%left STRINGJOINSYM
%left MESSAGENAMESYM /* This might as well be part of the symbol. Use a very
high precedence. */

%right FUNCAPPSYM

%%

list	: /* empty */
	| list stat '\n'
	;

stat	:    expr
		{
			Calcrcvr.lval.val = $1
		}
	;

expr	:    LPARSYM expr RPARSYM
		{ $$  =  $2 }
	|    LPARSYM compexpr RPARSYM
		{
			ex := &Expression{}
			ex.Parts = []Ex{&Symbol{"CompoundExpression"}}
			ex.Parts = append(ex.Parts, $2...)
			$$ = ex
		}
	/*|    INTEGER NAME*/
		/*{ $$  =  &Expression{[]Ex{&Symbol{"Times"}, $1, $2}} }*/
	/*|    expr SEMISYM expr*/
		/*{ $$  =  &Expression{[]Ex{&Symbol{"CompoundExpression"}, $1, $3}} }*/
	|    expr LBRACKETSYM exprseq RBRACKETSYM
		{
			ex := &Expression{}
			ex.Parts = append([]Ex{$1}, $3...)
			$$ = ex
		}
	|    LCURLYSYM exprseq RCURLYSYM
		{
			ex := &Expression{}
			ex.Parts = []Ex{&Symbol{"List"}}
			ex.Parts = append(ex.Parts, $2...)
			$$ = ex
		}
	|    expr PLUSSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Plus"}, $1, $3}} }
	|    expr MINUSSYM expr
		{ $$  =  &Expression{ []Ex{&Symbol{"Plus"}, $1, &Expression{[]Ex{&Symbol{"Times"}, $3, &Integer{big.NewInt(-1)}}} } } }
	|    expr MULTSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Times"}, $1, $3}} }
	|    expr expr %prec MULTSYM
		{ $$  =  &Expression{[]Ex{&Symbol{"Times"}, $1, $2}} }
	|    expr DIVSYM expr
		{ $$  =  &Expression{[]Ex{
		           &Symbol{"Times"},
				   $1,
				   &Expression{[]Ex{
				     &Symbol{"Power"},
				     $3,
					 &Integer{big.NewInt(-1)},
				   }},
			     }}
		}
	|    expr EXPSYM expr
		{ $$  =  &Expression{[]Ex{
		           &Symbol{"Power"},
				   $1,
				   $3,
				 }}
		}
	|    expr POSTFIXSYM expr
		{ $$  =  &Expression{[]Ex{$3, $1}} }
	|    expr FUNCAPPSYM expr
		{ $$  =  &Expression{[]Ex{$1, $3}} }
	|    expr PATTESTSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"PatternTest"}, $1, $3}} }
	|    expr ALTSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Alternatives"}, $1, $3}} }
	|    expr APPLYSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Apply"}, $1, $3}} }
	|    expr MAPSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Map"}, $1, $3}} }
	|    expr RULESYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Rule"}, $1, $3}} }
	|    expr RULEDELAYEDSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"RuleDelayed"}, $1, $3}} }
	|    expr REPLACEREPSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"ReplaceRepeated"}, $1, $3}} }
	|    expr REPLACEALLSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"ReplaceAll"}, $1, $3}} }
	|    expr CONDITIONSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Condition"}, $1, $3}} }
	|    expr SETSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Set"}, $1, $3}} }
	|    expr SETDELAYEDSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"SetDelayed"}, $1, $3}} }
	|    expr SAMESYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"SameQ"}, $1, $3}} }
	|    expr EQUALSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Equal"}, $1, $3}} }
	|    MINUSSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Times"}, $2, &Integer{big.NewInt(-1)}}} }
	|    SLOTSYM
		{ $$  =  &Expression{[]Ex{&Symbol{"Slot"}, &Integer{big.NewInt(1)}}} }
	|    SLOTSYM INTEGER
		{ $$  =  &Expression{[]Ex{&Symbol{"Slot"}, $2}} }
	|    expr MESSAGENAMESYM expr
		{
			if sym, isSym := $3.(*Symbol); isSym {
				$$  =  &Expression{[]Ex{&Symbol{"MessageName"}, $1, &String{sym.Name}}}
			} else {
				$$  =  &Expression{[]Ex{&Symbol{"MessageName"}, $1, $3}}
			}
		}
	|    expr STRINGJOINSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"StringJoin"}, $1, $3}} }
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
compexpr:
	/* empty */
		{ $$ = []Ex{} }
	| expr
	    { $$ = append($$, $1) }
	| compexpr SEMISYM expr
	    { $$ = append($$, $3) }
	| compexpr SEMISYM
	    { $$ = append($$, &Symbol{"Null"}) }
	;

%%      /*  start  of  programs  */

func Interp(line string) Ex {
	lex := newLexer(line + "\n")
	var parser CalcParser = CalcNewParser()
	parser.Parse(lex)

	return parser.(*CalcParserImpl).lval.val
}

func EvalInterp(line string, es *EvalState) Ex {
	return Interp(line).Eval(es)
}

func EasyRun(line string, es *EvalState) string {
	return EvalInterp(line, es).StringForm("InputForm")
}
