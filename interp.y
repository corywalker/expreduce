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
}

// any non-terminal which returns a value needs a type, which is
// really a field name in the above union struct
%type <val> expr

// same for terminals
%token <val> FLOAT INTEGER LPARSYM RPARSYM COMMASYM LBRACKETSYM RBRACKETSYM REPLACEREPSYM REPLACESYM PLUSSYM MINUSSYM MULTSYM DIVSYM EXPSYM RULESYM SAMESYM EQUALSYM SETSYM SETDELAYEDSYM NAME PATTERN

%left REPLACEREPSYM REPLACESYM
%left SAMESYM EQUALSYM
%left RULESYM
%left PLUSSYM MINUSSYM
%left MULTSYM DIVSYM
%left EXPSYM

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
	|    expr LBRACKETSYM RBRACKETSYM
		{
			ex := &Expression{}
			ex.Parts = []Ex{$1}
			$$ = ex
		}
	|    expr LBRACKETSYM expr RBRACKETSYM
		{
			ex := &Expression{}
			ex.Parts = []Ex{$1, $3}
			$$ = ex
		}
	|    expr LBRACKETSYM expr COMMASYM expr RBRACKETSYM
		{
			ex := &Expression{}
			ex.Parts = []Ex{$1, $3, $5}
			$$ = ex
		}
	|    expr LBRACKETSYM expr COMMASYM expr COMMASYM expr RBRACKETSYM
		{
			ex := &Expression{}
			ex.Parts = []Ex{$1, $3, $5, $7}
			$$ = ex
		}
	|    expr LBRACKETSYM expr COMMASYM expr COMMASYM expr COMMASYM expr RBRACKETSYM
		{
			fc := &Expression{}
			fc.Parts = []Ex{$1, $3, $5, $7, $9}
			$$ = fc
		}
	|    expr LBRACKETSYM expr COMMASYM expr COMMASYM expr COMMASYM expr COMMASYM expr RBRACKETSYM
		{
			fc := &Expression{}
			fc.Parts = []Ex{$1, $3, $5, $7, $9, $11}
			$$ = fc
		}
	|    expr PLUSSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Plus"}, $1, $3}} }
	|    expr MINUSSYM expr
		{ $$  =  &Expression{ []Ex{&Symbol{"Plus"}, $1, &Expression{[]Ex{&Symbol{"Times"}, $3, &Integer{big.NewInt(-1)}}} } } }
	|    expr MULTSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Times"}, $1, $3}} }
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
	|    expr RULESYM expr
		{ $$  =  &Rule{$1, $3} }
	|    expr REPLACEREPSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"ReplaceRepeated"}, $1, $3}} }
	|    expr REPLACESYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Replace"}, $1, $3}} }
	|    expr SETSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Set"}, $1, $3}} }
	|    expr SETDELAYEDSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"SetDelayed"}, $1, $3}} }
	|    expr SAMESYM expr
		{ $$  =  &SameQ{$1, $3} }
	|    expr EQUALSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Equal"}, $1, $3}} }
	|    MINUSSYM expr
		{ $$  =  &Expression{[]Ex{&Symbol{"Times"}, $2, &Integer{big.NewInt(-1)}}} }
	|    PATTERN
		{ $$  =  $1 }
	|    NAME
		{ $$  =  $1 }
	|    FLOAT
		{ $$  =  $1 }
	|    INTEGER
		{ $$  =  $1 }
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
	return EvalInterp(line, es).ToString()
}
