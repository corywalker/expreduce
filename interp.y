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
%token <val> FLOAT INTEGER LPARSYM RPARSYM COMMASYM LBRACKETSYM RBRACKETSYM PLUSSYM MINUSSYM MULTSYM DIVSYM EXPSYM SAMESYM EQUALSYM SETSYM SETDELAYEDSYM NAME

%left SAMESYM EQUALSYM
%left PLUSSYM MINUSSYM
%left MULTSYM DIVSYM
%left EXPSYM
%left UMINUS

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
	|    NAME LBRACKETSYM RBRACKETSYM
		{
			fc := &Function{}
			fc.Name = $1.(*Symbol).Name
			$$ = fc
		}
	|    NAME LBRACKETSYM expr RBRACKETSYM
		{
			fc := &Function{}
			fc.Name = $1.(*Symbol).Name
			fc.Arguments = []Ex{$3}
			$$ = fc
		}
	|    NAME LBRACKETSYM expr COMMASYM expr RBRACKETSYM
		{
			fc := &Function{}
			fc.Name = $1.(*Symbol).Name
			fc.Arguments = []Ex{$3, $5}
			$$ = fc
		}
	|    NAME LBRACKETSYM expr COMMASYM expr COMMASYM expr RBRACKETSYM
		{
			fc := &Function{}
			fc.Name = $1.(*Symbol).Name
			fc.Arguments = []Ex{$3, $5, $7}
			$$ = fc
		}
	|    expr PLUSSYM expr
		{ $$  =  &Plus{[]Ex{$1, $3}} }
	|    expr MINUSSYM expr
		{ $$  =  &Plus{ []Ex{$1, &Times{[]Ex{$3, &Integer{big.NewInt(-1)}}} } } }
	|    expr MULTSYM expr
		{ $$  =  &Times{[]Ex{$1, $3}} }
	|    expr DIVSYM expr
		{ $$  =  &Times{ []Ex{$1, &Power{$3, &Integer{big.NewInt(-1)}} } } }
	|    expr EXPSYM expr
		{ $$  =  &Power{$1, $3} }
	|    expr SETSYM expr
		{ $$  =  &Set{$1, $3} }
	|    expr SETDELAYEDSYM expr
		{ $$  =  &SetDelayed{$1, $3} }
	|    expr SAMESYM expr
		{ $$  =  &SameQ{$1, $3} }
	|    expr EQUALSYM expr
		{ $$  =  &Equal{$1, $3} }
	|    MINUSSYM expr
		{ $$  =  &Times{[]Ex{$2, &Integer{big.NewInt(-1)}}} }
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
