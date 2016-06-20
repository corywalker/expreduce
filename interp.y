%{

package cas

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
%token <val> FLOAT INTEGER LPARSYM RPARSYM PLUSSYM MULTSYM EXPSYM EQUALSYM NAME

%left EQUALSYM
%left PLUSSYM
%left MULTSYM
%left EXPSYM

%%

list	: /* empty */
	| list stat '\n'
	;

stat	:    expr
		{
			/*fmt.Printf( "In:  %s\n", $1.ToString() );*/
			/*fmt.Printf( "Out: %s\n", $1.Eval().ToString() );*/
			/*return $1*/
			Calcrcvr.lval.val = $1
		}
	;

expr	:    LPARSYM expr RPARSYM
		{ $$  =  $2 }
	|    expr PLUSSYM expr
		{ $$  =  &Add{[]Ex{$1, $3}} }
	|    expr MULTSYM expr
		{ $$  =  &Mul{[]Ex{$1, $3}} }
	|    expr EXPSYM expr
		{ $$  =  &Exponent{$1, $3} }
	|    expr EQUALSYM expr
		{ $$  =  &EqualQ{$1, $3} }
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

func EvalInterp(line string) Ex {
	return Interp(line).Eval()
}
