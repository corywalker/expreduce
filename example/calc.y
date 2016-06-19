%{

package main

import (
	"fmt"
	"gopkg.in/readline.v1"
	"github.com/corywalker/cas"
)

// TODO: Add boolean literals

%}

// fields inside this union end up as the fields in a structure known
// as ${PREFIX}SymType, of which a reference is passed to the lexer.
%union{
	val cas.Ex
}

// any non-terminal which returns a value needs a type, which is
// really a field name in the above union struct
%type <val> expr

// same for terminals
%token <val> FLOAT INTEGER LETTER

%left '='
%left '+'
%left '*'
%left '^'

%%

list	: /* empty */
	| list stat '\n'
	;

stat	:    expr
		{
			fmt.Printf( "In:  %s\n", $1.ToString() );
			fmt.Printf( "Out: %s\n", $1.Eval().ToString() );
		}
	;

expr	:    '(' expr ')'
		{ $$  =  $2 }
	|    expr '+' expr
		{ $$  =  &cas.Add{[]cas.Ex{$1, $3}} }
	|    expr '*' expr
		{ $$  =  &cas.Mul{[]cas.Ex{$1, $3}} }
	|    expr '^' expr
		{ $$  =  &cas.Exponent{$1, $3} }
	|    expr '=' expr
		{ $$  =  &cas.EqualQ{$1, $3} }
	|    LETTER
		{ $$  =  $1 }
	|    FLOAT
		{ $$  =  $1 }
	|    INTEGER
		{ $$  =  $1 }
	;

%%      /*  start  of  programs  */

func main() {
	rl, err := readline.NewEx(&readline.Config{
		Prompt: "> ",
		HistoryFile: "/tmp/readline.tmp",
	})
	if err != nil {
		panic(err)
	}
	defer rl.Close()

	for {
		line, err := rl.Readline()
		if err != nil { // io.EOF, readline.ErrInterrupt
			break
		}
		CalcParse(newLexer(line + "\n"))
	}
}
