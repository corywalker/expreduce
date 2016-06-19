// Copyright 2011 Bobby Powers. All rights reserved.
// Use of this source code is governed by the MIT
// license that can be found in the LICENSE file.

// based off of Appendix A from http://dinosaur.compilertools.net/yacc/

%{

package main

import (
	"fmt"
	"unicode"
	"gopkg.in/readline.v1"
	"github.com/corywalker/cas"
	"math/big"
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
%type <val> expr number

// same for terminals
%token <val> DIGIT LETTER

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
	|    number
	;

number	:    DIGIT
		{
			$$ = $1;
		}
	|    number DIGIT
		{ $$ = &cas.Flt{$1.(*cas.Flt).Val.Mul($1.(*cas.Flt).Val, big.NewFloat(10)).Add($1.(*cas.Flt).Val, $2.(*cas.Flt).Val)} }
	;

%%      /*  start  of  programs  */

type CalcLex struct {
	s string
	pos int
}


func (l *CalcLex) Lex(lval *CalcSymType) int {
	var c rune = ' '
	for c == ' ' {
		if l.pos == len(l.s) {
			return 0
		}
		c = rune(l.s[l.pos])
		l.pos += 1
	}

	if unicode.IsDigit(c) {
		lval.val = &cas.Flt{big.NewFloat(float64(int(c) - '0'))};
		return DIGIT
	} else if unicode.IsLower(c) {
		lval.val = &cas.Variable{string(c)}
		return LETTER
	}
	return int(c)
}

func (l *CalcLex) Error(s string) {
	fmt.Printf("syntax error: %s\n", s)
}

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
		CalcParse(&CalcLex{s: line + "\n"})
	}
}
