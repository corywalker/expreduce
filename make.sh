#!/bin/bash

rm calc.go y.output y.go lex.go
go tool yacc -p Calc -o calc.go calc.y
go run calc.go
