# Expreduce
[![Build Status](https://travis-ci.org/corywalker/expreduce.svg?branch=master)](https://travis-ci.org/corywalker/expreduce)

This software is experimental quality and is not currently intended for serious use. There are plenty of more mature open source computer algebra systems to use instead.

# Source generation
Generate source files from lex and yacc:
```
go generate
```

# Example
This must be done after running "go generate". To run the example CAS prompt:

```
cd example
go run calc.go
```

```
# go run calc.go

Welcome to Expreduce!

In[1]:= D[Sin[x]/x,x]

Out[1]= ((-1 * x^-2 * Sin[x]) + (Cos[x] * x^-1))

In[2]:= Table[a^2,{a,1,10}]

Out[2]= {1, 4, 9, 16, 25, 36, 49, 64, 81, 100}

In[3]:= Sum[i, {i, 1, n}]

Out[3]= (1/2 * (1 + n) * n)

In[4]:= (2^(-1) * n * (1 + n)) /. n->5

Out[4]= 15

In[5]:= Total[Table[i,{i,1,5}]]

Out[5]= 15

In[6]:= bar[1, foo[a, b]] + bar[2, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] + bar[bmatch_Integer, foo[cmatch__]] -> bar[amatch + bmatch, foo[cmatch]]

Out[6]= bar[3, foo[a, b]]
```

## Development

To run the tests:
```
go test
```
