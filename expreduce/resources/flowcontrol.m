If::usage = "`If[cond, iftrue, iffalse]` returns `iftrue` if `cond` is True, and `iffalse` if `cond` is False.";
Attributes[If] = {HoldRest, Protected};
Tests`If = {
    ESimpleExamples[
        EStringTest["9", "x=9"],
        EStringTest["18", "If[x+3==12, x*2, x+3]"],
        EStringTest["12", "If[x+3==11, x*2, x+3]"]
    ], EFurtherExamples[
        EComment["Undefined conditions leave the statement unevaluated."],
        EStringTest["If[undefined, a, b]", "If[undefined, a, b]"]
    ], ETests[
        EStringTest["True", "t=True"],
        EStringTest["True", "t"],
        EStringTest["False", "f=False"],
        EStringTest["False", "f"],
        EStringTest["True", "If[t, True, False]"],
        EStringTest["False", "If[f, True, False]"],
        EStringTest["False", "If[t, False, True]"],
        EStringTest["True", "If[f, False, True]"],
        ESameTest[itsfalse, If[1 == 2, itstrue, itsfalse]],
        ESameTest[itsfalse, If[1 == 2, itstrue, itsfalse] /. (2 -> 1)],
        ESameTest[itstrue, If[1 == k, itstrue, itsfalse] /. (k -> 1)],
        ESameTest[If[1 == k, itstrue, itsfalse], If[1 == k, itstrue, itsfalse]],
        ESameTest[a, If[True, a]],
        ESameTest[Null, If[False, a]]
    ]
};

While::usage = "`While[cond, body]` evaluates `cond`, and if it returns True, evaluates `body`. This happens repeatedly.";
Attributes[While] = {HoldAll, Protected};
Tests`While = {
    ESimpleExamples[
        ESameTest[1, a=1],
        ESameTest[Null, While[a != 5, a = a + 1]],
        ESameTest[5, a]
    ]
};

CompoundExpression::usage = "`CompoundExpression[e1, e2, ...]` evaluates each expression in order and returns the result of the last one.";
Attributes[CompoundExpression] = {HoldAll, ReadProtected, Protected};
Tests`CompoundExpression = {
    ESimpleExamples[
        EComment["The result of the first expression is not included in the output, but the result of the second is:"],
        ESameTest[3, a = 5; a - 2],
        EComment["Including a trailing semicolon causes the expression to return `Null`:"],
        ESameTest[Null, a = 5; a - 2;]
    ]
};

Return::usage = "`Return[x]` returns `x` immediately.";
Attributes[Return] = {Protected};
Tests`Return = {
    ESimpleExamples[
        ESameTest[x, myreturnfunc:=(Return[x];hello);myreturnfunc],
        ESameTest[3, ret[x_]:=(Return[x];hello);ret[3]],
        ESameTest[3, myfoo:=(i=1;While[i<5,If[i===3,Return[i]];i=i+1]);myfoo],
        ESameTest[Return[3], Return[3]],
        ESameTest[Null, retother:=(Return[];hello);retother]
    ]
};

Which::usage = "`Which[cond, res, cond, res, ...]` tries each `cond` in sequence and returns the corresponding result if True.";
Attributes[Which] = {HoldAll, Protected};
Tests`Which = {
    ESimpleExamples[
        ESameTest[b, Which[1>2, a, 1<2, b]],
        ESameTest[Null, Which[2>2, a, 2<2, b]]
    ], ETests[
        ESameTest[Which[True, a, b], Which[True, a, b]],
        ESameTest[Null, Which[False,a,False,b]]
    ]
};

Switch::usage = "`Switch[e, case1, val1, case2, val2, ...]` attempts to match `e` with the cases in order. If a match is found, returns the corresponding value..";
Attributes[Switch] = {HoldRest, Protected, ReadProtected};
Tests`Switch = {
    ESimpleExamples[
        ESameTest[b, Switch[z,_,b,z,c]],
        ESameTest[k, Switch[z,k_Symbol,k]],
        ESameTest[Switch[z,1], Switch[z,1]],
        ESameTest[Switch[z,d,b,l,c], Switch[z,d,b,l,c]]
    ], ETests[
        ESameTest[Switch[], Switch[]],
        ESameTest[Switch[z], Switch[z]]
    ]
};

With::usage = "`With[{s1=v1, s2=v2, ...}, body]` locally replaces the specified symbols in body with their respective values.";
Attributes[With] = {HoldAll, Protected};
Tests`With = {
    ESimpleExamples[
        ESameTest[{2, 6}, With[{x=2},{x,3*x}]],
        ESameTest[{2, 9}, With[{x:=2,y:=3},{x,3*y}]]
    ]
};

Do::usage = "`Do[expr, n]` evaluates `expr` `n` times.

`Table[expr, {sym, n}]` evaluates `expr` with `sym` = 1 to `n`.

`Table[expr, {sym, m, n}]` evaluates `expr` with `sym` = `m` to `n`.";
Attributes[Do] = {HoldAll, Protected};
Tests`Do = {
    ESimpleExamples[
        ESameTest[7, Catch[Do[If[a > 6, Throw[a]], {a, 10}]; False]]
    ]
};
