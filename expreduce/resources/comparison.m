NumericQ::usage =  "`NumericQ[expr]` returns `True` if `expr` is a numeric quantity, `False` otherwise.";
NumericQ[e_] := If[NumberQ[N[e]], True, False];
Attributes[NumericQ] = {Protected};
Tests`NumericQ = {
    ESimpleExamples[
        ESameTest[True, NumericQ[5]],
        ESameTest[False, NumericQ[a]],
        ESameTest[False, NumericQ[Sin[a]]],
        ESameTest[True, NumericQ[Sin[2]]]
    ], ETests[
        ESameTest[True, NumericQ[Cos[2]]],
        ESameTest[False, NumericQ[Sqrt[a]]],
        ESameTest[False, NumericQ[Sqrt[Sin[2]]*Sqrt[Sin[x]]]],
        ESameTest[True, NumericQ[Sqrt[2]]]
    ]
};
Equal::usage = "`lhs == rhs` evaluates to True or False if equality or inequality is known.";
(*TODO(corywalker): Ideally this should be handled in the core. Also should
  support arbitrary number of arguments.*)
Equal[a_?NumericQ, b_?NumericQ] := (a//N) == (b//N);
Attributes[Equal] = {Protected};
Tests`Equal = {
    ESimpleExamples[
        EComment["Expressions known to be equal will evaluate to True:"],
        EStringTest["True", "9*x==x*9"],
        EComment["Sometimes expressions may or may not be equal, or Expreduce does not know how to test for equality. In these cases, the statement will remain unevaluated:"],
        EStringTest["(9*x == 10*x)", "9*x==x*10"],
        EComment["Equal considers Integers and Reals that are close enough to be equal:"],
        EStringTest["5", "tmp=5"],
        EStringTest["True", "tmp==5"],
        EStringTest["True", "tmp==5."],
        EStringTest["True", "tmp==5.00000"],
        EComment["Equal can test for Rational equality:"],
        EStringTest["False", "4/3==3/2"],
        EStringTest["True", "4/3==8/6"]
    ], EFurtherExamples[
        EStringTest["True", "If[xx == 2, yy, zz] == If[xx == 2, yy, zz]"],
        EComment["Equal does not match patterns:"],
        ESameTest[{1, 2, 3} == _List, {1, 2, 3} == _List],
        EComment["This functionality is reserved for MatchQ:"],
        ESameTest[True, MatchQ[{1, 2, 3}, _List]]
    ], ETests[
        EStringTest["5", "tmp=5"],
        EStringTest["True", "tmp==5"],
        EStringTest["True", "5==tmp"],
        EStringTest["False", "tmp==6"],
        EStringTest["False", "6==tmp"],
        EStringTest["(a == b)", "a==b"],
        EStringTest["True", "a==a"],
        EStringTest["(a == 2)", "a==2"],
        EStringTest["(2 == a)", "2==a"],
        EStringTest["(2 == a + b)", "2==a+b"],
        EStringTest["(2. == a)", "2.==a"],
        EStringTest["(2^k == a)", "2^k==a"],
        EStringTest["(2^k == 2^a)", "2^k==2^a"],
        EStringTest["(2^k == 2 + k)", "2^k==k+2"],
        EStringTest["(k == 2*k)", "k==2*k"],
        EStringTest["(2*k == k)", "2*k==k"],
        EStringTest["True", "1+1==2"],
        EStringTest["(y == b + m*x)", "y==m*x+b"],
        EStringTest["True", "1==1."],
        EStringTest["True", "1.==1"],
        EStringTest["True", "(x==2)==(x==2)"],
        EStringTest["True", "(x==2.)==(x==2)"],
        EStringTest["True", "(x===2.)==(x===2)"],
        EStringTest["(If[xx == 3, yy, zz] == If[xx == 2, yy, zz])", "If[xx == 3, yy, zz] == If[xx == 2, yy, zz]"],
        EStringTest["True", "(1 == 2) == (2 == 3)"],
        EStringTest["False", "(1 == 2) == (2 == 2)"],
        ESameTest[True, foo[x == 2, y, x] == foo[x == 2, y, x]],
        ESameTest[True, foo[x == 2, y, x] == foo[x == 2., y, x]],
        ESameTest[foo[x == 2, y, x] == foo[x == 2., y, y], foo[x == 2, y, x] == foo[x == 2., y, y]],
        ESameTest[foo[x == 2, y, x] == bar[x == 2, y, x], foo[x == 2, y, x] == bar[x == 2, y, x]],
        EStringTest["(foo[x, y, z] == foo[x, y])", "foo[x, y, z] == foo[x, y]"],
        EStringTest["(foo[x, y, z] == foo[x, y, 1])", "foo[x, y, z] == foo[x, y, 1]"],
        ESameTest[True, foo[x, y, 1] == foo[x, y, 1]],
        ESameTest[True, foo[x, y, 1.] == foo[x, y, 1]],
        ESameTest[True, Equal[test]],
        ESameTest[True, Equal[]],
        ESameTest[False, (-1)^(1/6)==-I],
        ESameTest[True, (-1)^(1/6)==(-1)^(1/6)//N],
        ESameTest[True, (2^(-1/2)*E^((-1/2)*x^2)*Pi^(-1/2)/.x->(-Sqrt[2] Sqrt[Log[5 Sqrt[2/\[Pi]]]]//N))==.1],
        ESameTest[True, 1.0000000000005==1.00000000000051],
        ESameTest[False, 1.000000000005==1.0000000000051],
        ESameTest[True, 100.00000000005==100.000000000051],
        ESameTest[True, 1000000000000.5==1000000000000.51],
    ]
};

Unequal::usage = "`lhs != rhs` evaluates to True if inequality is known or False if equality is known.";
Attributes[Unequal] = {Protected};
Tests`Unequal = {
    ESimpleExamples[
        EComment["Expressions known to be unequal will evaluate to True:"],
        EStringTest["True", "9 != 8"],
        EComment["Sometimes expressions may or may not be unequal, or Expreduce does not know how to test for inequality. In these cases, the statement will remain unevaluated:"],
        EStringTest["((9*x) != (10*x))", "9*x != x*10"],
        EComment["Unequal considers Integers and Reals that are close enough to be equal:"],
        EStringTest["5", "tmp=5"],
        EStringTest["False", "tmp != 5"],
        EStringTest["False", "tmp != 5."],
        EStringTest["False", "tmp != 5.00000"],
        EComment["Unequal can test for Rational inequality:"],
        EStringTest["True", "4/3 != 3/2"],
        EStringTest["False", "4/3 != 8/6"]
    ]
};

SameQ::usage = "`lhs === rhs` evaluates to True if `lhs` and `rhs` are identical after evaluation, False otherwise.";
Attributes[SameQ] = {Protected};
Tests`SameQ = {
    ESimpleExamples[
        EStringTest["True", "a===a"],
        EStringTest["True", "5 === 5"],
        EComment["Unlike Equal, SameQ does not forgive differences between Integers and Reals:"],
        EStringTest["False", "5 === 5."],
        EComment["SameQ considers the arguments of all expressions and subexpressions:"],
        ESameTest[True, foo[x == 2, y, x] === foo[x == 2, y, x]],
        ESameTest[False, foo[x == 2, y, x] === foo[x == 2., y, x]]
    ], EFurtherExamples[
        EComment["SameQ does not match patterns:"],
        ESameTest[False, {1, 2, 3} === _List],
        EComment["This functionality is reserved for MatchQ:"],
        ESameTest[True, MatchQ[{1, 2, 3}, _List]]
    ], ETests[
        EStringTest["5", "tmp=5"],
        EStringTest["False", "a===b"],
        EStringTest["True", "tmp===5"],
        EStringTest["False", "tmp===5."],
        EStringTest["True", "1+1===2"],
        EStringTest["False", "y===m*x+b"],
        EStringTest["False", "1===1."],
        EStringTest["False", "1.===1"],
        EStringTest["True", "(x===2.)===(x===2)"],
        EStringTest["False", "(x==2.)===(x==2)"],
        EStringTest["True", "If[xx == 2, yy, zz] === If[xx == 2, yy, zz]"],
        EStringTest["False", "If[xx == 2, yy, zz] === If[xx == 2., yy, zz]"],
        EStringTest["False", "If[xx == 3, yy, zz] === If[xx == 2, yy, zz]"],
        EStringTest["False", "(x == y) === (y == x)"],
        EStringTest["True", "(x == y) === (x == y)"],
        ESameTest[False, foo[x == 2, y, x] === foo[x == 2., y, y]],
        ESameTest[False, foo[x == 2, y, x] === bar[x == 2, y, x]],
        ESameTest[False, foo[x, y, z] === foo[x, y]],
        ESameTest[False, foo[x, y, z] === foo[x, y, 1]],
        ESameTest[True, foo[x, y, 1] === foo[x, y, 1]],
        ESameTest[False, foo[x, y, 1.] === foo[x, y, 1]],
        ESameTest[True, SameQ[test]],
        ESameTest[True, SameQ[]]
    ]
};

UnsameQ::usage = "`lhs =!= rhs` evaluates to False if `lhs` and `rhs` are identical after evaluation, True otherwise.";
Attributes[UnsameQ] = {Protected};
Tests`UnsameQ = {
    ESimpleExamples[
        EStringTest["False", "a=!=a"],
        EStringTest["False", "5 =!= 5"],
        EStringTest["True", "a=!=b"]
    ], ETests[
        EStringTest["False", "a=!=b=!=a"],
        EStringTest["True", "UnsameQ[]"]
    ]
};

AtomQ::usage = "`AtomQ[expr]` returns True if `expr` is an atomic type, and False if `expr` is a full expression.";
Attributes[AtomQ] = {Protected};
Tests`AtomQ = {
    ESimpleExamples[
        ESameTest[True, AtomQ["hello"]],
        ESameTest[True, AtomQ[5/3]],
        ESameTest[True, AtomQ[hello]],
        ESameTest[False, AtomQ[a/b]],
        ESameTest[False, AtomQ[bar[x]]]
    ]
};

NumberQ::usage = "`NumberQ[expr]` returns True if `expr` is numeric, otherwise False.";
Attributes[NumberQ] = {Protected};
Tests`NumberQ = {
    ESimpleExamples[
        ESameTest[True, NumberQ[2]],
        ESameTest[True, NumberQ[2.2]],
        ESameTest[True, NumberQ[Rational[5, 2]]],
        ESameTest[False, NumberQ[Infinity]],
        ESameTest[False, NumberQ[Sqrt[2]]],
        ESameTest[False, NumberQ[randomvar]],
        ESameTest[False, NumberQ["hello"]]
    ]
};

Less::usage = "`a < b` returns True if `a` is less than `b`.";
Attributes[Less] = {Protected};
Tests`Less = {
    ESimpleExamples[
        ESameTest[a < b, a < b],
        ESameTest[True, 1 < 2],
        ESameTest[True, 3 < 5.5],
        ESameTest[False, 5.5 < 3],
        ESameTest[False, 3 < 3]
    ]
};

Greater::usage = "`a > b` returns True if `a` is greater than `b`.";
Attributes[Greater] = {Protected};
Tests`Greater = {
    ESimpleExamples[
        ESameTest[a > b, a > b],
        ESameTest[False, 1 > 2],
        ESameTest[False, 3 > 5.5],
        ESameTest[True, 5.5 > 3],
        ESameTest[False, 3 > 3]
    ]
};

LessEqual::usage = "`a <= b` returns True if `a` is less than or equal to `b`.";
-Infinity <= (_Integer | _Real | _Rational) := True;
Infinity <= (_Integer | _Real | _Rational) := False;
(_Integer | _Real | _Rational) <= -Infinity := False;
(_Integer | _Real | _Rational) <= Infinity := True;
Attributes[LessEqual] = {Protected};
Tests`LessEqual = {
    ESimpleExamples[
        ESameTest[a <= b, a <= b],
        ESameTest[True, 1 <= 2],
        ESameTest[True, 3 <= 5.5],
        ESameTest[False, 5.5 <= 3],
        ESameTest[True, 3 <= 3]
    ]
};

GreaterEqual::usage = "`a >= b` returns True if `a` is greater than or equal to `b`.";
Attributes[GreaterEqual] = {Protected};
Tests`GreaterEqual = {
    ESimpleExamples[
        ESameTest[a >= b, a >= b],
        ESameTest[False, 1 >= 2],
        ESameTest[False, 3 >= 5.5],
        ESameTest[True, 5.5 >= 3],
        ESameTest[True, 3 >= 3]
    ]
};

Positive::usage = "`Positive[x]` returns `True` if `x` is positive.";
Positive[x_?NumberQ] := x > 0;
Attributes[Positive] = {Listable, Protected};
Tests`Positive = {
    ESimpleExamples[
        ESameTest[{True, False, False, Positive[a]}, Map[Positive, {1, 0, -1, a}]]
    ]
};

Negative::usage = "`Negative[x]` returns `True` if `x` is positive.";
Negative[x_?NumberQ] := x < 0;
Attributes[Negative] = {Listable, Protected};
Tests`Negative = {
    ESimpleExamples[
        ESameTest[{False, False, True, Negative[a]}, Map[Negative, {1, 0, -1, a}]]
    ]
};

Max::usage = "`Max[e1, e2, ...]` the maximum of the expressions.";
Attributes[Max] = {Flat, NumericFunction, OneIdentity, Orderless, Protected};
Tests`Max = {
    ESimpleExamples[
        ESameTest[3, Max[1,2,3]],
        ESameTest[Max[3,a], Max[1,a,3]]
    ], ETests[
        ESameTest[Max[3,a,b], Max[b,1,a,3]],
        ESameTest[Max[3.,a,b], Max[b,1,a,3,3.]],
        ESameTest[Max[3.1,a,b], Max[b,1,a,3,3.,3.1]],
        ESameTest[Max[99/2,a,b], Max[b,1,a,3,3.,3.1 ,Rational[99,2]]],
        ESameTest[-Infinity, Max[]],
        ESameTest[Max[99/2,a,b], Max[{b,1,a},3,3.,3.1 ,Rational[99,2]]],
        ESameTest[Max[99/2,foo[b,1,a]], Max[foo[b,1,a],3,3.,3.1 ,Rational[99,2]]]
    ], EKnownDangerous[
        ESameTest[Max[a,b,c,d], Max[{c,d},{b,a}]],
        ESameTest[Max[a,b,c,d], Max[{c,{d}},{b,a}]]
    ]
};

Min::usage = "`Min[e1, e2, ...]` the maximum of the expressions.";
Attributes[Min] = {Flat, NumericFunction, OneIdentity, Orderless, Protected};
Tests`Min = {
    ESimpleExamples[
        ESameTest[1, Min[1,2,3]],
        ESameTest[Min[1,a], Min[1,a,3]]
    ], ETests[
        ESameTest[Min[1,a,b], Min[b,1,a,3]],
        ESameTest[Min[1,a,b], Min[b,1,a,3,3.]],
        ESameTest[Min[1,a,b], Min[b,1,a,3,3.,3.1]],
        ESameTest[Min[1,a,b], Min[b,1,a,3,3.,3.1 ,Rational[99,2]]],
        ESameTest[Infinity, Min[]],
    ], EKnownDangerous[
        ESameTest[Min[a,b,c,d], Min[{c,d},{b,a}]],
        ESameTest[Min[a,b,c,d], Min[{c,{d}},{b,a}]]
    ]
};

PossibleZeroQ::usage = "`PossibleZeroQ[e]` returns True if `e` is most likely equivalent to zero.";
Attributes[PossibleZeroQ] = {Listable, Protected};
PossibleZeroQ[e_] := e === 0 || e === 0.;
Tests`PossibleZeroQ = {
    ESimpleExamples[
        ESameTest[True, PossibleZeroQ[a-a]],
        ESameTest[False, PossibleZeroQ[a-b]]
    ]
};

MinMax::usage = "`MinMax[l]` returns `{Min[l], Max[l]}`.";
Attributes[MinMax] = {Protected};
MinMax[l_List] := {Min[l], Max[l]};
Tests`MinMax = {
    ESimpleExamples[
        ESameTest[{1, 5}, MinMax[Range[5]]]
    ]
};

Element::usage = "`Element[i, s]` checks if `i` is an element of `s`.";
Attributes[Element] = {Protected};
Element[i_Integer, Integers] := True;
Tests`Element = {
    ESimpleExamples[
        ESameTest[True, Element[-1, Integers]]
    ]
};

Attributes[Inequality] = {Protected};
Tests`Inequality = {
    ESimpleExamples[
        ESameTest[True, Inequality[-Pi,Less,0,LessEqual,Pi]],
        ESameTest[0<=a, Inequality[-Pi,Less,0,LessEqual,a]],
    ], ETests[
        ESameTest[Inequality[c, Less, 0, Less, a], Inequality[c,Less,0,Less,a]],
        ESameTest[c<0, Inequality[c,Less,0]],
        ESameTest[Inequality[c,Less], Inequality[c,Less]],
        ESameTest[True, Inequality[c]],
        ESameTest[Inequality[], Inequality[]],
        ESameTest[True, Inequality[False]],
        ESameTest[Inequality[-1, Less], Inequality[-1,Less]],
        ESameTest[Inequality[-1, Less, a, Less, 0], Inequality[-1,Less,a,Less,0,Less,1]],
        ESameTest[Inequality[0, Less, a, Less, 1], Inequality[-1,Less,0,Less,a,Less,1]],
        ESameTest[False, Inequality[-1,Less,a,Less,-2]],
        ESameTest[0>=a, Inequality[-Pi,Less,0,GreaterEqual,a]],
        ESameTest[0<a&&Inequality[a,Greater,0,Greater,k], Inequality[0,Less,a,Greater,0,Greater,k]],
        ESameTest[0>a&&a<0, Inequality[0,Greater,a,Less,0]],
        ESameTest[Inequality[0, Less, a, Less, 1], Inequality[0,Less,a,Less,1]],
        ESameTest[0<a&&a<1, 0<a && a<1],
        ESameTest[a<b<=c, Inequality[a,Less,b,LessEqual,c]],
        ESameTest[a<b<=c==d&&d>=e>f, Inequality[a,Less,b,LessEqual,c,Equal,d,GreaterEqual,e,Greater,f]],
        ESameTest[a>b>=c==d&&d<=e<f, Inequality[a,Greater,b,GreaterEqual,c,Equal,d,LessEqual,e,Less,f]],
        ESameTest[a>b>=c==d>=e&&e<f, Inequality[a,Greater,b,GreaterEqual,c,Equal,d,GreaterEqual,e,Less,f]],
        ESameTest[False, Inequality[a,Greater,1,GreaterEqual,c,Equal,d,GreaterEqual,5,Less,f]],
        ESameTest[a<1<4<=b, a<1<2<3<4<=b],
        ESameTest[a<1<4<=b<5, a<1<2<3<4<=b<5],
    ], EKnownFailures[
        ESameTest[Inequality[0,Lesks,1], Inequality[-1,Less,0,Lesks,1]],
    ]
};
