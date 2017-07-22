And::usage = "`e1 && e2 && ...` returns `True` if all expressions evaluate to `True`.";
Attributes[And] = {Flat, HoldAll, OneIdentity, Protected};
Tests`And = {
    ESimpleExamples[
        ESameTest[False, True && False],
        ESameTest[True, True && True && True]
    ], ETests[
        ESameTest[True, And[]],
        ESameTest[1, 1 && True && True],
        ESameTest[False, True && False],
        ESameTest[False, False && True],
        ESameTest[True, True && True],
        ESameTest[False, False && 1],
        ESameTest[False, 1 && False],
        ESameTest[1 && 1, 1 && 1],
        ESameTest[1 && 1 && kfdkkfd, 1 && 1 && kfdkkfd],
        ESameTest[1 && 1 && kfdkkfd, 1 && 1 && True && kfdkkfd],
        ESameTest[False, 1 && 1 && True && False && kfdkkfd]
    ]
};

Or::usage = "`e1 || e2 || ...` returns `True` if any expressions evaluate to `True`.";
Attributes[Or] = {Flat, HoldAll, OneIdentity, Protected};
Tests`Or = {
    ESimpleExamples[
        ESameTest[True, True || False],
        ESameTest[False, False || False || False]
    ], ETests[
        ESameTest[a || b, a || b],
        ESameTest[True, a || True || b],
        ESameTest[True, a || True || False],
        ESameTest[a || b, a || b || False],
        ESameTest[a || b, a || b || False || False],
        ESameTest[a || b, a || False || b || False || False],
        ESameTest[True, True || False],
        ESameTest[False, False || False],
        ESameTest[False, Or[False]],
        ESameTest[False, Or[]]
    ]
};

Not::usage = "`!e` returns `True` if `e` is `False` and `False` if `e` is `True`.";
!!e_ := e;
Attributes[Not] = {Protected};
Tests`Not = {
    ESimpleExamples[
        ESameTest[False, !True],
        ESameTest[True, !False],
        ESameTest[!a, !a],
        ESameTest[a, !!a]
    ]
};

TrueQ::usage = "`TrueQ[expr]` returns True if `expr` is True, False otherwise.";
Attributes[TrueQ] = {Protected};
Tests`TrueQ = {
    ESimpleExamples[
        ESameTest[True, TrueQ[True]],
        ESameTest[False, TrueQ[False]],
        ESameTest[False, TrueQ[1]]
    ]
};

BooleanQ::usage = "`BooleanQ[expr]` returns True if `expr` is True or False, False otherwise.";
Attributes[BooleanQ] = {Protected};
Tests`BooleanQ = {
    ESimpleExamples[
        ESameTest[True, BooleanQ[True]],
        ESameTest[True, BooleanQ[False]],
        ESameTest[False, BooleanQ[1]]
    ]
};

AllTrue::usage = "`AllTrue[list, condition]` returns True if all parts of `list` satisfy `condition`.";
AllTrue[_[elems___], cond_] := And @@ (cond /@ {elems});
Attributes[AllTrue] = {Protected};
Tests`AllTrue = {
    ESimpleExamples[
        ESameTest[False, AllTrue[{1, a}, NumberQ]],
        ESameTest[True, AllTrue[{1, 2}, NumberQ]]
    ]
};

Boole::usage = "`Boole[e]` returns 0 if `e` is False and 1 if `e` is True.";
Boole[True] := 1;
Boole[False] := 0;
Attributes[Boole] = {Listable, Protected};
Tests`Boole = {
    ESimpleExamples[
        ESameTest[1, Boole[True]],
        ESameTest[0, Boole[False]]
    ], ETests[
        ESameTest[Boole[1], Boole[1]],
        ESameTest[Boole[a], Boole[a]],
        ESameTest[Boole[False,False], Boole[False, False]]
    ]
};
