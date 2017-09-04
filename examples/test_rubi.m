testproblems = ReadList["/Users/cwalker32/Code/gocode/src/github.com/corywalker/expreduce/test_rubi/test_rubi.m"];
testproblems = DeleteCases[testproblems, Null];

testi = 1;

runRubiTest[thei_Integer] := (
    testp = testproblems[[thei]];
    (*Print[testp];*)
    res = Int[testp[[1]], testp[[2]]];
    (*Print[res];*)
    (*Print[res === testp[[4]]];*)
    (*If[res === testp[[4]], Print[thei]];*)
    If[res =!= testp[[4]], Print[thei]];
);

While[testi <= Length[testproblems],
    Print["Testing ", testi, " ", testproblems[[testi]]]
    (*If[(testi>34&&testi<47)||MemberQ[{50, 52, 53, 54, 55, 56, 57, 58, 59, 211, 214, 215, 216, 218, 222, 223, 224, 225, 228, 229, 231, 232, 233}, testi] || (testi>=160&&testi<=166), Null,
        runRubiTest[testi];
    ];*)
    runRubiTest[testi];
    testi = testi+1;
];
