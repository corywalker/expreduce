testproblems = ReadList["/Users/cwalker32/Code/gocode/src/github.com/corywalker/expreduce/test_rubi/test_rubi.m"];
testproblems = DeleteCases[testproblems, Null];

testi = 1;

While[testi <= Length[testproblems],
    testp = testproblems[[testi]];
    (*Print[testp];*)
    res = Int[testp[[1]], testp[[2]]];
    (*Print[res];*)
    (*Print[res === testp[[4]]];*)
    If[res === testp[[4]], Print[testi]];
    testi = testi+1;
];
