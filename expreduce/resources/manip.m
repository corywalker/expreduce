Together::usage = "`Together[e]` attempts to put the terms in `e` under the same denominator.";
Together[(rest___ + a_*Rational[b_,c_])/d_] := (Print[5];Together[(a b+Expand[c Plus[rest]])/(c d)]);
Together[a_+Rational[b_,c_]*d_] := (Print[7];Together[(a c+b d)/c]);
Together[(e_)^p_?((NumberQ[#] && # =!= -1)&)] := Together[Together[e]^p];

Together[(a_/b_+rest___)/d_] := (Print[1];Together[(a+Expand[b Plus[rest]])/(b d)]);
(*Together[(a_/b_+rest___)/(c_*d_)] := (Print[4];Together[(a+Expand[b Plus[rest]])/(b c d)]);*)
Together[a_/b_+c_+rest___] := (Print[2];Together[(a+b c)/b+rest]);
Together[1/(a__Plus) + b__] := (Print[3];Together[(1+Expand[a*Plus[b]])/(a)]);
Together[1/(a__Plus)+1/(b__Plus) + c___] := (Print[6];Together[(a+b+Expand[a*b*Plus[c]])/(a*b)]);
Together[1/(a_Symbol)+ rest___] := (Print[8];Together[(1+Expand[a*Plus[rest]])/(a)]);

Together[e_] := e;
Attributes[Together] = {Listable, Protected};
Tests`Together = {
    ESimpleExamples[
        ESameTest[(6+a)/(2 a), 1/2+3/a//Together],
        ESameTest[(1/2+3/a)^c, (1/2+3/a)^c//Together],
        ESameTest[(6+a)^2/(4 a^2), (1/2+3/a)^2//Together],
        ESameTest[(c+a d+b d)/d, a+b+c/d//Together],
        ESameTest[(a+b+c+d)/((a+b) (c+d)), 1/(a+b)+1/(c+d)//Together],
        ESameTest[(a+b+c-a^2 c-a b c+d-a^2 d-a b d)/((a+b) (c+d)), 1/(a+b)+1/(c+d)-a//Together],
        (*Only for when we have Cancel:*)
        (*ESameTest[-(a/(2+a)), Together[a/(-2+a+a^2)-a^2/(-2+a+a^2)]],*)
        ESameTest[(a+b c)/b, a/b+c//Together],
        ESameTest[(b c+a d)/(b d), (a+(b c)/d)/b//Together],
        ESameTest[(b c+a d)/d, a+(b c)/d//Together],
        ESameTest[(c+a d+b d)/d, Together[(c + a*d + b*d)/d]],
        ESameTest[(6+a+2 b)/(2 a), (3+a/2+b)/a//Together],
        ESameTest[a/(b e), (a/b)/e//Together],
        ESameTest[(12+a)/(4 a), (3 + a*1/4)/a//Together],
        ESameTest[1/2 (6+foo[a]), 3 + foo[a]*2/4//Together],
        ESameTest[(6+a)/(2 a), 1/2 + 3/a//Together],
        ESameTest[(a+b c)/(a b), (c+ a/b)/a//Together],
        ESameTest[(a+b c+b e)/(b d), (c+e+ a/b)/d//Together],
        ESameTest[(6+a)/(2 a), (3 + a/2)/a//Together],
        ESameTest[(a b+c rest)/(c d), (rest + a*b/c)/d//Together],
        ESameTest[(1+a c+b c)/(a+b), 1/(a+b)+c//Together],
        ESameTest[(c+a d+b d)/d, Together[(c + a*d + b*d)/d]],
        ESameTest[(6+a+2 b)/(2 a), (3+a/2+b)/a//Together],
        ESameTest[a/(b e), (a/b)/e//Together],
        ESameTest[(a+a^2 c+a b c+a d+b d)/(a (a+b)), Together[1/(a + b) + c+d/a]],
        ESameTest[(a+b) (c+d), (a+b)(c+d)//Together],
        ESameTest[(a+b+c+d)/((a+b) (c+d)), 1/(a + b)+1/(c+d)//Together],
        ESameTest[1/(a+b), 1/(a + b)//Together],
        ESameTest[(a+b c e f)/(b c), a/(b*c)+(e*f)//Together],
        ESameTest[(a+b+c-a^2 c-a b c+d-a^2 d-a b d)/((a+b) (c+d)), Together[1/(a + b) + 1/(c + d) - a]],
        ESameTest[(a+b)/(a b), 1/a+1/b//Together],
        ESameTest[(a+b+a b c)/(a b), 1/a+1/b+c//Together],
        ESameTest[(1+c d)/c, 1/c+d//Together],
        ESameTest[(a+b+a b c+a b d)/(a b), 1/a+1/b+c+d//Together]
    ]
};

Distribute::usage = "`Distribute[e]` distributes the function over the `Plus` expressions.";
(*Distribute[e_, f_] := e;*)
Distribute[e_] := Distribute[e, Plus];
Attributes[Distribute] = {Protected};
Tests`Distribute = {
    ESimpleExamples[
        ESameTest[a c+b c+a d+b d, Distribute[(a+b)*(c+d)]],
        ESameTest[a c+b c, Distribute[(a+b)*c]],
        ESameTest[foo[a,c]+foo[b,c], Distribute[foo[(a+b),c]]],
        ESameTest[foo[a,b], Distribute[foo[a,b]]],
        ESameTest[foo[c]+foo[a,b], Distribute[foo[a,b]+foo[c]]],
        ESameTest[a+(a+b) c, Distribute[(a+b)*(c)+a]],
        ESameTest[(a+b) c e+d e+(a+b) c f+d f, Distribute[((a+b)*(c)+d)*(e+f)]],
        ESameTest[test[foo[a,b]], Distribute[foo[a,b],test]],
        ESameTest[test[foo[a,b],foo[a,c]], Distribute[foo[a,test[b,c]],test]],
        ESameTest[test[foo[a,b,d],foo[a,b,e],foo[a,c,d],foo[a,c,e]], Distribute[foo[a,test[b,c],test[d,e]],test]],
        ESameTest[test[foo[a,b,d,bar[a]],foo[a,b,e,bar[a]],foo[a,c,d,bar[a]],foo[a,c,e,bar[a]]], Distribute[foo[a,test[b,c],test[d,e],bar[a]],test]],
        ESameTest[a, Distribute[a,test]],
        ESameTest[1[a+b], Distribute[a+b,1]],
        ESameTest[test[bar[a,b,d],bar[a,b,e],bar[a,c,d],bar[a,c,e]], Distribute[bar[a,test[b,c],test[d,e]],test]],
        ESameTest[test[test[f,g][a,b,d],test[f,g][a,b,e],test[f,g][a,c,d],test[f,g][a,c,e]], Distribute[test[f,g][a,test[b,c],test[d,e]],test]],
        ESameTest[test[foo[]], Distribute[foo[],test]],
        ESameTest[test[][foo[]], Distribute[foo[],test[]]],
        ESameTest[foo, Distribute[foo,test]]
    ]
};
