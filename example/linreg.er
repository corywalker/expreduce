n = 50;
x = Table[{1, RandomReal[{-1, 1}]}, {i, n}];
targetM = .2;
targetB = 3;
y = Table[
{x[[i, 2]]*targetM + targetB + RandomReal[{-.05, .05}]}, {i, n}];
params = (Inverse[Transpose[x].x].Transpose[x]).y
