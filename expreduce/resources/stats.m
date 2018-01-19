NormalDistribution::usage = "`NormalDistribution[mu, sigma]` is a normal distribution with a mean `mu` and standard deviation of `sigma`.";
Attributes[NormalDistribution] = {ReadProtected, Protected};
Tests`NormalDistribution = {
    ESimpleExamples[
        ESameTest[E^(-((x-\[Mu])^2/(2 \[Sigma]^2)))/(Sqrt[2 \[Pi]] \[Sigma]), PDF[NormalDistribution[\[Mu],\[Sigma]],x]]
    ]
};

LogNormalDistribution::usage = "`LogNormalDistribution[mu, sigma]` is a lognormal distribution with a mean `mu` and standard deviation of `sigma`.";
Attributes[LogNormalDistribution] = {ReadProtected, Protected};
Tests`LogNormalDistribution = {
    ESimpleExamples[
        ESameTest[Piecewise[{{1/(E^((-\[Mu] + Log[x])^2/(2*\[Sigma]^2))*Sqrt[2*Pi]*x*\[Sigma]), x > 0}}, 0], PDF[LogNormalDistribution[\[Mu],\[Sigma]],x]]
    ]
};

PDF::usage = "`PDF[dist, var]` calculates the PDF of `dist`.";
PDF[NormalDistribution[mu_, sigma_], x_] := E^(-((-mu+x)^2/(2 sigma^2)))/(Sqrt[2 \[Pi]] sigma);
PDF[LogNormalDistribution[mu_, sigma_], x_] := Piecewise[{{1/(E^((-mu + Log[x])^2/(2*sigma^2))*Sqrt[2*Pi]*sigma*x), x > 0}},  0]
Attributes[PDF] = {ReadProtected, Protected};
Tests`PDF = {
    ESimpleExamples[
        ESameTest[E^(-((x-\[Mu])^2/(2 \[Sigma]^2)))/(Sqrt[2 \[Pi]] \[Sigma]), PDF[NormalDistribution[\[Mu],\[Sigma]],x]],
        ESameTest[Piecewise[{{1/(E^((-\[Mu] + Log[x])^2/(2*\[Sigma]^2))*Sqrt[2*Pi]*x*\[Sigma]), x > 0}}, 0], PDF[LogNormalDistribution[\[Mu],\[Sigma]],x]]
    ]
};
