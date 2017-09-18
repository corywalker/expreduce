(* ::Package:: *)

(* ::Section:: *)
(*1.1.3 General Binomial Product Integration Rules*)


(* ::Subsection::Closed:: *)
(*1.1.3.1 (a+b x^n)^p*)


Int[(b_.*x_^n_)^p_,x_Symbol] :=
  b^IntPart[p]*(b*x^n)^FracPart[p]/x^(n*FracPart[p])*Int[x^(n*p),x] /;
FreeQ[{b,n,p},x]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,p},x] && FractionQ[n] && IntegerQ[1/n]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*(a+b*x^n)^(p+1)/a /;
FreeQ[{a,b,n,p},x] && EqQ[1/n+p+1,0]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -x*(a+b*x^n)^(p+1)/(a*n*(p+1)) +
  (n*(p+1)+1)/(a*n*(p+1))*Int[(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,n,p},x] && ILtQ[Simplify[1/n+p+1],0] && NeQ[p,-1]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[x^(n*p)*(b+a*x^(-n))^p,x] /;
FreeQ[{a,b},x] && LtQ[n,0] && IntegerQ[p]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^p,x],x] /;
FreeQ[{a,b},x] && IGtQ[n,0] && IGtQ[p,0]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*(a+b*x^n)^p/(n*p+1) +
  a*n*p/(n*p+1)*Int[(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && IGtQ[n,0] && GtQ[p,0] && 
  (IntegerQ[2*p] || n==2 && IntegerQ[4*p] || n==2 && IntegerQ[3*p] || Denominator[p+1/n]<Denominator[p])


Int[1/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
  2/(a^(5/4)*Rt[b/a,2])*EllipticE[1/2*ArcTan[Rt[b/a,2]*x],2] /;
FreeQ[{a,b},x] && PosQ[b/a] && PositiveQ[a]


Int[1/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
  (1+b*x^2/a)^(1/4)/(a*(a+b*x^2)^(1/4))*Int[1/(1+b*x^2/a)^(5/4),x] /;
FreeQ[{a,b},x] && PosQ[b/a] && Not[PositiveQ[a]]


Int[1/(a_+b_.*x_^2)^(7/6),x_Symbol] :=
  1/((a +b*x^2)^(2/3)*(a/(a+b*x^2))^(2/3))*Subst[Int[1/(1-b*x^2)^(1/3),x],x,x/Sqrt[a+b*x^2]] /;
FreeQ[{a,b},x]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -x*(a+b*x^n)^(p+1)/(a*n*(p+1)) +
  (n*(p+1)+1)/(a*n*(p+1))*Int[(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && IGtQ[n,0] && LtQ[p,-1] && 
  (IntegerQ[2*p] || n==2 && IntegerQ[4*p] || n==2 && IntegerQ[3*p] || Denominator[p+1/n]<Denominator[p])


Int[1/(a_+b_.*x_^3),x_Symbol] :=
  1/(3*Rt[a,3]^2)*Int[1/(Rt[a,3]+Rt[b,3]*x),x] + 
  1/(3*Rt[a,3]^2)*Int[(2*Rt[a,3]-Rt[b,3]*x)/(Rt[a,3]^2-Rt[a,3]*Rt[b,3]*x+Rt[b,3]^2*x^2),x] /;
FreeQ[{a,b},x]


(* Int[1/(a_+b_.*x_^5),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,5]], s=Denominator[Rt[a/b,5]]},
  r/(5*a)*Int[1/(r+s*x),x] + 
  2*r/(5*a)*Int[(r-1/4*(1-Sqrt[5])*s*x)/(r^2-1/2*(1-Sqrt[5])*r*s*x+s^2*x^2),x] + 
  2*r/(5*a)*Int[(r-1/4*(1+Sqrt[5])*s*x)/(r^2-1/2*(1+Sqrt[5])*r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b},x] && PosQ[a/b] *)


(* Int[1/(a_+b_.*x_^5),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,5]], s=Denominator[Rt[-a/b,5]]},
  r/(5*a)*Int[1/(r-s*x),x] + 
  2*r/(5*a)*Int[(r+1/4*(1-Sqrt[5])*s*x)/(r^2+1/2*(1-Sqrt[5])*r*s*x+s^2*x^2),x] + 
  2*r/(5*a)*Int[(r+1/4*(1+Sqrt[5])*s*x)/(r^2+1/2*(1+Sqrt[5])*r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b},x] && NegQ[a/b] *)


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
  u=Int[(r-s*Cos[(2*k-1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  r/(a*n)*Int[1/(r+s*x),x] + Dist[2*r/(a*n),Sum[u,{k,1,(n-1)/2}],x]] /;
FreeQ[{a,b},x] && IGtQ[(n-3)/2,0] && PosQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
  u=Int[(r+s*Cos[(2*k-1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  r/(a*n)*Int[1/(r-s*x),x] + Dist[2*r/(a*n),Sum[u,{k,1,(n-1)/2}],x]] /;
FreeQ[{a,b},x] && IGtQ[(n-3)/2,0] && NegQ[a/b]


Int[1/(a_+b_.*x_^2),x_Symbol] :=
  1/(Rt[a,2]*Rt[b,2])*ArcTan[Rt[b,2]*x/Rt[a,2]] /;
FreeQ[{a,b},x] && PosQ[a/b] && (PositiveQ[a] || PositiveQ[b])


Int[1/(a_+b_.*x_^2),x_Symbol] :=
  -1/(Rt[-a,2]*Rt[-b,2])*ArcTan[Rt[-b,2]*x/Rt[-a,2]] /;
FreeQ[{a,b},x] && PosQ[a/b] && (NegativeQ[a] || NegativeQ[b])


Int[1/(a_+b_.*x_^2),x_Symbol] :=
(*Rt[b/a,2]/b*ArcTan[Rt[b/a,2]*x] /; *)
  Rt[a/b,2]/a*ArcTan[x/Rt[a/b,2]] /;
FreeQ[{a,b},x] && PosQ[a/b]


Int[1/(a_+b_.*x_^2),x_Symbol] :=
  1/(Rt[a,2]*Rt[-b,2])*ArcTanh[Rt[-b,2]*x/Rt[a,2]] /;
FreeQ[{a,b},x] && NegQ[a/b] && (PositiveQ[a] || NegativeQ[b])


Int[1/(a_+b_.*x_^2),x_Symbol] :=
  -1/(Rt[-a,2]*Rt[b,2])*ArcTanh[Rt[b,2]*x/Rt[-a,2]] /;
FreeQ[{a,b},x] && NegQ[a/b] && (NegativeQ[a] || PositiveQ[b])


Int[1/(a_+b_.*x_^2),x_Symbol] :=
(*-Rt[-b/a,2]/b*ArcTanh[Rt[-b/a,2]*x] /; *)
  Rt[-a/b,2]/a*ArcTanh[x/Rt[-a/b,2]] /;
FreeQ[{a,b},x] && NegQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u, v},
  u=Int[(r-s*Cos[(2*k-1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x] + 
    Int[(r+s*Cos[(2*k-1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  2*r^2/(a*n)*Int[1/(r^2+s^2*x^2),x] + Dist[2*r/(a*n),Sum[u,{k,1,(n-2)/4}],x]] /;
FreeQ[{a,b},x] && IGtQ[(n-2)/4,0] && PosQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
  u=Int[(r-s*Cos[(2*k*Pi)/n]*x)/(r^2-2*r*s*Cos[(2*k*Pi)/n]*x+s^2*x^2),x] + 
    Int[(r+s*Cos[(2*k*Pi)/n]*x)/(r^2+2*r*s*Cos[(2*k*Pi)/n]*x+s^2*x^2),x];
  2*r^2/(a*n)*Int[1/(r^2-s^2*x^2),x] + Dist[2*r/(a*n),Sum[u,{k,1,(n-2)/4}],x]] /;
FreeQ[{a,b},x] && IGtQ[(n-2)/4,0] && NegQ[a/b]


Int[1/(a_+b_.*x_^4),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,2]], s=Denominator[Rt[a/b,2]]},
  1/(2*r)*Int[(r-s*x^2)/(a+b*x^4),x] + 1/(2*r)*Int[(r+s*x^2)/(a+b*x^4),x]] /;
FreeQ[{a,b},x] && (PositiveQ[a/b] || PosQ[a/b] && AtomQ[SplitProduct[SumBaseQ,a]] && AtomQ[SplitProduct[SumBaseQ,b]])


Int[1/(a_+b_.*x_^4),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  r/(2*a)*Int[1/(r-s*x^2),x] + r/(2*a)*Int[1/(r+s*x^2),x]] /;
FreeQ[{a,b},x] && Not[PositiveQ[a/b]]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,4]], s=Denominator[Rt[a/b,4]]},
  r/(2*Sqrt[2]*a)*Int[(Sqrt[2]*r-s*x^(n/4))/(r^2-Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x] + 
  r/(2*Sqrt[2]*a)*Int[(Sqrt[2]*r+s*x^(n/4))/(r^2+Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x]] /;
FreeQ[{a,b},x] && IGtQ[n/4,1] && PositiveQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  r/(2*a)*Int[1/(r-s*x^(n/2)),x] + r/(2*a)*Int[1/(r+s*x^(n/2)),x]] /;
FreeQ[{a,b},x] && IGtQ[n/4,1] && Not[PositiveQ[a/b]]


Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
  ArcSinh[Rt[b,2]*x/Sqrt[a]]/Rt[b,2] /;
FreeQ[{a,b},x] && PositiveQ[a] && PosQ[b]


Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
  ArcSin[Rt[-b,2]*x/Sqrt[a]]/Rt[-b,2] /;
FreeQ[{a,b},x] && PositiveQ[a] && NegQ[b]


Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
  Subst[Int[1/(1-b*x^2),x],x,x/Sqrt[a+b*x^2]] /;
FreeQ[{a,b},x] && Not[PositiveQ[a]]


(* Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{q=Rt[b/a,3]},
  -Sqrt[2]*(1+Sqrt[3])*(1+Sqrt[3]+q*x)^2*Sqrt[(1+q^3*x^3)/(1+Sqrt[3]+q*x)^4]/(3^(1/4)*q*Sqrt[a+b*x^3])*
    EllipticF[ArcSin[(-1+Sqrt[3]-q*x)/(1+Sqrt[3]+q*x)],-7-4*Sqrt[3]]] /;
FreeQ[{a,b},x] && PosQ[a] *)


(* Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{q=Rt[a/b,3]},
  2*Sqrt[2+Sqrt[3]]*(q+x)*Sqrt[(q^2-q*x+x^2)/((1+Sqrt[3])*q+x)^2]/
    (3^(1/4)*Sqrt[a+b*x^3]*Sqrt[q*(q+x)/((1+Sqrt[3])*q+x)^2])*
    EllipticF[ArcSin[((1-Sqrt[3])*q+x)/((1+Sqrt[3])*q+x)],-7-4*Sqrt[3]]] /;
FreeQ[{a,b},x] && PosQ[a] && EqQ[b^2,1] *)


(* Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{q=Rt[b/a,3]},
  -2*Sqrt[2+Sqrt[3]]*(1+q*x)*Sqrt[(1-q*x+q^2*x^2)/(1+Sqrt[3]+q*x)^2]/
    (3^(1/4)*q*Sqrt[a+b*x^3]*Sqrt[(1+q*x)/(1+Sqrt[3]+q*x)^2])*
    EllipticF[ArcSin[(-1+Sqrt[3]-q*x)/(1+Sqrt[3]+q*x)],-7-4*Sqrt[3]]] /;
FreeQ[{a,b},x] && PosQ[a] *)


Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  2*Sqrt[2+Sqrt[3]]*(s+r*x)*Sqrt[(s^2-r*s*x+r^2*x^2)/((1+Sqrt[3])*s+r*x)^2]/
    (3^(1/4)*r*Sqrt[a+b*x^3]*Sqrt[s*(s+r*x)/((1+Sqrt[3])*s+r*x)^2])*
    EllipticF[ArcSin[((1-Sqrt[3])*s+r*x)/((1+Sqrt[3])*s+r*x)],-7-4*Sqrt[3]]] /;
FreeQ[{a,b},x] && PosQ[a]


(* Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{q=Rt[a/b,3]},
  2*Sqrt[2-Sqrt[3]]*(q+x)*Sqrt[(q^2-q*x+x^2)/((1-Sqrt[3])*q+x)^2]/
    (3^(1/4)*Sqrt[a+b*x^3]*Sqrt[-q*(q+x)/((1-Sqrt[3])*q+x)^2])*
    EllipticF[ArcSin[((1+Sqrt[3])*q+x)/((1-Sqrt[3])*q+x)],-7+4*Sqrt[3]]] /;
FreeQ[{a,b},x] && NegQ[a] && EqQ[b^2,1] *)


(* Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{q=Rt[b/a,3]},
  -2*Sqrt[2-Sqrt[3]]*(1+q*x)*Sqrt[(1-q*x+q^2*x^2)/(1-Sqrt[3]+q*x)^2]/
    (3^(1/4)*q*Sqrt[a+b*x^3]*Sqrt[-(1+q*x)/(1-Sqrt[3]+q*x)^2])*
    EllipticF[ArcSin[(1+Sqrt[3]+q*x)/(-1+Sqrt[3]-q*x)],-7+4*Sqrt[3]]] /;
FreeQ[{a,b},x] && NegQ[a] *)


Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  2*Sqrt[2-Sqrt[3]]*(s+r*x)*Sqrt[(s^2-r*s*x+r^2*x^2)/((1-Sqrt[3])*s+r*x)^2]/
    (3^(1/4)*r*Sqrt[a+b*x^3]*Sqrt[-s*(s+r*x)/((1-Sqrt[3])*s+r*x)^2])*
    EllipticF[ArcSin[((1+Sqrt[3])*s+r*x)/((1-Sqrt[3])*s+r*x)],-7+4*Sqrt[3]]] /;
FreeQ[{a,b},x] && NegQ[a]


Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  With[{q=Rt[b/a,4]},
  (1+q^2*x^2)*Sqrt[(a+b*x^4)/(a*(1+q^2*x^2)^2)]/(2*q*Sqrt[a+b*x^4])*EllipticF[2*ArcTan[q*x],1/2]] /;
FreeQ[{a,b},x] && PosQ[b/a]


Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  EllipticF[ArcSin[Rt[-b,4]*x/Rt[a,4]],-1]/(Rt[a,4]*Rt[-b,4]) /;
FreeQ[{a,b},x] && NegQ[b/a] && PositiveQ[a]


Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*b,2]},
  Sqrt[-a+q*x^2]*Sqrt[(a+q*x^2)/q]/(Sqrt[2]*Sqrt[-a]*Sqrt[a+b*x^4])*
    EllipticF[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2] /;
  IntegerQ[q]] /;
FreeQ[{a,b},x] && NegativeQ[a] && PositiveQ[b]


Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*b,2]},
  Sqrt[(a-q*x^2)/(a+q*x^2)]*Sqrt[(a+q*x^2)/q]/(Sqrt[2]*Sqrt[a+b*x^4]*Sqrt[a/(a+q*x^2)])*
    EllipticF[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2]] /;
FreeQ[{a,b},x] && NegativeQ[a] && PositiveQ[b]


Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  Sqrt[1+b*x^4/a]/Sqrt[a+b*x^4]*Int[1/Sqrt[1+b*x^4/a],x] /;
FreeQ[{a,b},x] && NegQ[b/a] && Not[PositiveQ[a]]


Int[1/Sqrt[a_+b_.*x_^6],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  x*(s+r*x^2)*Sqrt[(s^2-r*s*x^2+r^2*x^4)/(s+(1+Sqrt[3])*r*x^2)^2]/
    (2*3^(1/4)*s*Sqrt[a+b*x^6]*Sqrt[r*x^2*(s+r*x^2)/(s+(1+Sqrt[3])*r*x^2)^2])*
    EllipticF[ArcCos[(s+(1-Sqrt[3])*r*x^2)/(s+(1+Sqrt[3])*r*x^2)],(2+Sqrt[3])/4]] /;
FreeQ[{a,b},x]


Int[1/Sqrt[a_+b_.*x_^8],x_Symbol] :=
  1/2*Int[(1-Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] + 
  1/2*Int[(1+Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] /;
FreeQ[{a,b},x]


Int[1/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
  2*x/(a+b*x^2)^(1/4) - a*Int[1/(a+b*x^2)^(5/4),x] /;
FreeQ[{a,b},x] && PosQ[b/a]


Int[1/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
  2/(a^(1/4)*Rt[-b/a,2])*EllipticE[1/2*ArcSin[Rt[-b/a,2]*x],2] /;
FreeQ[{a,b},x] && NegQ[b/a] && PositiveQ[a]


Int[1/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
  (1+b*x^2/a)^(1/4)/(a+b*x^2)^(1/4)*Int[1/(1+b*x^2/a)^(1/4),x] /;
FreeQ[{a,b},x] && NegQ[b/a] && Not[PositiveQ[a]]


Int[1/(a_+b_.*x_^2)^(3/4),x_Symbol] :=
  2/(a^(3/4)*Rt[b/a,2])*EllipticF[1/2*ArcTan[Rt[b/a,2]*x],2] /;
FreeQ[{a,b},x] && PositiveQ[a] && PosQ[b/a]


Int[1/(a_+b_.*x_^2)^(3/4),x_Symbol] :=
  2/(a^(3/4)*Rt[-b/a,2])*EllipticF[1/2*ArcSin[Rt[-b/a,2]*x],2] /;
FreeQ[{a,b},x] && PositiveQ[a] && NegQ[b/a]


Int[1/(a_+b_.*x_^2)^(3/4),x_Symbol] :=
  (1+b*x^2/a)^(3/4)/(a+b*x^2)^(3/4)*Int[1/(1+b*x^2/a)^(3/4),x] /;
FreeQ[{a,b},x] && Not[PositiveQ[a]]


Int[1/(a_+b_.*x_^2)^(1/3),x_Symbol] :=
  3*Sqrt[b*x^2]/(2*b*x)*Subst[Int[x/Sqrt[-a+x^3],x],x,(a+b*x^2)^(1/3)] /;
FreeQ[{a,b},x]


Int[1/(a_+b_.*x_^2)^(2/3),x_Symbol] :=
  3*Sqrt[b*x^2]/(2*b*x)*Subst[Int[1/Sqrt[-a+x^3],x],x,(a+b*x^2)^(1/3)] /;
FreeQ[{a,b},x]


Int[1/(a_+b_.*x_^4)^(3/4),x_Symbol] :=
  x^3*(1+a/(b*x^4))^(3/4)/(a+b*x^4)^(3/4)*Int[1/(x^3*(1+a/(b*x^4))^(3/4)),x] /;
FreeQ[{a,b},x]


Int[1/(a_+b_.*x_^2)^(1/6),x_Symbol] :=
  3*x/(2*(a+b*x^2)^(1/6)) - a/2*Int[1/(a+b*x^2)^(7/6),x] /;
FreeQ[{a,b},x]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  a^(p+1/n)*Subst[Int[1/(1-b*x^n)^(p+1/n+1),x],x,x/(a+b*x^n)^(1/n)] /;
FreeQ[{a,b},x] && IGtQ[n,0] && GtQ[p,-1] && LtQ[p,0] && NeQ[p,-1/2] && IntegerQ[p+1/n]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (a/(a+b*x^n))^(p+1/n)*(a+b*x^n)^(p+1/n)*Subst[Int[1/(1-b*x^n)^(p+1/n+1),x],x,x/(a+b*x^n)^(1/n)] /;
FreeQ[{a,b},x] && IGtQ[n,0] && GtQ[p,-1] && LtQ[p,0] && NeQ[p,-1/2] && Denominator[p+1/n]<Denominator[p]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p/x^2,x],x,1/x] /;
FreeQ[{a,b,p},x] && ILtQ[n,0]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*x^(k*n))^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,p},x] && FractionQ[n]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,n},x] && IGtQ[p,0]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  a^p*x*Hypergeometric2F1[-p,1/n,1/n+1,-b*x^n/a] /;
FreeQ[{a,b,n,p},x] && Not[IGtQ[p,0]] && Not[IntegerQ[1/n]] && Not[ILtQ[Simplify[1/n+p],0]] && 
  (IntegerQ[p] || PositiveQ[a])


(* Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*(a+b*x^n)^(p+1)/a*Hypergeometric2F1[1,1/n+p+1,1/n+1,-b*x^n/a] /;
FreeQ[{a,b,n,p},x] && Not[IGtQ[p,0]] && Not[IntegerQ[1/n]] && Not[ILtQ[Simplify[1/n+p],0]] && 
  Not[IntegerQ[p] || PositiveQ[a]] *)


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^n)^FracPart[p]/(1+b*x^n/a)^FracPart[p]*Int[(1+b*x^n/a)^p,x] /;
FreeQ[{a,b,n,p},x] && Not[IGtQ[p,0]] && Not[IntegerQ[1/n]] && 
  Not[ILtQ[Simplify[1/n+p],0]] && Not[IntegerQ[p] || PositiveQ[a]]


Int[(a_.+b_.*u_^n_)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n)^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a1_.+b1_.*x_^n_)^p_.*(a2_.+b2_.*x_^n_)^p_.,x_Symbol] :=
  Int[(a1*a2+b1*b2*x^(2*n))^p,x] /;
FreeQ[{a1,b1,a2,b2,n,p},x] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[p] || PositiveQ[a1] && PositiveQ[a2])


Int[(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
  x*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(2*n*p+1) + 
  2*a1*a2*n*p/(2*n*p+1)*Int[(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
FreeQ[{a1,b1,a2,b2},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && GtQ[p,0] && (IntegerQ[2*p] || Denominator[p+1/n]<Denominator[p])


Int[(a1_+b1_.*x_^n_.)^p_*(a2_+b2_.*x_^n_.)^p_,x_Symbol] :=
  -x*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*a1*a2*n*(p+1)) + 
  (2*n*(p+1)+1)/(2*a1*a2*n*(p+1))*Int[(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
FreeQ[{a1,b1,a2,b2},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && LtQ[p,-1] && (IntegerQ[2*p] || Denominator[p+1/n]<Denominator[p])


Int[(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  -Subst[Int[(a1+b1*x^(-n))^p*(a2+b2*x^(-n))^p/x^2,x],x,1/x] /;
FreeQ[{a1,b1,a2,b2,p},x] && EqQ[a2*b1+a1*b2,0] && ILtQ[2*n,0]


Int[(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[2*n]},
  k*Subst[Int[x^(k-1)*(a1+b1*x^(k*n))^p*(a2+b2*x^(k*n))^p,x],x,x^(1/k)]] /;
FreeQ[{a1,b1,a2,b2,p},x] && EqQ[a2*b1+a1*b2,0] && FractionQ[2*n]


Int[(a1_.+b1_.*x_^n_)^p_*(a2_.+b2_.*x_^n_)^p_,x_Symbol] :=
  (a1+b1*x^n)^FracPart[p]*(a2+b2*x^n)^FracPart[p]/(a1*a2+b1*b2*x^(2*n))^FracPart[p]*Int[(a1*a2+b1*b2*x^(2*n))^p,x] /;
FreeQ[{a1,b1,a2,b2,n,p},x] && EqQ[a2*b1+a1*b2,0] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*1.1.3.2 (c x)^m (a+b x^n)^p*)


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  Int[(c*x)^m*(a1*a2+b1*b2*x^(2*n))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2] && (IntegerQ[p] || PositiveQ[a1] && PositiveQ[a2])


Int[(c_.*x_)^m_.*(b_.*x_^n_)^p_,x_Symbol] :=
  c^m/(n*b^(Simplify[(m+1)/n]-1))*Subst[Int[(b*x)^(p+Simplify[(m+1)/n]-1),x],x,x^n] /;
FreeQ[{b,c,m,n,p},x] && (IntegerQ[m] || PositiveQ[c]) && IntegerQ[Simplify[(m+1)/n]]


Int[(c_.*x_)^m_.*(b_.*x_^n_.)^p_,x_Symbol] :=
  c^m*b^IntPart[p]*(b*x^n)^FracPart[p]/x^(n*FracPart[p])*Int[x^(m+n*p),x] /;
FreeQ[{b,c,m,n,p},x] && (IntegerQ[m] || PositiveQ[c]) && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[(c_*x_)^m_*(b_.*x_^n_.)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(b*x^n)^p,x] /;
FreeQ[{b,c,m,n,p},x] && Not[IntegerQ[m]]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Log[RemoveContent[a+b*x^n,x]]/(b*n) /;
FreeQ[{a,b,m,n},x] && EqQ[m,n-1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (a+b*x^n)^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && EqQ[m,n-1] && NeQ[p,-1]


Int[x_^m_.*(a1_+b1_.*x_^n_.)^p_*(a2_+b2_.*x_^n_.)^p_,x_Symbol] :=
  (a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*b1*b2*n*(p+1)) /;
FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && EqQ[m,2*n-1] && NeQ[p,-1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[x^(m+n*p)*(b+a*x^(-n))^p,x] /;
FreeQ[{a,b,m,n},x] && IntegerQ[p] && NegQ[n]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[(m+1)/n+p+1] && NeQ[m+1]


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(a1*a2*c*(m+1)) /;
FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2] && EqQ[(m+1)/(2*n)+p+1] && NeQ[m+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a1+b1*x)^p*(a2+b2*x)^p,x],x,x^n] /;
FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2] && IntegerQ[Simplify[(m+1)/(2*n)]]


Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2] && IntegerQ[Simplify[(m+1)/(2*n)]]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n)^(p+1)/(a*(m+1)) - 
  b*(m+n*(p+1)+1)/(a*(m+1))*Int[x^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,m,n,p},x] && NegativeIntegerQ[Simplify[(m+1)/n+p+1]] && NeQ[m+1]


Int[x_^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  x^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(a1*a2*(m+1)) - 
  b1*b2*(m+2*n*(p+1)+1)/(a1*a2*(m+1))*Int[x^(m+2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2] && NegativeIntegerQ[Simplify[(m+1)/(2*n)+p+1]] && NeQ[m+1]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*n*(p+1)) +
  (m+n*(p+1)+1)/(a*n*(p+1))*Int[(c*x)^m*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,m,n,p},x] && NegativeIntegerQ[Simplify[(m+1)/n+p+1]] && NeQ[p+1]


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*a1*a2*c*n*(p+1)) +
  (m+2*n*(p+1)+1)/(2*a1*a2*n*(p+1))*Int[(c*x)^m*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2] && NegativeIntegerQ[Simplify[(m+1)/(2*n)+p+1]] && NeQ[p+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k))^p,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,b,p},x] && PositiveIntegerQ[n] && IntegerQ[m]


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  With[{k=GCD[m+1,2*n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(a1+b1*x^(n/k))^p*(a2+b2*x^(n/k))^p,x],x,x^k] /;
 k!=1] /;
FreeQ[{a1,b1,a2,b2,p},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && IntegerQ[m]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+1)) - 
  b*n*p/(c^n*(m+1))*Int[(c*x)^(m+n)*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-1 && Not[NegativeIntegerQ[(m+n*p+n+1)/n]] && 
  IntBinomialQ[a,b,c,n,m,p,x]


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(c*(m+1)) - 
  2*b1*b2*n*p/(c^(2*n)*(m+1))*Int[(c*x)^(m+2*n)*(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
FreeQ[{a1,b1,a2,b2,c,m},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && RationalQ[m,p] && p>0 && NeQ[m+2*n*p+1] && 
  IntBinomialQ[a1*a2,b1*b2,c,n,m,p,x]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+n*p+1)) +
  a*n*p/(m+n*p+1)*Int[(c*x)^m*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c,m},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && NeQ[m+n*p+1] && IntBinomialQ[a,b,c,n,m,p,x]


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(c*(m+2*n*p+1)) + 
  2*a1*a2*n*p/(m+2*n*p+1)*Int[(c*x)^m*(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
FreeQ[{a1,b1,a2,b2,c,m},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && RationalQ[m,p] && p>0 && NeQ[m+2*n*p+1] && 
  IntBinomialQ[a1*a2,b1*b2,c,n,m,p,x]


Int[x_^2/(a_+b_.*x_^4)^(5/4),x_Symbol] :=
  x*(1+a/(b*x^4))^(1/4)/(b*(a+b*x^4)^(1/4))*Int[1/(x^3*(1+a/(b*x^4))^(5/4)),x] /;
FreeQ[{a,b},x] && PosQ[b/a]


Int[x_^m_/(a_+b_.*x_^4)^(5/4),x_Symbol] :=
  x^(m-3)/(b*(m-4)*(a+b*x^4)^(1/4)) - a*(m-3)/(b*(m-4))*Int[x^(m-4)/(a+b*x^4)^(5/4),x] /;
FreeQ[{a,b},x] && PosQ[b/a] && PositiveIntegerQ[(m-2)/4]


Int[x_^m_/(a_+b_.*x_^4)^(5/4),x_Symbol] :=
  x^(m+1)/(a*(m+1)*(a+b*x^4)^(1/4)) - b*m/(a*(m+1))*Int[x^(m+4)/(a+b*x^4)^(5/4),x] /;
FreeQ[{a,b},x] && PosQ[b/a] && NegativeIntegerQ[(m-2)/4]


Int[Sqrt[c_.*x_]/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
  Sqrt[c*x]*(1+a/(b*x^2))^(1/4)/(b*(a+b*x^2)^(1/4))*Int[1/(x^2*(1+a/(b*x^2))^(5/4)),x] /;
FreeQ[{a,b,c},x] && PosQ[b/a]


Int[(c_.*x_)^m_/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
  2*c*(c*x)^(m-1)/(b*(2*m-3)*(a+b*x^2)^(1/4)) - 2*a*c^2*(m-1)/(b*(2*m-3))*Int[(c*x)^(m-2)/(a+b*x^2)^(5/4),x] /;
FreeQ[{a,b,c},x] && PosQ[b/a] && IntegerQ[2*m] && m>3/2 


Int[(c_.*x_)^m_/(a_+b_.*x_^2)^(5/4),x_Symbol] :=
  (c*x)^(m+1)/(a*c*(m+1)*(a+b*x^2)^(1/4)) - b*(2*m+1)/(2*a*c^2*(m+1))*Int[(c*x)^(m+2)/(a+b*x^2)^(5/4),x] /;
FreeQ[{a,b,c},x] && PosQ[b/a] && IntegerQ[2*m] && m<-1


Int[x_^2/(a_+b_.*x_^4)^(5/4),x_Symbol] :=
  -1/(b*x*(a+b*x^4)^(1/4)) - 1/b*Int[1/(x^2*(a+b*x^4)^(1/4)),x] /;
FreeQ[{a,b},x] && NegQ[b/a]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*n*(p+1)) -
  c^n*(m-n+1)/(b*n*(p+1))*Int[(c*x)^(m-n)*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m+1>n && 
  Not[NegativeIntegerQ[(m+n*(p+1)+1)/n]] && IntBinomialQ[a,b,c,n,m,p,x]


(* Int[(c_.*x_)^m_.*u_^p_*v_^p_,x_Symbol] :=
  With[{a=BinomialParts[u,x][[1]],b=BinomialParts[u,x][[2]],n=BinomialParts[u,x][[3]]},
  c^(n-1)*(c*x)^(m-n+1)*u^(p+1)*v^(p+1)/(b*n*(p+1)) -
  c^n*(m-n+1)/(b*n*(p+1))*Int[(c*x)^(m-n)*u^(p+1)*v^(p+1),x] /;
 PositiveIntegerQ[n] && m+1>n && Not[NegativeIntegerQ[(m+n*(p+1)+1)/n]] && 
   IntBinomialQ[a,b,c,n,m,p,x]] /;
FreeQ[c,x] && BinomialQ[u*v,x] && RationalQ[m,p] && p<-1 *)


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  c^(2*n-1)*(c*x)^(m-2*n+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*b1*b2*n*(p+1)) - 
  c^(2*n)*(m-2*n+1)/(2*b1*b2*n*(p+1))*Int[(c*x)^(m-2*n)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
FreeQ[{a1,b1,a2,b2,c},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && RationalQ[m,p] && p<-1 && m+1>2*n && 
  Not[NegativeIntegerQ[(m+2*n*(p+1)+1)/(2*n)]] && IntBinomialQ[a1*a2,b1*b2,c,n,m,p,x]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*n*(p+1)) +
  (m+n*(p+1)+1)/(a*n*(p+1))*Int[(c*x)^m*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,m},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && IntBinomialQ[a,b,c,n,m,p,x]


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*a1*a2*c*n*(p+1)) + 
  (m+2*n*(p+1)+1)/(2*a1*a2*n*(p+1))*Int[(c*x)^m*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
FreeQ[{a1,b1,a2,b2,c,m},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && RationalQ[m,p] && p<-1 && 
  IntBinomialQ[a1*a2,b1*b2,c,n,m,p,x]


Int[x_/(a_+b_.*x_^3),x_Symbol] :=
  -1/(3*Rt[a,3]*Rt[b,3])*Int[1/(Rt[a,3]+Rt[b,3]*x),x] + 
  1/(3*Rt[a,3]*Rt[b,3])*Int[(Rt[a,3]+Rt[b,3]*x)/(Rt[a,3]^2-Rt[a,3]*Rt[b,3]*x+Rt[b,3]^2*x^2),x] /;
FreeQ[{a,b},x]


(* Int[x_^m_./(a_+b_.*x_^5),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,5]], s=Denominator[Rt[a/b,5]]},
  (-1)^m*r^(m+1)/(5*a*s^m)*Int[1/(r+s*x),x] + 
  2*r^(m+1)/(5*a*s^m)*Int[(r*Cos[m*Pi/5]-s*Cos[(m+1)*Pi/5]*x)/(r^2-1/2*(1+Sqrt[5])*r*s*x+s^2*x^2),x] + 
  2*r^(m+1)/(5*a*s^m)*Int[(r*Cos[3*m*Pi/5]-s*Cos[3*(m+1)*Pi/5]*x)/(r^2-1/2*(1-Sqrt[5])*r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m] && m<4 && PosQ[a/b] *)


(* Int[x_^m_./(a_+b_.*x_^5),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,5]], s=Denominator[Rt[-a/b,5]]},
  (r^(m+1)/(5*a*s^m))*Int[1/(r-s*x),x] + 
  2*(-1)^m*r^(m+1)/(5*a*s^m)*Int[(r*Cos[m*Pi/5]+s*Cos[(m+1)*Pi/5]*x)/(r^2+1/2*(1+Sqrt[5])*r*s*x+s^2*x^2),x] + 
  2*(-1)^m*r^(m+1)/(5*a*s^m)*Int[(r*Cos[3*m*Pi/5]+s*Cos[3*(m+1)*Pi/5]*x)/(r^2+1/2*(1-Sqrt[5])*r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m] && m<4 && NegQ[a/b] *)


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
  u=Int[(r*Cos[(2*k-1)*m*Pi/n]-s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  -(-r)^(m+1)/(a*n*s^m)*Int[1/(r+s*x),x] + Dist[2*r^(m+1)/(a*n*s^m),Sum[u,{k,1,(n-1)/2}],x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[(n-1)/2] && PositiveIntegerQ[m] && m<n-1 && PosQ[a/b]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
  u=Int[(r*Cos[(2*k-1)*m*Pi/n]+s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  r^(m+1)/(a*n*s^m)*Int[1/(r-s*x),x] - Dist[2*(-r)^(m+1)/(a*n*s^m),Sum[u,{k,1,(n-1)/2}],x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,(n-1)/2] && PositiveIntegerQ[m] && m<n-1 && NegQ[a/b]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
  u=Int[(r*Cos[(2*k-1)*m*Pi/n]-s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x] + 
    Int[(r*Cos[(2*k-1)*m*Pi/n]+s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  2*(-1)^(m/2)*r^(m+2)/(a*n*s^m)*Int[1/(r^2+s^2*x^2),x] + Dist[2*r^(m+1)/(a*n*s^m),Sum[u,{k,1,(n-2)/4}],x]] /;
 FreeQ[{a,b},x] && PositiveIntegerQ[m,(n-2)/4] && PositiveIntegerQ[m] && m<n-1 && PosQ[a/b]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
  u=Int[(r*Cos[2*k*m*Pi/n]-s*Cos[2*k*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[2*k*Pi/n]*x+s^2*x^2),x] + 
    Int[(r*Cos[2*k*m*Pi/n]+s*Cos[2*k*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[2*k*Pi/n]*x+s^2*x^2),x];
  2*r^(m+2)/(a*n*s^m)*Int[1/(r^2-s^2*x^2),x] + Dist[2*r^(m+1)/(a*n*s^m),Sum[u,{k,1,(n-2)/4}],x]] /;
 FreeQ[{a,b},x] && PositiveIntegerQ[m,(n-2)/4] && PositiveIntegerQ[m] && m<n-1 && NegQ[a/b]


Int[x_^2/(a_+b_.*x_^4),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,2]], s=Denominator[Rt[a/b,2]]},
  1/(2*s)*Int[(r+s*x^2)/(a+b*x^4),x] - 
  1/(2*s)*Int[(r-s*x^2)/(a+b*x^4),x]] /;
FreeQ[{a,b},x] && (PositiveQ[a/b] || PosQ[a/b] && AtomQ[SplitProduct[SumBaseQ,a]] && AtomQ[SplitProduct[SumBaseQ,b]])


Int[x_^2/(a_+b_.*x_^4),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  s/(2*b)*Int[1/(r+s*x^2),x] -
  s/(2*b)*Int[1/(r-s*x^2),x]] /;
FreeQ[{a,b},x] && Not[PositiveQ[a/b]]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,4]], s=Denominator[Rt[a/b,4]]},
  s^3/(2*Sqrt[2]*b*r)*Int[x^(m-n/4)/(r^2-Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x] -
  s^3/(2*Sqrt[2]*b*r)*Int[x^(m-n/4)/(r^2+Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,n/4] && PositiveIntegerQ[m] && m<n-1 && PositiveQ[a/b]


Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  r/(2*a)*Int[x^m/(r+s*x^(n/2)),x] +
  r/(2*a)*Int[x^m/(r-s*x^(n/2)),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,n/4] && PositiveIntegerQ[m] && m<n/2 && Not[PositiveQ[a/b]]


Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  s/(2*b)*Int[x^(m-n/2)/(r+s*x^(n/2)),x] -
  s/(2*b)*Int[x^(m-n/2)/(r-s*x^(n/2)),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,n/4] && PositiveIntegerQ[m] && n/2<=m<n && Not[PositiveQ[a/b]]


Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
  Int[PolynomialDivide[x^m,(a+b*x^n),x],x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,n] && m>2*n-1


Int[x_/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  Sqrt[2]*s/(Sqrt[2+Sqrt[3]]*r)*Int[1/Sqrt[a+b*x^3],x] + 1/r*Int[((1-Sqrt[3])*s+r*x)/Sqrt[a+b*x^3],x]] /;
FreeQ[{a,b},x] && PosQ[a]


Int[x_/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  -Sqrt[2]*s/(Sqrt[2-Sqrt[3]]*r)*Int[1/Sqrt[a+b*x^3],x] + 1/r*Int[((1+Sqrt[3])*s+r*x)/Sqrt[a+b*x^3],x]] /;
FreeQ[{a,b},x] && NegQ[a]


Int[x_^2/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  With[{q=Rt[b/a,2]},
  1/q*Int[1/Sqrt[a+b*x^4],x] - 1/q*Int[(1-q*x^2)/Sqrt[a+b*x^4],x]] /;
FreeQ[{a,b},x] && PosQ[b/a]


Int[x_^2/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  With[{q=Rt[-b/a,2]},
  1/q*Int[1/Sqrt[a+b*x^4],x] - 1/q*Int[(1-q*x^2)/Sqrt[a+b*x^4],x]] /;
FreeQ[{a,b},x] && NegativeQ[a] && PositiveQ[b]


Int[x_^2/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  With[{q=Rt[-b/a,2]},
  -1/q*Int[1/Sqrt[a+b*x^4],x] + 1/q*Int[(1+q*x^2)/Sqrt[a+b*x^4],x]] /;
FreeQ[{a,b},x] && NegQ[b/a]


Int[x_^4/Sqrt[a_+b_.*x_^6],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  (Sqrt[3]-1)*s^2/(2*r^2)*Int[1/Sqrt[a+b*x^6],x] - 1/(2*r^2)*Int[((Sqrt[3]-1)*s^2-2*r^2*x^4)/Sqrt[a+b*x^6],x]] /;
FreeQ[{a,b},x]


(* Int[x_^4/Sqrt[a_+b_.*x_^6],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  (1+Sqrt[3])*r*x*Sqrt[a+b*x^6]/(2*b*(s+(1+Sqrt[3])*r*x^2)) - 
  3^(1/4)*s*x*(s+r*x^2)*Sqrt[(s^2-r*s*x^2+r^2*x^4)/(s+(1+Sqrt[3])*r*x^2)^2]/
    (2*r^2*Sqrt[a+b*x^6]*Sqrt[r*x^2*(s+r*x^2)/(s+(1+Sqrt[3])*r*x^2)^2])*
    EllipticE[ArcCos[(s+(1-Sqrt[3])*r*x^2)/(s+(1+Sqrt[3])*r*x^2)],(2+Sqrt[3])/4] - 
  (1-Sqrt[3])*s*x*(s+r*x^2)*Sqrt[(s^2-r*s*x^2+r^2*x^4)/(s+(1+Sqrt[3])*r*x^2)^2]/
    (4*3^(1/4)*r^2*Sqrt[a+b*x^6]*Sqrt[r*x^2*(s+r*x^2)/(s+(1+Sqrt[3])*r*x^2)^2])*
    EllipticF[ArcCos[(s+(1-Sqrt[3])*r*x^2)/(s+(1+Sqrt[3])*r*x^2)],(2+Sqrt[3])/4]] /;
FreeQ[{a,b},x] *)


Int[x_^2/Sqrt[a_+b_.*x_^8],x_Symbol] :=
  1/(2*Rt[b/a,4])*Int[(1+Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] - 
  1/(2*Rt[b/a,4])*Int[(1-Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] /;
FreeQ[{a,b},x]


Int[x_^2/(a_+b_.*x_^4)^(1/4),x_Symbol] :=
  x^3/(2*(a+b*x^4)^(1/4)) - a/2*Int[x^2/(a+b*x^4)^(5/4),x] /;
FreeQ[{a,b},x] && PosQ[b/a]


Int[x_^2/(a_+b_.*x_^4)^(1/4),x_Symbol] :=
  (a+b*x^4)^(3/4)/(2*b*x) + a/(2*b)*Int[1/(x^2*(a+b*x^4)^(1/4)),x] /;
FreeQ[{a,b},x] && NegQ[b/a]


Int[1/(x_^2*(a_+b_.*x_^4)^(1/4)),x_Symbol] :=
  -1/(x*(a+b*x^4)^(1/4)) - b*Int[x^2/(a+b*x^4)^(5/4),x] /;
FreeQ[{a,b},x] && PosQ[b/a]


Int[1/(x_^2*(a_+b_.*x_^4)^(1/4)),x_Symbol] :=
  x*(1+a/(b*x^4))^(1/4)/(a+b*x^4)^(1/4)*Int[1/(x^3*(1+a/(b*x^4))^(1/4)),x] /;
FreeQ[{a,b},x] && NegQ[b/a]


Int[Sqrt[c_*x_]/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
  x*Sqrt[c*x]/(a+b*x^2)^(1/4) - a/2*Int[Sqrt[c*x]/(a+b*x^2)^(5/4),x] /;
FreeQ[{a,b,c},x] && PosQ[b/a]


Int[Sqrt[c_*x_]/(a_+b_.*x_^2)^(1/4),x_Symbol] :=
  c*(a+b*x^2)^(3/4)/(b*Sqrt[c*x]) + a*c^2/(2*b)*Int[1/((c*x)^(3/2)*(a+b*x^2)^(1/4)),x] /;
FreeQ[{a,b,c},x] && NegQ[b/a]


Int[1/((c_.*x_)^(3/2)*(a_+b_.*x_^2)^(1/4)),x_Symbol] :=
  -2/(c*Sqrt[c*x]*(a+b*x^2)^(1/4)) - b/c^2*Int[Sqrt[c*x]/(a+b*x^2)^(5/4),x] /;
FreeQ[{a,b,c},x] && PosQ[b/a]


Int[1/((c_.*x_)^(3/2)*(a_+b_.*x_^2)^(1/4)),x_Symbol] :=
  Sqrt[c*x]*(1+a/(b*x^2))^(1/4)/(c^2*(a+b*x^2)^(1/4))*Int[1/(x^2*(1+a/(b*x^2))^(1/4)),x] /;
FreeQ[{a,b,c},x] && NegQ[b/a]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*(m+n*p+1)) -
  a*c^n*(m-n+1)/(b*(m+n*p+1))*Int[(c*x)^(m-n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,p},x] && PositiveIntegerQ[n] && RationalQ[m] && m>n-1 && NeQ[m+n*p+1] && IntBinomialQ[a,b,c,n,m,p,x]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*(m+n*p+1)) -
  a*c^n*(m-n+1)/(b*(m+n*p+1))*Int[(c*x)^(m-n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && PositiveIntegerQ[n] && SumSimplerQ[m,-n] && NeQ[m+n*p+1] && NegativeIntegerQ[Simplify[(m+1)/n+p]]


Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  c^(2*n-1)*(c*x)^(m-2*n+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(b1*b2*(m+2*n*p+1)) - 
  a1*a2*c^(2*n)*(m-2*n+1)/(b1*b2*(m+2*n*p+1))*Int[(c*x)^(m-2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,p},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && RationalQ[m] && m>2*n-1 && 
  NeQ[m+2*n*p+1] && IntBinomialQ[a1*a2,b1*b2,c,n,m,p,x]


Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  c^(2*n-1)*(c*x)^(m-2*n+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(b1*b2*(m+2*n*p+1)) - 
  a1*a2*c^(2*n)*(m-2*n+1)/(b1*b2*(m+2*n*p+1))*Int[(c*x)^(m-2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,p},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && SumSimplerQ[m,-2*n] && NeQ[m+2*n*p+1] && 
  NegativeIntegerQ[Simplify[(m+1)/(2*n)+p]]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) -
  b*(m+n*(p+1)+1)/(a*c^n*(m+1))*Int[(c*x)^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,p},x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && IntBinomialQ[a,b,c,n,m,p,x]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) -
  b*(m+n*(p+1)+1)/(a*c^n*(m+1))*Int[(c*x)^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && PositiveIntegerQ[n] && SumSimplerQ[m,n] && NegativeIntegerQ[Simplify[(m+1)/n+p]]


Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(a1*a2*c*(m+1)) - 
  b1*b2*(m+2*n*(p+1)+1)/(a1*a2*c^(2*n)*(m+1))*Int[(c*x)^(m+2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,p},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && RationalQ[m] && m<-1 && 
  IntBinomialQ[a1*a2,b1*b2,c,n,m,p,x]


Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(a1*a2*c*(m+1)) - 
  b1*b2*(m+2*n*(p+1)+1)/(a1*a2*c^(2*n)*(m+1))*Int[(c*x)^(m+2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,p},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && SumSimplerQ[m,2*n] && 
  NegativeIntegerQ[Simplify[(m+1)/(2*n)+p]]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/c*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/c^n)^p,x],x,(c*x)^(1/k)]] /;
FreeQ[{a,b,c,p},x] && PositiveIntegerQ[n] && FractionQ[m] && IntBinomialQ[a,b,c,n,m,p,x]


Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/c*Subst[Int[x^(k*(m+1)-1)*(a1+b1*x^(k*n)/c^n)^p*(a2+b2*x^(k*n)/c^n)^p,x],x,(c*x)^(1/k)]] /;
FreeQ[{a1,b1,a2,b2,c,p},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && FractionQ[m] && IntBinomialQ[a1*a2,b1*b2,c,n,m,p,x]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  a^(p+(m+1)/n)*Subst[Int[x^m/(1-b*x^n)^(p+(m+1)/n+1),x],x,x/(a+b*x^n)^(1/n)] /;
FreeQ[{a,b},x] && PositiveIntegerQ[n] && RationalQ[p] && -1<p<0 && p!=-1/2 && IntegersQ[m,p+(m+1)/n]


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (a1*a2)^(p+(m+1)/(2*n))*
    Subst[Int[x^m/((1-b1*x^n)^(p+(m+1)/(2*n)+1)*(1-b2*x^n)^(p+(m+1)/(2*n)+1)),x],x,
      x/((a1+b1*x^n)^(1/(2*n))*(a2+b2*x^n)^(1/(2*n)))] /;
FreeQ[{a1,b1,a2,b2},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && RationalQ[p] && -1<p<0 && p!=-1/2 && 
  IntegersQ[m,p+(m+1)/(2*n)]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (a/(a+b*x^n))^(p+(m+1)/n)*(a+b*x^n)^(p+(m+1)/n)*Subst[Int[x^m/(1-b*x^n)^(p+(m+1)/n+1),x],x,x/(a+b*x^n)^(1/n)] /;
FreeQ[{a,b},x] && PositiveIntegerQ[n] && RationalQ[p] && -1<p<0 && p!=-1/2 && IntegerQ[m] && 
  Denominator[p+(m+1)/n]<Denominator[p]


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (a1/(a1+b1*x^n))^(p+(m+1)/(2*n))*(a1+b1*x^n)^(p+(m+1)/(2*n))*(a2/(a2+b2*x^n))^(p+(m+1)/(2*n))*(a2+b2*x^n)^(p+(m+1)/(2*n))*
    Subst[Int[x^m/((1-b1*x^n)^(p+(m+1)/(2*n)+1)*(1-b2*x^n)^(p+(m+1)/(2*n)+1)),x],x,
      x/((a1+b1*x^n)^(1/(2*n))*(a2+b2*x^n)^(1/(2*n)))] /;
FreeQ[{a1,b1,a2,b2},x] && EqQ[a2*b1+a1*b2] && PositiveIntegerQ[2*n] && RationalQ[p] && -1<p<0 && p!=-1/2 && 
  IntegerQ[m] && Denominator[p+(m+1)/(2*n)]<Denominator[p]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,p},x] && NegativeIntegerQ[n] && IntegerQ[m]


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  -Subst[Int[(a1+b1*x^(-n))^p*(a2+b2*x^(-n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a1,b1,a2,b2,p},x] && EqQ[a2*b1+a1*b2] && NegativeIntegerQ[2*n] && IntegerQ[m]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/c*Subst[Int[(a+b*c^(-n)*x^(-k*n))^p/x^(k*(m+1)+1),x],x,1/(c*x)^(1/k)]] /;
FreeQ[{a,b,c,p},x] && NegativeIntegerQ[n] && FractionQ[m]


Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/c*Subst[Int[(a1+b1*c^(-n)*x^(-k*n))^p*(a2+b2*c^(-n)*x^(-k*n))^p/x^(k*(m+1)+1),x],x,1/(c*x)^(1/k)]] /;
FreeQ[{a1,b1,a2,b2,c,p},x] && EqQ[a2*b1+a1*b2] && NegativeIntegerQ[2*n] && FractionQ[m]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^m*(x^(-1))^m*Subst[Int[(a+b*x^(-n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,m,p},x] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^m*(x^(-1))^m*Subst[Int[(a1+b1*x^(-n))^p*(a2+b2*x^(-n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a1,b1,a2,b2,c,m,p},x] && EqQ[a2*b1+a1*b2] && NegativeIntegerQ[2*n] && Not[RationalQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n))^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,m,p},x] && FractionQ[n]


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[2*n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a1+b1*x^(k*n))^p*(a2+b2*x^(k*n))^p,x],x,x^(1/k)]] /;
FreeQ[{a1,b1,a2,b2,m,p},x] && EqQ[a2*b1+a1*b2] && FractionQ[2*n]


Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && FractionQ[n]


Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,p},x] && EqQ[a2*b1+a1*b2] && FractionQ[2*n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a1+b1*x^Simplify[n/(m+1)])^p*(a2+b2*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2] && IntegerQ[Simplify[2*n/(m+1)]] && Not[IntegerQ[2*n]]


Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2] && IntegerQ[Simplify[2*n/(m+1)]] && Not[IntegerQ[2*n]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n)^p/(m+1) - 
  b*n*p/(m+1)*Int[x^(m+n)*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b,m,n},x] && EqQ[(m+1)/n+p] && RationalQ[p] && p>0


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  x^(m+1)*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(m+1) - 
  2*b1*b2*n*p/(m+1)*Int[x^(m+n)*(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
FreeQ[{a1,b1,a2,b2,m,n},x] && EqQ[a2*b1+a1*b2] && EqQ[(m+1)/(2*n)+p] && RationalQ[p] && p>0


Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n},x] && EqQ[(m+1)/n+p] && RationalQ[p] && p>0


Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,n},x] && EqQ[a2*b1+a1*b2] && EqQ[(m+1)/(2*n)+p] && RationalQ[p] && p>0


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+n*p+1)) +
  a*n*p/(m+n*p+1)*Int[(c*x)^m*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && p>0 && NeQ[m+n*p+1]


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(c*(m+2*n*p+1)) +
  2*a1*a2*n*p/(m+2*n*p+1)*Int[(c*x)^m*(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
FreeQ[{a1,b1,a2,b2,c,m,n},x] && EqQ[a2*b1+a1*b2] && IntegerQ[p+Simplify[(m+1)/(2*n)]] && RationalQ[p] && p>0 && 
  NeQ[m+2*n*p+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[p]},
  k*a^(p+Simplify[(m+1)/n])/n*
	Subst[Int[x^(k*Simplify[(m+1)/n]-1)/(1-b*x^k)^(p+Simplify[(m+1)/n]+1),x],x,x^(n/k)/(a+b*x^n)^(1/k)]] /;
FreeQ[{a,b,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && -1<p<0


Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  With[{k=Denominator[p]},
  k*(a1*a2)^(p+Simplify[(m+1)/(2*n)])/(2*n)*
	Subst[Int[x^(k*Simplify[(m+1)/(2*n)]-1)/((1-b1*x^k)^(p+Simplify[(m+1)/(2*n)]+1)*(1-b2*x^k)^(p+Simplify[(m+1)/(2*n)]+1)),x],x,
      x^(2*n/k)/((a1+b1*x^n)^(1/k)*(a2+b2*x^n)^(1/k))]] /;
FreeQ[{a1,b1,a2,b2,m,n},x] && EqQ[a2*b1+a1*b2] && IntegerQ[p+Simplify[(m+1)/(2*n)]] && RationalQ[p] && -1<p<0


Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && -1<p<0


Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,n},x] && EqQ[a2*b1+a1*b2] && IntegerQ[p+Simplify[(m+1)/(2*n)]] && RationalQ[p] && -1<p<0


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*n*(p+1)) +
  (m+n*(p+1)+1)/(a*n*(p+1))*Int[(c*x)^m*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && p<-1


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*a1*a2*c*n*(p+1)) +
  (m+2*n*(p+1)+1)/(2*a1*a2*n*(p+1))*Int[(c*x)^m*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
FreeQ[{a1,b1,a2,b2,c,m,n},x] && EqQ[a2*b1+a1*b2] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && p<-1


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  With[{mn=Simplify[m-n]},
  x^(mn+1)/(b*(mn+1)) -
  a/b*Int[x^mn/(a+b*x^n),x]] /;
FreeQ[{a,b,m,n},x] && FractionQ[Simplify[(m+1)/n]] && SumSimplerQ[m,-n]


Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
  x^(m+1)/(a*(m+1)) -
  b/a*Int[x^Simplify[m+n]/(a+b*x^n),x] /;
FreeQ[{a,b,m,n},x] && FractionQ[Simplify[(m+1)/n]] && SumSimplerQ[m,n]


Int[(c_*x_)^m_/(a_+b_.*x_^n_),x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m/(a+b*x^n),x] /;
FreeQ[{a,b,c,m,n},x] && FractionQ[Simplify[(m+1)/n]] && (SumSimplerQ[m,n] || SumSimplerQ[m,-n])


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  a^p*(c*x)^(m+1)/(c*(m+1))*Hypergeometric2F1[-p,(m+1)/n,(m+1)/n+1,-b*x^n/a] /;
FreeQ[{a,b,c,m,n,p},x] && Not[PositiveIntegerQ[p]] && (NegativeIntegerQ[p] || PositiveQ[a])


(* Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1))*Hypergeometric2F1[1,(m+1)/n+p+1,(m+1)/n+1,-b*x^n/a] /;
FreeQ[{a,b,c,m,n,p},x] && Not[PositiveIntegerQ[p]] && Not[NegativeIntegerQ[p] || PositiveQ[a]] *)


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^n)^FracPart[p]/(1+b*x^n/a)^FracPart[p]*Int[(c*x)^m*(1+b*x^n/a)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && Not[PositiveIntegerQ[p]] && Not[NegativeIntegerQ[p] || PositiveQ[a]]


Int[x_^m_.*(a_+b_.*v_^n_)^p_.,x_Symbol] :=
  1/Coefficient[v,x,1]^(m+1)*Subst[Int[SimplifyIntegrand[(x-Coefficient[v,x,0])^m*(a+b*x^n)^p,x],x],x,v] /;
FreeQ[{a,b,n,p},x] && LinearQ[v,x] && IntegerQ[m] && NeQ[v-x]


Int[u_^m_.*(a_+b_.*v_^n_)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n)^p,x],x,v] /;
FreeQ[{a,b,m,n,p},x] && LinearPairQ[u,v,x]


Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
  (a1+b1*x^n)^FracPart[p]*(a2+b2*x^n)^FracPart[p]/(a1*a2+b1*b2*x^(2*n))^FracPart[p]*Int[(c*x)^m*(a1*a2+b1*b2*x^(2*n))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2] && Not[IntegerQ[p]]


(* IntBinomialQ[a,b,c,n,m,p,x] returns True iff (c*x)^m*(a+b*x^n)^p is integrable wrt x in terms of non-hypergeometric functions. *)
IntBinomialQ[a_,b_,c_,n_,m_,p_,x_] :=
  IntegerQ[2*p] || IntegerQ[(m+1)/n+p] || 
  (EqQ[n-2] || EqQ[n-4]) && IntegersQ[2*m,4*p] || 
  EqQ[n-2] && IntegerQ[6*p] && (IntegerQ[m] || IntegerQ[m-p])


(* ::Subsection::Closed:: *)
(*1.1.3.3 (a+b x^n)^p (c+d x^n)^q*)


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && PositiveIntegerQ[p,q]


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  Int[x^(n*(p+q))*(b+a*x^(-n))^p*(d+c*x^(-n))^q,x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && IntegersQ[p,q] && NegQ[n]


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*(a+b*x^(g*n))^p*(c+d*x^(g*n))^q,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && FractionQ[n]


Int[(a_+b_.*x_^n_)^p_/(c_+d_.*x_^n_),x_Symbol] :=
  Subst[Int[1/(c-(b*c-a*d)*x^n),x],x,x/(a+b*x^n)^(1/n)] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[n*p+1] && IntegerQ[n]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  -x*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*n*(p+1)) - 
  c*q/(a*(p+1))*Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1),x] /;
FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+1)+1] && RationalQ[q] && q>0 && NeQ[p+1]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  a^p*x/(c^(p+1)*(c+d*x^n)^(1/n))*Hypergeometric2F1[1/n,-p,1+1/n,-(b*c-a*d)*x^n/(a*(c+d*x^n))] /;
FreeQ[{a,b,c,d,n,q},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+1)+1] && NegativeIntegerQ[p]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  x*(a+b*x^n)^p/(c*(c*(a+b*x^n)/(a*(c+d*x^n)))^p*(c+d*x^n)^(1/n+p))*
    Hypergeometric2F1[1/n,-p,1+1/n,-(b*c-a*d)*x^n/(a*(c+d*x^n))] /;
FreeQ[{a,b,c,d,n,p,q},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+1)+1]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*c) /;
FreeQ[{a,b,c,d,n,p,q},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+2)+1] && EqQ[a*d*(p+1)+b*c*(q+1)]


(* Int[(a1_+b1_.*x_^n2_.)^p_*(a2_+b2_.*x_^n2_.)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)*(c+d*x^n)^(q+1)/(a1*a2*c) /;
FreeQ[{a1,b1,a2,b2,c,d,n,p,q},x] && EqQ[n2-n/2] && EqQ[a2*b1+a1*b2] && EqQ[n*(p+q+2)+1] && EqQ[a1*a2*d*(p+1)+b1*b2*c*(q+1)] *)


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -b*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*n*(p+1)*(b*c-a*d)) + 
  (b*c+n*(p+1)*(b*c-a*d))/(a*n*(p+1)*(b*c-a*d))*Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,n,q},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+2)+1] && (RationalQ[p] && p<-1 || Not[RationalQ[q] && q<-1]) && NeQ[p+1]


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*x*(a+b*x^n)^(p+1)/a /;
FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && EqQ[a*d-b*c*(n*(p+1)+1),0]


Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2) /;
FreeQ[{a1,b1,a2,b2,c,d,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && EqQ[a1*a2*d-b1*b2*c*(n*(p+1)+1),0]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_),x_Symbol] :=
  -(b*c-a*d)*x*(a+b*x^n)^(p+1)/(a*b*n*(p+1)) - 
  (a*d-b*c*(n*(p+1)+1))/(a*b*n*(p+1))*Int[(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && (LtQ[p,-1] || ILtQ[1/n+p,0])


Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  -(b1*b2*c-a1*a2*d)*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*b1*b2*n*(p+1)) - 
  (a1*a2*d-b1*b2*c*(n*(p+1)+1))/(a1*a2*b1*b2*n*(p+1))*Int[(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1),x] /;
FreeQ[{a1,b1,a2,b2,c,d,n},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && (LtQ[p,-1] || ILtQ[1/n+p,0])


Int[(c_+d_.*x_^n_)/(a_+b_.*x_^n_),x_Symbol] :=
  c*x/a - (b*c-a*d)/a*Int[1/(b+a*x^(-n)),x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && RationalQ[n] && n<0


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_),x_Symbol] :=
  d*x*(a+b*x^n)^(p+1)/(b*(n*(p+1)+1)) - 
  (a*d-b*c*(n*(p+1)+1))/(b*(n*(p+1)+1))*Int[(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && NeQ[n*(p+1)+1,0]


Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  d*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(b1*b2*(n*(p+1)+1)) - 
  (a1*a2*d-b1*b2*c*(n*(p+1)+1))/(b1*b2*(n*(p+1)+1))*Int[(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,d,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && NeQ[n*(p+1)+1,0]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Int[PolynomialDivide[(a+b*x^n)^p,(c+d*x^n)^(-q),x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && PositiveIntegerQ[n,p] && NegativeIntegerQ[q] && p>=-q


Int[1/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*x^n),x] - d/(b*c-a*d)*Int[1/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0]


Int[1/((a_+b_.*x_^2)^(1/3)*(c_+d_.*x_^2)),x_Symbol] :=
  Sqrt[3]/(2*c)*Int[1/((a+b*x^2)^(1/3)*(Sqrt[3]-Rt[b/a,2]*x)),x] + 
  Sqrt[3]/(2*c)*Int[1/((a+b*x^2)^(1/3)*(Sqrt[3]+Rt[b/a,2]*x)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+3*a*d] && PosQ[b/a]


Int[1/((a_+b_.*x_^2)^(1/3)*(c_+d_.*x_^2)),x_Symbol] :=
  1/6*Int[(3+Rt[-b/a,2]*x)/((a+b*x^2)^(1/3)*(c+d*x^2)),x] + 
  1/6*Int[(3-Rt[-b/a,2]*x)/((a+b*x^2)^(1/3)*(c+d*x^2)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+3*a*d] && NegQ[b/a]


Int[(a_+b_.*x_^2)^(2/3)/(c_+d_.*x_^2),x_Symbol] :=
  b/d*Int[1/(a+b*x^2)^(1/3),x] - (b*c-a*d)/d*Int[1/((a+b*x^2)^(1/3)*(c+d*x^2)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+3*a*d]


Int[1/((a_+b_.*x_^2)^(1/4)*(c_+d_.*x_^2)),x_Symbol] :=
  Sqrt[-b*x^2/a]/(2*x)*Subst[Int[1/(Sqrt[-b*x/a]*(a+b*x)^(1/4)*(c+d*x)),x],x,x^2] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[1/((a_+b_.*x_^2)^(3/4)*(c_+d_.*x_^2)),x_Symbol] :=
  Sqrt[-b*x^2/a]/(2*x)*Subst[Int[1/(Sqrt[-b*x/a]*(a+b*x)^(3/4)*(c+d*x)),x],x,x^2] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[(a_+b_.*x_^2)^p_./(c_+d_.*x_^2),x_Symbol] :=
  b/d*Int[(a+b*x^2)^(p-1),x] - (b*c-a*d)/d*Int[(a+b*x^2)^(p-1)/(c+d*x^2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && RationalQ[p] && p>0 && (p==1/2 || Denominator[p]==4)


Int[(a_+b_.*x_^2)^p_/(c_+d_.*x_^2),x_Symbol] :=
  b/(b*c-a*d)*Int[(a+b*x^2)^p,x] - d/(b*c-a*d)*Int[(a+b*x^2)^(p+1)/(c+d*x^2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && RationalQ[p] && p<-1 && Denominator[p]==4 && (p==-5/4 || p==-7/4)


Int[Sqrt[a_+b_.*x_^4]/(c_+d_.*x_^4),x_Symbol] :=
  a/c*Subst[Int[1/(1-4*a*b*x^4),x],x,x/Sqrt[a+b*x^4]] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d] && PosQ[a*b]


Int[Sqrt[a_+b_.*x_^4]/(c_+d_.*x_^4),x_Symbol] :=
  With[{q=Rt[-a*b,4]},
  a/(2*c*q)*ArcTan[q*x*(a+q^2*x^2)/(a*Sqrt[a+b*x^4])] + a/(2*c*q)*ArcTanh[q*x*(a-q^2*x^2)/(a*Sqrt[a+b*x^4])]] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d] && NegQ[a*b]


Int[Sqrt[a_+b_.*x_^4]/(c_+d_.*x_^4),x_Symbol] :=
  b/d*Int[1/Sqrt[a+b*x^4],x] - (b*c-a*d)/d*Int[1/(Sqrt[a+b*x^4]*(c+d*x^4)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[(a_+b_.*x_^4)^(1/4)/(c_+d_.*x_^4),x_Symbol] :=
  Sqrt[a+b*x^4]*Sqrt[a/(a+b*x^4)]*Subst[Int[1/(Sqrt[1-b*x^4]*(c-(b*c-a*d)*x^4)),x],x,x/(a+b*x^4)^(1/4)] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[(a_+b_.*x_^4)^p_/(c_+d_.*x_^4),x_Symbol] :=
  b/d*Int[(a+b*x^4)^(p-1),x] - (b*c-a*d)/d*Int[(a+b*x^4)^(p-1)/(c+d*x^4),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && RationalQ[p] && (p==3/4 || p==5/4)


Int[1/(Sqrt[a_+b_.*x_^4]*(c_+d_.*x_^4)),x_Symbol] :=
  1/(2*c)*Int[1/(Sqrt[a+b*x^4]*(1-Rt[-d/c,2]*x^2)),x] + 1/(2*c)*Int[1/(Sqrt[a+b*x^4]*(1+Rt[-d/c,2]*x^2)),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[1/((a_+b_.*x_^4)^(3/4)*(c_+d_.*x_^4)),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*x^4)^(3/4),x] - d/(b*c-a*d)*Int[(a+b*x^4)^(1/4)/(c+d*x^4),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[Sqrt[a_+b_.*x_^2]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  Sqrt[a+b*x^2]/(c*Rt[d/c,2]*Sqrt[c+d*x^2]*Sqrt[c*(a+b*x^2)/(a*(c+d*x^2))])*EllipticE[ArcTan[Rt[d/c,2]*x],1-b*c/(a*d)] /;
FreeQ[{a,b,c,d},x] && PosQ[b/a] && PosQ[d/c]


(* Int[Sqrt[a_+b_.*x_^2]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
  a*Sqrt[c+d*x^2]*Sqrt[(c*(a+b*x^2))/(a*(c+d*x^2))]/(c^2*Rt[d/c,2]*Sqrt[a+b*x^2])*EllipticE[ArcTan[Rt[d/c,2]*x],1-b*c/(a*d)] /;
FreeQ[{a,b,c,d},x] && PosQ[b/a] && PosQ[d/c] *)


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -x*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*n*(p+1)) + 
  1/(a*n*(p+1))*Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(n*(p+1)+1)+d*(n*(p+q+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && RationalQ[p,q] && p<-1 && 0<q<1 && IntBinomialQ[a,b,c,d,n,p,q,x]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (a*d-c*b)*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*b*n*(p+1)) - 
  1/(a*b*n*(p+1))*
    Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-2)*Simp[c*(a*d-c*b*(n*(p+1)+1))+d*(a*d*(n*(q-1)+1)-b*c*(n*(p+q)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && RationalQ[p,q] && p<-1 && q>1 && IntBinomialQ[a,b,c,d,n,p,q,x]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -b*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*n*(p+1)*(b*c-a*d)) + 
  1/(a*n*(p+1)*(b*c-a*d))*
    Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[b*c+n*(p+1)*(b*c-a*d)+d*b*(n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,n,q},x] && NeQ[b*c-a*d,0] && RationalQ[p] && p<-1 && Not[Not[IntegerQ[p]] && IntegerQ[q] && q<-1] && 
  IntBinomialQ[a,b,c,d,n,p,q,x]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && PositiveIntegerQ[n] && IntegersQ[p,q] && p+q>0


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  d*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(b*(n*(p+q)+1)) + 
  1/(b*(n*(p+q)+1))*
    Int[(a+b*x^n)^p*(c+d*x^n)^(q-2)*Simp[c*(b*c*(n*(p+q)+1)-a*d)+d*(b*c*(n*(p+2*q-1)+1)-a*d*(n*(q-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && RationalQ[q] && q>1 && NeQ[n*(p+q)+1] && Not[IntegerQ[p] && p>1] && 
  IntBinomialQ[a,b,c,d,n,p,q,x]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  x*(a+b*x^n)^p*(c+d*x^n)^q/(n*(p+q)+1) + 
  n/(n*(p+q)+1)*Int[(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && RationalQ[p,q] && q>0 && p>0 && IntBinomialQ[a,b,c,d,n,p,q,x]


Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[a+b*x^2]/(a*Rt[d/c,2]*Sqrt[c+d*x^2]*Sqrt[c*(a+b*x^2)/(a*(c+d*x^2))])*EllipticF[ArcTan[Rt[d/c,2]*x],1-b*c/(a*d)] /;
FreeQ[{a,b,c,d},x] && PosQ[d/c] && PosQ[b/a] && Not[SimplerSqrtQ[b/a,d/c]]


(* Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[c+d*x^2]*Sqrt[c*(a+b*x^2)/(a*(c+d*x^2))]/(c*Rt[d/c,2]*Sqrt[a+b*x^2])*EllipticF[ArcTan[Rt[d/c,2]*x],1-b*c/(a*d)] /;
FreeQ[{a,b,c,d},x] && PosQ[d/c] && PosQ[b/a] && Not[SimplerSqrtQ[b/a,d/c]] *)


Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  1/(Sqrt[a]*Sqrt[c]*Rt[-d/c,2])*EllipticF[ArcSin[Rt[-d/c,2]*x],b*c/(a*d)] /;
FreeQ[{a,b,c,d},x] && NegQ[d/c] && PositiveQ[c] && PositiveQ[a] && Not[NegQ[b/a] && SimplerSqrtQ[-b/a,-d/c]]


Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  -1/(Sqrt[c]*Rt[-d/c,2]*Sqrt[a-b*c/d])*EllipticF[ArcCos[Rt[-d/c,2]*x],b*c/(b*c-a*d)] /;
FreeQ[{a,b,c,d},x] && NegQ[d/c] && PositiveQ[c] && PositiveQ[a-b*c/d]


Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[1+d/c*x^2]/Sqrt[c+d*x^2]*Int[1/(Sqrt[a+b*x^2]*Sqrt[1+d/c*x^2]),x] /;
FreeQ[{a,b,c,d},x] && Not[PositiveQ[c]]


Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
  a*Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] + b*Int[x^2/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d},x] && PosQ[d/c] && PosQ[b/a]


Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
  b/d*Int[Sqrt[c+d*x^2]/Sqrt[a+b*x^2],x] - (b*c-a*d)/d*Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d},x] && PosQ[d/c] && NegQ[b/a]


Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[a]/(Sqrt[c]*Rt[-d/c,2])*EllipticE[ArcSin[Rt[-d/c,2]*x],b*c/(a*d)] /;
FreeQ[{a,b,c,d},x] && NegQ[d/c] && PositiveQ[c] && PositiveQ[a]


Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
  -Sqrt[a-b*c/d]/(Sqrt[c]*Rt[-d/c,2])*EllipticE[ArcCos[Rt[-d/c,2]*x],b*c/(b*c-a*d)] /;
FreeQ[{a,b,c,d},x] && NegQ[d/c] && PositiveQ[c] && PositiveQ[a-b*c/d]


Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]/Sqrt[1+b/a*x^2]*Int[Sqrt[1+b/a*x^2]/Sqrt[c+d*x^2],x] /;
FreeQ[{a,b,c,d},x] && NegQ[d/c] && PositiveQ[c] && Not[PositiveQ[a]]


Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[1+d/c*x^2]/Sqrt[c+d*x^2]*Int[Sqrt[a+b*x^2]/Sqrt[1+d/c*x^2],x] /;
FreeQ[{a,b,c,d},x] && NegQ[d/c] && Not[PositiveQ[c]]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
FreeQ[{a,b,c,d,n,q},x] && NeQ[b*c-a*d,0] && PositiveIntegerQ[p]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  a^p*c^q*x*AppellF1[1/n,-p,-q,1+1/n,-b*x^n/a,-d*x^n/c] /;
FreeQ[{a,b,c,d,n,p,q},x] && NeQ[b*c-a*d,0] && NeQ[n+1] && PositiveQ[a] && PositiveQ[c]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^n)^FracPart[p]/(1+b*x^n/a)^FracPart[p]*Int[(1+b*x^n/a)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,n,p,q},x] && NeQ[b*c-a*d,0] && NeQ[n+1] && Not[PositiveQ[a]]


Int[(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.,x_Symbol] :=
  Int[(a+b*x^n)^p*(d+c*x^n)^q/x^(n*q),x] /;
FreeQ[{a,b,c,d,n,p},x] && EqQ[mn,-n] && IntegerQ[q] && (PosQ[n] || Not[IntegerQ[p]])


Int[(a_+b_.*x_^n_.)^p_*(c_+d_.*x_^mn_.)^q_,x_Symbol] :=
  x^(n*FracPart[q])*(c+d*x^(-n))^FracPart[q]/(d+c*x^n)^FracPart[q]*Int[(a+b*x^n)^p*(d+c*x^n)^q/x^(n*q),x] /;
FreeQ[{a,b,c,d,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]]


Int[(a_.+b_.*u_^n_)^p_.*(c_.+d_.*u_^n_)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n)^p*(c+d*x^n)^q,x],x,u] /;
FreeQ[{a,b,c,d,n,p,q},x] && LinearQ[u,x] && NeQ[u-x]


Int[u_^p_.*v_^q_.,x_Symbol] :=
  Int[NormalizePseudoBinomial[u,x]^p*NormalizePseudoBinomial[v,x]^q,x] /;
FreeQ[{p,q},x] && PseudoBinomialPairQ[u,v,x]


Int[x_^m_.*u_^p_.*v_^q_.,x_Symbol] :=
  Int[NormalizePseudoBinomial[x^(m/p)*u,x]^p*NormalizePseudoBinomial[v,x]^q,x] /;
FreeQ[{p,q},x] && IntegersQ[p,m/p] && PseudoBinomialPairQ[x^(m/p)*u,v,x]


(* IntBinomialQ[a,b,c,d,n,p,q,x] returns True iff (a+b*x^n)^p*(c+d*x^n)^q is integrable wrt x in terms of non-Appell functions. *)
IntBinomialQ[a_,b_,c_,d_,n_,p_,q_,x_Symbol] :=
  IntegersQ[p,q] || PositiveIntegerQ[p] || PositiveIntegerQ[q] || 
  (EqQ[n-2] || EqQ[n-4]) && (IntegersQ[p,4*q] || IntegersQ[4*p,q]) || 
  EqQ[n-2] && (IntegersQ[2*p,2*q] || IntegersQ[3*p,q] && EqQ[b*c+3*a*d] || IntegersQ[p,3*q] && EqQ[3*b*c+a*d])


(* ::Subsection::Closed:: *)
(*1.1.3.4 (e x)^m (a+b x^n)^p (c+d x^n)^q*)


Int[(e_.*x_)^m_.*(b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  e^m/(n*b^(Simplify[(m+1)/n]-1))*Subst[Int[(b*x)^(p+Simplify[(m+1)/n]-1)*(c+d*x)^q,x],x,x^n] /;
FreeQ[{b,c,d,e,m,n,p,q},x] && (IntegerQ[m] || PositiveQ[e]) && IntegerQ[Simplify[(m+1)/n]]


Int[(e_.*x_)^m_.*(b_.*x_^n_.)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  e^m*b^IntPart[p]*(b*x^n)^FracPart[p]/x^(n*FracPart[p])*Int[x^(m+n*p)*(c+d*x^n)^q,x] /;
FreeQ[{b,c,d,e,m,n,p,q},x] && (IntegerQ[m] || PositiveQ[e]) && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[(e_*x_)^m_*(b_.*x_^n_.)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{b,c,d,e,m,n,p,q},x] && Not[IntegerQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  1/n*Subst[Int[(a+b*x)^p*(c+d*x)^q,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && NeQ[b*c-a*d] && EqQ[m-n+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  Int[x^(m+n*(p+q))*(b+a*x^(-n))^p*(d+c*x^(-n))^q,x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d] && IntegersQ[p,q] && NegQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p*(c+d*x)^q,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && NeQ[b*c-a*d] && IntegerQ[Simplify[(m+1)/n]]


Int[(e_*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && NeQ[b*c-a*d] && IntegerQ[Simplify[(m+1)/n]]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d] && PositiveIntegerQ[p,q]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d] && EqQ[a*d*(m+1)-b*c*(m+n*(p+1)+1)] && NeQ[m+1]


Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*e*(m+1)) /;
FreeQ[{a1,b1,a2,b2,c,d,e,m,n,p},x] && EqQ[non2-n/2] && EqQ[a2*b1+a1*b2] && EqQ[a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1)] && 
  NeQ[m+1]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) + d/e^n*Int[(e*x)^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d] && EqQ[m+n*(p+1)+1] && (IntegerQ[n] || PositiveQ[e]) && 
  RationalQ[m,n] && (n>0 && m<-1 || n<0 && m+n>-1)


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  (b*c-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*b*e*(m+1)) + d/b*Int[(e*x)^m*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d] && EqQ[m+n*(p+1)+1] && NeQ[m+1]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) + 
  (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(a*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d] && (IntegerQ[n] || PositiveQ[e]) && 
  RationalQ[m,n] && (n>0 && m<-1 || n<0 && m+n>-1) && Not[IntegerQ[p] && p<-1]


Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*e*(m+1)) + 
  (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(a1*a2*e^n*(m+1))*Int[(e*x)^(m+n)*(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,d,e,p},x] && EqQ[non2-n/2] && EqQ[a2*b1+a1*b2] && (IntegerQ[n] || PositiveQ[e]) && 
  RationalQ[m,n] && (n>0 && m<-1 || n<0 && m+n>-1) && Not[IntegerQ[p] && p<-1]


Int[x_^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2),x_Symbol] :=
  (-a)^(m/2-1)*(b*c-a*d)*x*(a+b*x^2)^(p+1)/(2*b^(m/2+1)*(p+1)) + 
  1/(2*b^(m/2+1)*(p+1))*Int[(a+b*x^2)^(p+1)*
    ExpandToSum[2*b*(p+1)*x^2*Together[(b^(m/2)*x^(m-2)*(c+d*x^2)-(-a)^(m/2-1)*(b*c-a*d))/(a+b*x^2)]-(-a)^(m/2-1)*(b*c-a*d),x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && RationalQ[p] && p<-1 && PositiveIntegerQ[m/2] && (IntegerQ[p] || m+2*p+1==0)


Int[x_^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2),x_Symbol] :=
  (-a)^(m/2-1)*(b*c-a*d)*x*(a+b*x^2)^(p+1)/(2*b^(m/2+1)*(p+1)) + 
  1/(2*b^(m/2+1)*(p+1))*Int[x^m*(a+b*x^2)^(p+1)*
    ExpandToSum[2*b*(p+1)*Together[(b^(m/2)*(c+d*x^2)-(-a)^(m/2-1)*(b*c-a*d)*x^(-m+2))/(a+b*x^2)]-
      (-a)^(m/2-1)*(b*c-a*d)*x^(-m),x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && RationalQ[p] && p<-1 && NegativeIntegerQ[m/2] && (IntegerQ[p] || m+2*p+1==0)


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  -(b*c-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*b*e*n*(p+1)) - 
  (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(a*b*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d] && RationalQ[p] && p<-1 && 
  (IntegerQ[p] || Not[RationalQ[m]] || PositiveIntegerQ[n] && NegativeIntegerQ[p+1/2] && -1<=m<=-n*(p+1))


Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  -(b1*b2*c-a1*a2*d)*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*b1*b2*e*n*(p+1)) - 
  (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(a1*a2*b1*b2*n*(p+1))*Int[(e*x)^m*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1),x] /;
FreeQ[{a1,b1,a2,b2,c,d,e,m,n},x] && EqQ[non2-n/2] && EqQ[a2*b1+a1*b2] && RationalQ[p] && p<-1 && 
  (IntegerQ[p] || Not[RationalQ[m]] || PositiveIntegerQ[n] && NegativeIntegerQ[p+1/2] && -1<=m<=-n*(p+1))


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  d*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(b*e*(m+n*(p+1)+1)) - 
  (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(b*(m+n*(p+1)+1))*Int[(e*x)^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d] && NeQ[m+n*(p+1)+1]


Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  d*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(b1*b2*e*(m+n*(p+1)+1)) - 
  (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(b1*b2*(m+n*(p+1)+1))*Int[(e*x)^m*(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,d,e,m,n,p},x] && EqQ[non2-n/2] && EqQ[a2*b1+a1*b2] && NeQ[m+n*(p+1)+1]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_/(c_+d_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p/(c+d*x^n),x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && PositiveIntegerQ[p] && 
  (IntegerQ[m] || PositiveIntegerQ[2*(m+1)] || Not[RationalQ[m]])


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
  c^2*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) - 
  1/(a*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p*Simp[b*c^2*n*(p+1)+c*(b*c-2*a*d)*(m+1)-a*(m+1)*d^2*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,n] && m<-1 && n>0


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
  -(b*c-a*d)^2*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*b^2*e*n*(p+1)) + 
  1/(a*b^2*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*Simp[(b*c-a*d)^2*(m+1)+b^2*c^2*n*(p+1)+a*b*d^2*n*(p+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
  d^2*(e*x)^(m+n+1)*(a+b*x^n)^(p+1)/(b*e^(n+1)*(m+n*(p+2)+1)) + 
  1/(b*(m+n*(p+2)+1))*Int[(e*x)^m*(a+b*x^n)^p*Simp[b*c^2*(m+n*(p+2)+1)+d*((2*b*c-a*d)*(m+n+1)+2*b*c*n*(p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && NeQ[m+n*(p+2)+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k))^p*(c+d*x^(n/k))^q,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/e*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/e^n)^p*(c+d*x^(k*n)/e^n)^q,x],x,(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && FractionQ[m] && IntegerQ[p]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*n*(p+1)) - 
  e^n/(b*n*(p+1))*Int[(e*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m-n+1)+d*(m+n*(q-1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p,q] && p<-1 && q>0 && m-n+1>0 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(c*b-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*b*e*n*(p+1)) + 
  1/(a*b*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-2)*
    Simp[c*(c*b*n*(p+1)+(c*b-a*d)*(m+1))+d*(c*b*n*(p+1)+(c*b-a*d)*(m+n*(q-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p,q] && p<-1 && q>1 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*n*(p+1)) + 
  1/(a*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m+n*(p+1)+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p,q] && p<-1 && 0<q<1 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -a*e^(2*n-1)*(e*x)^(m-2*n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*n*(b*c-a*d)*(p+1)) + 
  e^(2*n)/(b*n*(b*c-a*d)*(p+1))*Int[(e*x)^(m-2*n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
    Simp[a*c*(m-2*n+1)+(a*d*(m-n+n*q+1)+b*c*n*(p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m-n+1>n && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(n*(b*c-a*d)*(p+1)) - 
  e^n/(n*(b*c-a*d)*(p+1))*Int[(e*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*(m-n+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && n>=m-n+1>0 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -b*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*e*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*
    Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*b*(m+1)+n*(b*c-a*d)*(p+1)+d*b*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,q},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+1)) - 
  n/(e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[b*c*p+a*d*q+b*d*(p+q)*x^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p,q] && q>0 && m<-1 && p>0 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  c*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*e*(m+1)) - 
  1/(a*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
    Simp[c*(c*b-a*d)*(m+1)+c*n*(b*c*(p+1)+a*d*(q-1))+d*((c*b-a*d)*(m+1)+c*b*n*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,q] && q>1 && m<-1 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*(m+1)) - 
  1/(a*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
    Simp[c*b*(m+1)+n*(b*c*(p+1)+a*d*q)+d*(b*(m+1)+b*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,q] && 0<q<1 && m<-1 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+n*(p+q)+1)) + 
  n/(m+n*(p+q)+1)*Int[(e*x)^m*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p,q] && q>0 && p>0 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  d*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(b*e*(m+n*(p+q)+1)) + 
  1/(b*(m+n*(p+q)+1))*Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
    Simp[c*((c*b-a*d)*(m+1)+c*b*n*(p+q))+(d*(c*b-a*d)*(m+1)+d*n*(q-1)*(b*c-a*d)+c*b*d*n*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[q] && q>1 && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*(m+n*(p+q)+1)) - 
  e^n/(b*(m+n*(p+q)+1))*
    Int[(e*x)^(m-n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*Simp[a*c*(m-n+1)+(a*d*(m-n+1)-n*q*(b*c-a*d))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,q] && q>0 && m-n+1>0 && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(2*n-1)*(e*x)^(m-2*n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*d*(m+n*(p+q)+1)) - 
  e^(2*n)/(b*d*(m+n*(p+q)+1))*
    Int[(e*x)^(m-2*n)*(a+b*x^n)^p*(c+d*x^n)^q*Simp[a*c*(m-2*n+1)+(a*d*(m+n*(q-1)+1)+b*c*(m+n*(p-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && m-n+1>n && 
  IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*c*e*(m+1)) - 
  1/(a*c*e^n*(m+1))*
    Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q*Simp[(b*c+a*d)*(m+n+1)+n*(b*c*p+a*d*q)+b*d*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  -a*e^n/(b*c-a*d)*Int[(e*x)^(m-n)/(a+b*x^n),x] + c*e^n/(b*c-a*d)*Int[(e*x)^(m-n)/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && n<=m<=2*n-1


Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  b/(b*c-a*d)*Int[(e*x)^m/(a+b*x^n),x] - d/(b*c-a*d)*Int[(e*x)^m/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d] && PositiveIntegerQ[n]


Int[x_^m_/((a_+b_.*x_^n_)*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  1/b*Int[x^(m-n)/Sqrt[c+d*x^n],x] - a/b*Int[x^(m-n)/((a+b*x^n)*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && IntegersQ[m/2,n/2] && 0<m-n+1<n && n<=4


Int[x_^2/((a_+b_.*x_^4)*Sqrt[c_+d_.*x_^4]),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  s/(2*b)*Int[1/((r+s*x^2)*Sqrt[c+d*x^4]),x] - s/(2*b)*Int[1/((r-s*x^2)*Sqrt[c+d*x^4]),x]] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d]


Int[x_/((a_+b_.*x_^3)*Sqrt[c_+d_.*x_^3]),x_Symbol] :=
  With[{q=Rt[d/c,3]},
  -q*ArcTan[1/Sqrt[3]+2^(2/3)*(Sqrt[c]-Sqrt[c+d*x^3])/(Sqrt[3]*Sqrt[c]*q*x)]/(3*2^(2/3)*Sqrt[3]*b*Sqrt[c]) + 
  q*ArcTan[1/Sqrt[3]+2^(2/3)*(Sqrt[c]+Sqrt[c+d*x^3])/(Sqrt[3]*Sqrt[c]*q*x)]/(3*2^(2/3)*Sqrt[3]*b*Sqrt[c]) + 
  q*ArcTanh[Sqrt[c+d*x^3]/Sqrt[c]]/(9*2^(2/3)*b*Sqrt[c]) + 
  q*Log[1-2^(1/3)*q*x-Sqrt[c+d*x^3]/Sqrt[c]]/(6*2^(2/3)*b*Sqrt[c]) - 
  q*Log[1-2^(1/3)*q*x+Sqrt[c+d*x^3]/Sqrt[c]]/(6*2^(2/3)*b*Sqrt[c])] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && EqQ[4*b*c-a*d]


Int[x_^m_/((a_+b_.*x_^3)*Sqrt[c_+d_.*x_^3]),x_Symbol] :=
  1/b*Int[x^(m-3)/Sqrt[c+d*x^3],x] - a/b*Int[x^(m-3)/((a+b*x^3)*Sqrt[c+d*x^3]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && EqQ[4*b*c-a*d] && PositiveIntegerQ[(m-1)/3]


Int[x_^m_/((a_+b_.*x_^3)*Sqrt[c_+d_.*x_^3]),x_Symbol] :=
  1/a*Int[x^m/Sqrt[c+d*x^3],x] - b/a*Int[x^(m+3)/((a+b*x^3)*Sqrt[c+d*x^3]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && EqQ[4*b*c-a*d] && NegativeIntegerQ[(m-1)/3]


Int[x_^2*Sqrt[c_+d_.*x_^4]/(a_+b_.*x_^4),x_Symbol] :=
  d/b*Int[x^2/Sqrt[c+d*x^4],x] + (b*c-a*d)/b*Int[x^2/((a+b*x^4)*Sqrt[c+d*x^4]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d]


Int[x_^m_.*Sqrt[c_+d_.*x_^3]/(a_+b_.*x_^3),x_Symbol] :=
  d/b*Int[x^m/Sqrt[c+d*x^3],x] + (b*c-a*d)/b*Int[x^m/((a+b*x^3)*Sqrt[c+d*x^3]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && EqQ[4*b*c-a*d] && IntegerQ[(m-1)/3]


Int[x_^2/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  x*Sqrt[a+b*x^2]/(b*Sqrt[c+d*x^2]) - c/b*Int[Sqrt[a+b*x^2]/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && PosQ[b/a] && PosQ[d/c] && Not[SimplerSqrtQ[b/a,d/c]]


Int[x_^n_/(Sqrt[a_+b_.*x_^n_]*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  1/b*Int[Sqrt[a+b*x^n]/Sqrt[c+d*x^n],x] - a/b*Int[1/(Sqrt[a+b*x^n]*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d] && (EqQ[n,2] || EqQ[n,4]) && Not[EqQ[n,2] && SimplerSqrtQ[-b/a,-d/c]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  With[{k=Denominator[p]},
  k*a^(p+(m+1)/n)/n*
	Subst[Int[x^(k*(m+1)/n-1)*(c-(b*c-a*d)*x^k)^q/(1-b*x^k)^(p+q+(m+1)/n+1),x],x,x^(n/k)/(a+b*x^n)^(1/k)]] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[n] && RationalQ[m,p] && IntegersQ[p+(m+1)/n,q] && -1<p<0


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  With[{g=Denominator[m]},
  -g/e*Subst[Int[(a+b*e^(-n)*x^(-g*n))^p*(c+d*e^(-n)*x^(-g*n))^q/x^(g*(m+1)+1),x],x,1/(e*x)^(1/g)]] /;
FreeQ[{a,b,c,d,e,p,q},x] && NegativeIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,m,p,q},x] && NeQ[b*c-a*d] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*(a+b*x^(g*n))^p*(c+d*x^(g*n))^q,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,d,m,p,q},x] && NeQ[b*c-a*d] && FractionQ[n]


Int[(e_*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,m,p,q},x] && NeQ[b*c-a*d] && FractionQ[n]


(* Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -1/(m+1)*Subst[Int[(a+b*x^Simplify[-n/(m+1)])^p*(c+d*x^Simplify[-n/(m+1)])^q/x^2,x],x,x^(-(m+1))] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d] && NeQ[m+1] && NegativeIntegerQ[Simplify[n/(m+1)+1]] && 
  RationalQ[p,q] && -1<=p<0 && -1<=q<0 && Not[IntegerQ[n]] *)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*x^Simplify[n/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && NeQ[b*c-a*d] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && NeQ[b*c-a*d] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(c*b-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*b*e*n*(p+1)) + 
  1/(a*b*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-2)*
    Simp[c*(c*b*n*(p+1)+(c*b-a*d)*(m+1))+d*(c*b*n*(p+1)+(c*b-a*d)*(m+n*(q-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d] && RationalQ[p,q] && p<-1 && q>1 && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*n*(p+1)) + 
  1/(a*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m+n*(p+1)+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d] && RationalQ[p,q] && p<-1 && 0<q<1 && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -b*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*e*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*
    Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*b*(m+1)+n*(b*c-a*d)*(p+1)+d*b*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && NeQ[b*c-a*d] && RationalQ[p] && p<-1 && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+n*(p+q)+1)) + 
  n/(m+n*(p+q)+1)*Int[(e*x)^m*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d] && RationalQ[p,q] && q>0 && p>0 && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  d*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(b*e*(m+n*(p+q)+1)) + 
  1/(b*(m+n*(p+q)+1))*Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
    Simp[c*((c*b-a*d)*(m+1)+c*b*n*(p+q))+(d*(c*b-a*d)*(m+1)+d*n*(q-1)*(b*c-a*d)+c*b*d*n*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d] && RationalQ[q] && q>1 && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]


Int[x_^m_/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  -a/(b*c-a*d)*Int[x^(m-n)/(a+b*x^n),x] + c/(b*c-a*d)*Int[x^(m-n)/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d] && (EqQ[m-n] || EqQ[m-2*n+1])


Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  b/(b*c-a*d)*Int[(e*x)^m/(a+b*x^n),x] - d/(b*c-a*d)*Int[(e*x)^m/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,e,n,m},x] && NeQ[b*c-a*d]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d] && IntegersQ[m,p,q] && p>=-2 && (q>=-2 || q==-3 && IntegerQ[(m-1)/2])


Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.,x_Symbol] :=
  Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[mn,-n] && IntegerQ[q] && (PosQ[n] || Not[IntegerQ[p]])


Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_,x_Symbol] :=
  x^(n*FracPart[q])*(c+d*x^(-n))^FracPart[q]/(d+c*x^n)^FracPart[q]*Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q,x] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]]


Int[(e_*x_)^m_*(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p*(c+d*x^(-n))^q,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[mn,-n]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  a^p*c^q*(e*x)^(m+1)/(e*(m+1))*AppellF1[(m+1)/n,-p,-q,1+(m+1)/n,-b*x^n/a,-d*x^n/c] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && NeQ[b*c-a*d] && NeQ[m+1] && NeQ[m-n+1] && PositiveQ[a] && PositiveQ[c]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^n)^FracPart[p]/(1+b*x^n/a)^FracPart[p]*Int[(e*x)^m*(1+b*x^n/a)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && NeQ[b*c-a*d] && NeQ[m+1] && NeQ[m-n+1] && Not[PositiveQ[a]]


Int[x_^m_.*(a_.+b_.*v_^n_)^p_.*(c_.+d_.*v_^n_)^q_.,x_Symbol] :=
  1/Coefficient[v,x,1]^(m+1)*Subst[Int[SimplifyIntegrand[(x-Coefficient[v,x,0])^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x],x,v] /;
FreeQ[{a,b,c,d,n,p,q},x] && LinearQ[v,x] && IntegerQ[m] && NeQ[v-x]


Int[u_^m_.*(a_.+b_.*v_^n_)^p_.*(c_.+d_.*v_^n_)^q_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x,v] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && LinearPairQ[u,v,x]


(* IntBinomialQ[a,b,c,d,e,m,n,p,q,x] returns True iff (e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q is integrable wrt x in terms of non-Appell functions. *)
IntBinomialQ[a_,b_,c_,d_,e_,m_,n_,p_,q_,x_Symbol] :=
  IntegersQ[p,q] || PositiveIntegerQ[p] || PositiveIntegerQ[q] || 
  EqQ[n-2] && IntegerQ[m] && IntegersQ[2*p,2*q] || 
  EqQ[n-4] && (IntegersQ[m,p,2*q] || IntegersQ[m,2*p,q])


Int[u_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  Int[u*(a1*a2+b1*b2*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a1,b1,a2,b2,c,d,n,p,q},x] && EqQ[non2-n/2] && EqQ[a2*b1+a1*b2] && (IntegerQ[p] || PositiveQ[a1] && PositiveQ[a2])


Int[u_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_.+e_.*x_^n2_.)^q_.,x_Symbol] :=
  Int[u*(a1*a2+b1*b2*x^n)^p*(c+d*x^n+e*x^(2*n))^q,x] /;
FreeQ[{a1,b1,a2,b2,c,d,e,n,p,q},x] && EqQ[non2-n/2] && EqQ[n2-2*n] && EqQ[a2*b1+a1*b2] && 
  (IntegerQ[p] || PositiveQ[a1] && PositiveQ[a2])


Int[u_.*(a1_+b1_.*x_^non2_.)^p_*(a2_+b2_.*x_^non2_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  (a1+b1*x^(n/2))^FracPart[p]*(a2+b2*x^(n/2))^FracPart[p]/(a1*a2+b1*b2*x^n)^FracPart[p]*
    Int[u*(a1*a2+b1*b2*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a1,b1,a2,b2,c,d,n,p,q},x] && EqQ[non2-n/2] && EqQ[a2*b1+a1*b2]


Int[u_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_.+e_.*x_^n2_.)^q_.,x_Symbol] :=
  (a1+b1*x^(n/2))^FracPart[p]*(a2+b2*x^(n/2))^FracPart[p]/(a1*a2+b1*b2*x^n)^FracPart[p]*
    Int[u*(a1*a2+b1*b2*x^n)^p*(c+d*x^n+e*x^(2*n))^q,x] /;
FreeQ[{a1,b1,a2,b2,c,d,e,n,p,q},x] && EqQ[non2-n/2] && EqQ[n2-2*n] && EqQ[a2*b1+a1*b2]





(* ::Subsection::Closed:: *)
(*1.1.3.5 (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r*)


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && PositiveIntegerQ[p,q,r]


Int[(e_+f_.*x_^n_)/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[1/(a+b*x^n),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[1/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,e,f,n},x]


Int[(e_+f_.*x_^n_)/((a_+b_.*x_^n_)*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  f/b*Int[1/Sqrt[c+d*x^n],x] + 
  (b*e-a*f)/b*Int[1/((a+b*x^n)*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d,e,f,n},x]


Int[(e_+f_.*x_^n_)/(Sqrt[a_+b_.*x_^n_]*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  f/b*Int[Sqrt[a+b*x^n]/Sqrt[c+d*x^n],x] + 
  (b*e-a*f)/b*Int[1/(Sqrt[a+b*x^n]*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && 
  Not[EqQ[n-2] && (PosQ[b/a] && PosQ[d/c] || NegQ[b/a] && (PosQ[d/c] || PositiveQ[a] && (Not[PositiveQ[c]] || SimplerSqrtQ[-b/a,-d/c])))]


Int[(e_+f_.*x_^2)/(Sqrt[a_+b_.*x_^2]*(c_+d_.*x_^2)^(3/2)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[Sqrt[a+b*x^2]/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[b/a] && PosQ[d/c]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  -(b*e-a*f)*x*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*b*n*(p+1)) + 
  1/(a*b*n*(p+1))*
    Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(b*e*n*(p+1)+b*e-a*f)+d*(b*e*n*(p+1)+(b*e-a*f)*(n*q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && RationalQ[p,q] && p<-1 && q>0


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  -(b*e-a*f)*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*
    Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*(b*e-a*f)+e*n*(b*c-a*d)*(p+1)+d*(b*e-a*f)*(n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n,q},x] && RationalQ[p] && p<-1


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  f*x*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*(n*(p+q+1)+1)) + 
  1/(b*(n*(p+q+1)+1))*
    Int[(a+b*x^n)^p*(c+d*x^n)^(q-1)*Simp[c*(b*e-a*f+b*e*n*(p+q+1))+(d*(b*e-a*f)+f*n*q*(b*c-a*d)+b*d*e*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && RationalQ[q] && q>0 && NeQ[n*(p+q+1)+1]


Int[(e_+f_.*x_^4)/((a_+b_.*x_^4)^(3/4)*(c_+d_.*x_^4)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[1/(a+b*x^4)^(3/4),x] - (d*e-c*f)/(b*c-a*d)*Int[(a+b*x^4)^(1/4)/(c+d*x^4),x] /;
FreeQ[{a,b,c,d,e,f},x]


Int[(a_+b_.*x_^n_)^p_*(e_+f_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
  f/d*Int[(a+b*x^n)^p,x] + (d*e-c*f)/d*Int[(a+b*x^n)^p/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,e,f,p,n},x]


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  e*Int[(a+b*x^n)^p*(c+d*x^n)^q,x] + f*Int[x^n*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,f,n,p,q},x]


Int[1/((a_+b_.*x_^2)*(c_+d_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  b/(b*c-a*d)*Int[1/((a+b*x^2)*Sqrt[e+f*x^2]),x] - 
  d/(b*c-a*d)*Int[1/((c+d*x^2)*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x]


Int[1/(x_^2*(c_+d_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  1/c*Int[1/(x^2*Sqrt[e+f*x^2]),x] - 
  d/c*Int[1/((c+d*x^2)*Sqrt[e+f*x^2]),x] /;
FreeQ[{c,d,e,f},x] && NeQ[d*e-c*f]


Int[Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2),x_Symbol] :=
  d/b*Int[Sqrt[e+f*x^2]/Sqrt[c+d*x^2],x] + (b*c-a*d)/b*Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveQ[d/c] && PositiveQ[f/e] && Not[SimplerSqrtQ[d/c,f/e]]


Int[Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2),x_Symbol] :=
  d/b*Int[Sqrt[e+f*x^2]/Sqrt[c+d*x^2],x] + (b*c-a*d)/b*Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[SimplerSqrtQ[-f/e,-d/c]]


Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  -f/(b*e-a*f)*Int[1/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] + 
  b/(b*e-a*f)*Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c] && PosQ[f/e] && Not[SimplerSqrtQ[d/c,f/e]]


Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  1/(a*Sqrt[c]*Sqrt[e]*Rt[-d/c,2])*EllipticPi[b*c/(a*d), ArcSin[Rt[-d/c,2]*x], c*f/(d*e)] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[d/c] && PositiveQ[c] && PositiveQ[e] && Not[NegQ[f/e] && SimplerSqrtQ[-f/e,-d/c]]


Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  Sqrt[1+d/c*x^2]/Sqrt[c+d*x^2]*Int[1/((a+b*x^2)*Sqrt[1+d/c*x^2]*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[PositiveQ[c]]


Int[Sqrt[c_+d_.*x_^2]/((a_+b_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  c*Sqrt[e+f*x^2]/(a*e*Rt[d/c,2]*Sqrt[c+d*x^2]*Sqrt[c*(e+f*x^2)/(e*(c+d*x^2))])*
    EllipticPi[1-b*c/(a*d),ArcTan[Rt[d/c,2]*x],1-c*f/(d*e)] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c]


(* Int[Sqrt[c_+d_.*x_^2]/((a_+b_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  Sqrt[c+d*x^2]*Sqrt[c*(e+f*x^2)/(e*(c+d*x^2))]/(a*Rt[d/c,2]*Sqrt[e+f*x^2])*
    EllipticPi[1-b*c/(a*d),ArcTan[Rt[d/c,2]*x],1-c*f/(d*e)] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c] *)


Int[Sqrt[c_+d_.*x_^2]/((a_+b_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  d/b*Int[1/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] + 
  (b*c-a*d)/b*Int[1/((a+b*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[d/c]


Int[Sqrt[e_+f_.*x_^2]/((a_+b_.*x_^2)*(c_+d_.*x_^2)^(3/2)),x_Symbol] :=
  b/(b*c-a*d)*Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] - 
  d/(b*c-a*d)*Int[Sqrt[e+f*x^2]/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c] && PosQ[f/e]


Int[(e_+f_.*x_^2)^(3/2)/((a_+b_.*x_^2)*(c_+d_.*x_^2)^(3/2)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[Sqrt[e+f*x^2]/(c+d*x^2)^(3/2),x] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c] && PosQ[f/e]


Int[(c_+d_.*x_^2)^(3/2)*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2),x_Symbol] :=
  (b*c-a*d)^2/b^2*Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x] + 
  d/b^2*Int[(2*b*c-a*d+b*d*x^2)*Sqrt[e+f*x^2]/Sqrt[c+d*x^2],x] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[d/c] && PosQ[f/e]


Int[(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_/(a_+b_.*x_^2),x_Symbol] :=
  b*(b*e-a*f)/(b*c-a*d)^2*Int[(c+d*x^2)^(q+2)*(e+f*x^2)^(r-1)/(a+b*x^2),x] - 
  1/(b*c-a*d)^2*Int[(c+d*x^2)^q*(e+f*x^2)^(r-1)*(2*b*c*d*e-a*d^2*e-b*c^2*f+d^2*(b*e-a*f)*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[q,r] && q<-1 && r>1


Int[(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_/(a_+b_.*x_^2),x_Symbol] :=
  d/b*Int[(c+d*x^2)^(q-1)*(e+f*x^2)^r,x] + 
  (b*c-a*d)/b*Int[(c+d*x^2)^(q-1)*(e+f*x^2)^r/(a+b*x^2),x] /;
FreeQ[{a,b,c,d,e,f,r},x] && RationalQ[q] && q>1


Int[(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_/(a_+b_.*x_^2),x_Symbol] :=
  b^2/(b*c-a*d)^2*Int[(c+d*x^2)^(q+2)*(e+f*x^2)^r/(a+b*x^2),x] - 
  d/(b*c-a*d)^2*Int[(c+d*x^2)^q*(e+f*x^2)^r*(2*b*c-a*d+b*d*x^2),x] /;
FreeQ[{a,b,c,d,e,f,r},x] && RationalQ[q] && q<-1


Int[(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_/(a_+b_.*x_^2),x_Symbol] :=
  -d/(b*c-a*d)*Int[(c+d*x^2)^q*(e+f*x^2)^r,x] + 
  b/(b*c-a*d)*Int[(c+d*x^2)^(q+1)*(e+f*x^2)^r/(a+b*x^2),x] /;
FreeQ[{a,b,c,d,e,f,r},x] && RationalQ[q] && q<=-1


Int[Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2)^2,x_Symbol] :=
  x*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]/(2*a*(a+b*x^2)) + 
  d*f/(2*a*b^2)*Int[(a-b*x^2)/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] + 
  (b^2*c*e-a^2*d*f)/(2*a*b^2)*Int[1/((a+b*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x]


Int[1/((a_+b_.*x_^2)^2*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  b^2*x*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]/(2*a*(b*c-a*d)*(b*e-a*f)*(a+b*x^2)) - 
  d*f/(2*a*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x^2)/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] + 
  (b^2*c*e+3*a^2*d*f-2*a*b*(d*e+c*f))/(2*a*(b*c-a*d)*(b*e-a*f))*Int[1/((a+b*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
  d/b*Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*(e+f*x^n)^r,x] + 
  (b*c-a*d)/b*Int[(a+b*x^n)^p*(c+d*x^n)^(q-1)*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,n,r},x] && NegativeIntegerQ[p] && RationalQ[q] && q>0


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
  b/(b*c-a*d)*Int[(a+b*x^n)^p*(c+d*x^n)^(q+1)*(e+f*x^n)^r,x] - 
  d/(b*c-a*d)*Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,n,q},x] && NegativeIntegerQ[p] && RationalQ[q] && q<=-1


Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  Sqrt[c+d*x^2]*Sqrt[a*(e+f*x^2)/(e*(a+b*x^2))]/(c*Sqrt[e+f*x^2]*Sqrt[a*(c+d*x^2)/(c*(a+b*x^2))])*
    Subst[Int[1/(Sqrt[1-(b*c-a*d)*x^2/c]*Sqrt[1-(b*e-a*f)*x^2/e]),x],x,x/Sqrt[a+b*x^2]] /;
FreeQ[{a,b,c,d,e,f},x]


Int[Sqrt[a_+b_.*x_^2]/(Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  a*Sqrt[c+d*x^2]*Sqrt[a*(e+f*x^2)/(e*(a+b*x^2))]/(c*Sqrt[e+f*x^2]*Sqrt[a*(c+d*x^2)/(c*(a+b*x^2))])*
    Subst[Int[1/((1-b*x^2)*Sqrt[1-(b*c-a*d)*x^2/c]*Sqrt[1-(b*e-a*f)*x^2/e]),x],x,x/Sqrt[a+b*x^2]] /;
FreeQ[{a,b,c,d,e,f},x]


Int[Sqrt[c_+d_.*x_^2]/((a_+b_.*x_^2)^(3/2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  Sqrt[c+d*x^2]*Sqrt[a*(e+f*x^2)/(e*(a+b*x^2))]/(a*Sqrt[e+f*x^2]*Sqrt[a*(c+d*x^2)/(c*(a+b*x^2))])*
    Subst[Int[Sqrt[1-(b*c-a*d)*x^2/c]/Sqrt[1-(b*e-a*f)*x^2/e],x],x,x/Sqrt[a+b*x^2]] /;
FreeQ[{a,b,c,d,e,f},x]


Int[Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]/Sqrt[e_+f_.*x_^2],x_Symbol] :=
  d*x*Sqrt[a+b*x^2]*Sqrt[e+f*x^2]/(2*f*Sqrt[c+d*x^2]) - 
  c*(d*e-c*f)/(2*f)*Int[Sqrt[a+b*x^2]/((c+d*x^2)^(3/2)*Sqrt[e+f*x^2]),x] + 
  b*c*(d*e-c*f)/(2*d*f)*Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] - 
  (b*d*e-b*c*f-a*d*f)/(2*d*f)*Int[Sqrt[c+d*x^2]/(Sqrt[a+b*x^2]*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[(d*e-c*f)/c]


Int[Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]/Sqrt[e_+f_.*x_^2],x_Symbol] :=
  x*Sqrt[a+b*x^2]*Sqrt[c+d*x^2]/(2*Sqrt[e+f*x^2]) + 
  e*(b*e-a*f)/(2*f)*Int[Sqrt[c+d*x^2]/(Sqrt[a+b*x^2]*(e+f*x^2)^(3/2)),x] + 
  (b*e-a*f)*(d*e-2*c*f)/(2*f^2)*Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] - 
  (b*d*e-b*c*f-a*d*f)/(2*f^2)*Int[Sqrt[e+f*x^2]/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[(d*e-c*f)/c]


Int[Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]/(e_+f_.*x_^2)^(3/2),x_Symbol] :=
  b/f*Int[Sqrt[c+d*x^2]/(Sqrt[a+b*x^2]*Sqrt[e+f*x^2]),x] - 
  (b*e-a*f)/f*Int[Sqrt[c+d*x^2]/(Sqrt[a+b*x^2]*(e+f*x^2)^(3/2)),x] /;
FreeQ[{a,b,c,d,e,f},x]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && PositiveIntegerQ[n]


Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q*(e+f*x^(-n))^r/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  Defer[Int][(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,n,p,q,r},x]


Int[(a_.+b_.*u_^n_)^p_.*(c_.+d_.*v_^n_)^q_.*(e_.+f_.*w_^n_)^r_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x],x,u] /;
FreeQ[{a,b,c,d,e,f,p,n,q,r},x] && EqQ[u-v] && EqQ[u-w] && LinearQ[u,x] && NeQ[u-x]


Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
  Int[(a+b*x^n)^p*(d+c*x^n)^q*(e+f*x^n)^r/x^(n*q),x] /;
FreeQ[{a,b,c,d,e,f,n,p,r},x] && EqQ[mn,-n] && IntegerQ[q]


Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
  Int[x^(n*(p+r))*(b+a*x^(-n))^p*(c+d*x^(-n))^q*(f+e*x^(-n))^r,x] /;
FreeQ[{a,b,c,d,e,f,n,q},x] && EqQ[mn,-n] && IntegerQ[p] && IntegerQ[r]


Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
  x^(n*FracPart[q])*(c+d*x^(-n))^FracPart[q]/(d+c*x^n)^FracPart[q]*Int[(a+b*x^n)^p*(d+c*x^n)^q*(e+f*x^n)^r/x^(n*q),x] /;
FreeQ[{a,b,c,d,e,f,n,p,q,r},x] && EqQ[mn,-n] && Not[IntegerQ[q]]


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e1_+f1_.*x_^n2_.)^r_.*(e2_+f2_.*x_^n2_.)^r_.,x_Symbol] :=
  Int[(a+b*x^n)^p*(c+d*x^n)^q*(e1*e2+f1*f2*x^n)^r,x] /;
FreeQ[{a,b,c,d,e1,f1,e2,f2,n,p,q,r},x] && EqQ[n2-n/2] && EqQ[e2*f1+e1*f2] && (IntegerQ[r] || PositiveQ[e1] && PositiveQ[e2])


Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e1_+f1_.*x_^n2_.)^r_.*(e2_+f2_.*x_^n2_.)^r_.,x_Symbol] :=
  (e1+f1*x^(n/2))^FracPart[r]*(e2+f2*x^(n/2))^FracPart[r]/(e1*e2+f1*f2*x^n)^FracPart[r]*
    Int[(a+b*x^n)^p*(c+d*x^n)^q*(e1*e2+f1*f2*x^n)^r,x] /;
FreeQ[{a,b,c,d,e1,f1,e2,f2,n,p,q,r},x] && EqQ[n2-n/2] && EqQ[e2*f1+e1*f2]





(* ::Subsection::Closed:: *)
(*1.1.3.6 (g x)^m (a+b x^n)^p (c+d x^n)^q (e+f x^n)^r*)


Int[(g_.*x_)^m_.*(b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  g^m/(n*b^(Simplify[(m+1)/n]-1))*Subst[Int[(b*x)^(p+Simplify[(m+1)/n]-1)*(c+d*x)^q*(e+f*x)^r,x],x,x^n] /;
FreeQ[{b,c,d,e,f,g,m,n,p,q,r},x] && (IntegerQ[m] || PositiveQ[g]) && IntegerQ[Simplify[(m+1)/n]]


Int[(g_.*x_)^m_.*(b_.*x_^n_.)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  g^m*b^IntPart[p]*(b*x^n)^FracPart[p]/x^(n*FracPart[p])*Int[x^(m+n*p)*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{b,c,d,e,f,g,m,n,p,q,r},x] && (IntegerQ[m] || PositiveQ[g]) && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[(g_*x_)^m_*(b_.*x_^n_.)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{b,c,d,e,f,g,m,n,p,q,r},x] && Not[IntegerQ[m]]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  Int[ExpandIntegrand[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && PositiveIntegerQ[p+2,q,r]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  1/n*Subst[Int[(a+b*x)^p*(c+d*x)^q*(e+f*x)^r,x],x,x^n] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && EqQ[m-n+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  Int[x^(m+n*(p+q+r))*(b+a*x^(-n))^p*(d+c*x^(-n))^q*(f+e*x^(-n))^r,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IntegersQ[p,q,r] && NegQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p*(c+d*x)^q*(e+f*x)^r,x],x,x^n] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && IntegerQ[Simplify[(m+1)/n]]


Int[(g_*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k))^p*(c+d*x^(n/k))^q*(e+f*x^(n/k))^r,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/g*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/g^n)^p*(c+d*x^(k*n)/g^n)^q*(e+f*x^(k*n)/g^n)^r,x],x,(g*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,g,p,q,r},x] && PositiveIntegerQ[n] && FractionQ[m]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*b*g*n*(p+1)) + 
  1/(a*b*n*(p+1))*Int[(g*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*
    Simp[c*(b*e*n*(p+1)+(b*e-a*f)*(m+1))+d*(b*e*n*(p+1)+(b*e-a*f)*(m+n*q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && PositiveIntegerQ[n] && RationalQ[p,q] && p<-1 && q>0 && Not[q==1 && SimplerQ[b*c-a*d,b*e-a*f]]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_),x_Symbol] :=
  g^(n-1)*(b*e-a*f)*(g*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*n*(b*c-a*d)*(p+1)) - 
  g^n/(b*n*(b*c-a*d)*(p+1))*Int[(g*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
    Simp[c*(b*e-a*f)*(m-n+1)+(d*(b*e-a*f)*(m+n*q+1)-b*n*(c*f-d*e)*(p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,q},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m-n+1>0


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_),x_Symbol] :=
  -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*g*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*Int[(g*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
    Simp[c*(b*e-a*f)*(m+1)+e*n*(b*c-a*d)*(p+1)+d*(b*e-a*f)*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,q},x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  e*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*g*(m+1)) - 
  1/(a*g^n*(m+1))*Int[(g*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
    Simp[c*(b*e-a*f)*(m+1)+e*n*(b*c*(p+1)+a*d*q)+d*((b*e-a*f)*(m+1)+b*e*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && PositiveIntegerQ[n] && RationalQ[m,q] && q>0 && m<-1 && Not[q==1 && SimplerQ[e+f*x^n,c+d*x^n]]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  f*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*g*(m+n*(p+q+1)+1)) + 
  1/(b*(m+n*(p+q+1)+1))*Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
    Simp[c*((b*e-a*f)*(m+1)+b*e*n*(p+q+1))+(d*(b*e-a*f)*(m+1)+f*n*q*(b*c-a*d)+b*e*d*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && PositiveIntegerQ[n] && RationalQ[q] && q>0 && Not[q==1 && SimplerQ[e+f*x^n,c+d*x^n]]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  f*g^(n-1)*(g*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*d*(m+n*(p+q+1)+1)) - 
  g^n/(b*d*(m+n*(p+q+1)+1))*Int[(g*x)^(m-n)*(a+b*x^n)^p*(c+d*x^n)^q*
    Simp[a*f*c*(m-n+1)+(a*f*d*(m+n*q+1)+b*(f*c*(m+n*p+1)-e*d*(m+n*(p+q+1)+1)))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,p,q},x] && PositiveIntegerQ[n] && RationalQ[m] && m>n-1


Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  e*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*c*g*(m+1)) + 
  1/(a*c*g^n*(m+1))*Int[(g*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q*
    Simp[a*f*c*(m+1)-e*(b*c+a*d)*(m+n+1)-e*n*(b*c*p+a*d*q)-b*e*d*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,p,q},x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(e_+f_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(g*x)^m*(a+b*x^n)^p*(e+f*x^n)/(c+d*x^n),x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && PositiveIntegerQ[n]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  e*Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x] + 
  f/e^n*Int[(g*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p,q},x] && PositiveIntegerQ[n]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  e*Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^(r-1),x] + 
  f/e^n*Int[(g*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^(r-1),x] /;
FreeQ[{a,b,c,d,e,f,g,m,p,q},x] && PositiveIntegerQ[n] && PositiveIntegerQ[r]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q*(e+f*x^(-n))^r/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/g*Subst[Int[(a+b*g^(-n)*x^(-k*n))^p*(c+d*g^(-n)*x^(-k*n))^q*(e+f*g^(-n)*x^(-k*n))^r/x^(k*(m+1)+1),x],x,1/(g*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,g,p,q,r},x] && NegativeIntegerQ[n] && FractionQ[m]


Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  -(g*x)^m*(x^(-1))^m*Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q*(e+f*x^(-n))^r/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,f,g,m,p,q,r},x] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n))^p*(c+d*x^(k*n))^q*(e+f*x^(k*n))^r,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,m,p,q,r},x] && FractionQ[n]


Int[(g_*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p,q,r},x] && FractionQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*x^Simplify[n/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q*(e+f*x^Simplify[n/(m+1)])^r,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && IntegerQ[Simplify[n/(m+1)]]


Int[(g_*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x] && IntegerQ[Simplify[n/(m+1)]]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*b*g*n*(p+1)) + 
  1/(a*b*n*(p+1))*Int[(g*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*
    Simp[c*(b*e*n*(p+1)+(b*e-a*f)*(m+1))+d*(b*e*n*(p+1)+(b*e-a*f)*(m+n*q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && RationalQ[p,q] && p<-1 && q>0 && Not[q==1 && SimplerQ[b*c-a*d,b*e-a*f]]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_),x_Symbol] :=
  -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*g*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*Int[(g*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
    Simp[c*(b*e-a*f)*(m+1)+e*n*(b*c-a*d)*(p+1)+d*(b*e-a*f)*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && RationalQ[p] && p<-1


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
  f*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*g*(m+n*(p+q+1)+1)) + 
  1/(b*(m+n*(p+q+1)+1))*Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
    Simp[c*((b*e-a*f)*(m+1)+b*e*n*(p+q+1))+(d*(b*e-a*f)*(m+1)+f*n*q*(b*c-a*d)+b*e*d*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && RationalQ[q] && q>0 && Not[q==1 && SimplerQ[e+f*x^n,c+d*x^n]]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(e_+f_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(g*x)^m*(a+b*x^n)^p*(e+f*x^n)/(c+d*x^n),x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_),x_Symbol] :=
  e*Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x] + 
  f*(g*x)^m/x^m*Int[x^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q},x]


Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
  Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,r},x] && EqQ[mn,-n] && IntegerQ[q]


Int[x_^m_.*(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
  Int[x^(m+n*(p+r))*(b+a*x^(-n))^p*(c+d*x^(-n))^q*(f+e*x^(-n))^r,x] /;
FreeQ[{a,b,c,d,e,f,m,n,q},x] && EqQ[mn,-n] && IntegerQ[p] && IntegerQ[r]


Int[x_^m_.*(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
  x^(n*FracPart[q])*(c+d*x^(-n))^FracPart[q]/(d+c*x^n)^FracPart[q]*Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && EqQ[mn,-n] && Not[IntegerQ[q]]


Int[(g_*x_)^m_*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
  g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n)^p*(c+d*x^(-n))^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x] && EqQ[mn,-n]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  Defer[Int][(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x]


Int[u_^m_.*(a_.+b_.*v_^n_)^p_.*(c_.+d_.*v_^n_)^q_.*(e_+f_.*v_^n_)^r_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x],x,v] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && LinearPairQ[u,v,x]


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e1_+f1_.*x_^n2_.)^r_.*(e2_+f2_.*x_^n2_.)^r_.,x_Symbol] :=
  Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e1*e2+f1*f2*x^n)^r,x] /;
FreeQ[{a,b,c,d,e1,f1,e2,f2,g,m,n,p,q,r},x] && EqQ[n2-n/2] && EqQ[e2*f1+e1*f2] && (IntegerQ[r] || PositiveQ[e1] && PositiveQ[e2])


Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e1_+f1_.*x_^n2_.)^r_.*(e2_+f2_.*x_^n2_.)^r_.,x_Symbol] :=
  (e1+f1*x^(n/2))^FracPart[r]*(e2+f2*x^(n/2))^FracPart[r]/(e1*e2+f1*f2*x^n)^FracPart[r]*
    Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e1*e2+f1*f2*x^n)^r,x] /;
FreeQ[{a,b,c,d,e1,f1,e2,f2,g,m,n,p,q,r},x] && EqQ[n2-n/2] && EqQ[e2*f1+e1*f2]



