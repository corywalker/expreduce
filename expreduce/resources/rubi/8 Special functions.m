(* ::Package:: *)

(* ::Section:: *)
(*Special Function Rules*)


(* ::Subsection::Closed:: *)
(*8.1 Error functions*)


Int[Erf[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*Erf[a+b*x]/b + 1/(b*Sqrt[Pi]*E^(a+b*x)^2) /;
FreeQ[{a,b},x]


Int[Erfc[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*Erfc[a+b*x]/b - 1/(b*Sqrt[Pi]*E^(a+b*x)^2) /;
FreeQ[{a,b},x]


Int[Erfi[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*Erfi[a+b*x]/b - E^(a+b*x)^2/(b*Sqrt[Pi]) /;
FreeQ[{a,b},x]


Int[Erf[b_.*x_]/x_,x_Symbol] :=
  2*b*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},-b^2*x^2] /;
FreeQ[b,x]


Int[Erfc[b_.*x_]/x_,x_Symbol] :=
  Log[x] - Int[Erf[b*x]/x,x] /;
FreeQ[b,x]


Int[Erfi[b_.*x_]/x_,x_Symbol] :=
  2*b*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},b^2*x^2] /;
FreeQ[b,x]


Int[x_^m_.*Erf[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*Erf[a+b*x]/(m+1) -
  2*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)/E^(a+b*x)^2,x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[x_^m_.*Erfc[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*Erfc[a+b*x]/(m+1) +
  2*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)/E^(a+b*x)^2,x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[x_^m_.*Erfi[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*Erfi[a+b*x]/(m+1) -
  2*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)*E^(a+b*x)^2,x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[x_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
  E^(c+d*x^2)*Erf[a+b*x]/(2*d) - 
  b/(d*Sqrt[Pi])*Int[E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] /;
FreeQ[{a,b,c,d},x]


Int[x_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
  E^(c+d*x^2)*Erfc[a+b*x]/(2*d) + 
  b/(d*Sqrt[Pi])*Int[E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] /;
FreeQ[{a,b,c,d},x]


Int[x_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
  E^(c+d*x^2)*Erfi[a+b*x]/(2*d) - 
  b/(d*Sqrt[Pi])*Int[E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] /;
FreeQ[{a,b,c,d},x]


Int[x_^m_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
  x^(m-1)*E^(c+d*x^2)*Erf[a+b*x]/(2*d) - 
  b/(d*Sqrt[Pi])*Int[x^(m-1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] - 
  (m-1)/(2*d)*Int[x^(m-2)*E^(c+d*x^2)*Erf[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>1


Int[x_^m_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
  x^(m-1)*E^(c+d*x^2)*Erfc[a+b*x]/(2*d) + 
  b/(d*Sqrt[Pi])*Int[x^(m-1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] - 
  (m-1)/(2*d)*Int[x^(m-2)*E^(c+d*x^2)*Erfc[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>1


Int[x_^m_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
  x^(m-1)*E^(c+d*x^2)*Erfi[a+b*x]/(2*d) - 
  b/(d*Sqrt[Pi])*Int[x^(m-1)*E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] - 
  (m-1)/(2*d)*Int[x^(m-2)*E^(c+d*x^2)*Erfi[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>1


Int[E^(c_.+d_.*x_^2)*Erf[b_.*x_]/x_,x_Symbol] :=
  2*b*E^c*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1},{3/2,3/2},d*x^2] /;
FreeQ[b,x] && EqQ[d-b^2]


Int[E^(c_.+d_.*x_^2)*Erfc[b_.*x_]/x_,x_Symbol] :=
  Int[E^(c+d*x^2)/x,x] - Int[E^(c+d*x^2)*Erf[b*x]/x,x] /;
FreeQ[b,x] && EqQ[d-b^2]


Int[E^(c_.+d_.*x_^2)*Erfi[b_.*x_]/x_,x_Symbol] :=
  2*b*E^c*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1},{3/2,3/2},d*x^2] /;
FreeQ[b,x] && EqQ[d+b^2]


Int[x_^m_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*E^(c+d*x^2)*Erf[a+b*x]/(m+1) - 
  2*b/((m+1)*Sqrt[Pi])*Int[x^(m+1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] - 
  2*d/(m+1)*Int[x^(m+2)*E^(c+d*x^2)*Erf[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[x_^m_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*E^(c+d*x^2)*Erfc[a+b*x]/(m+1) + 
  2*b/((m+1)*Sqrt[Pi])*Int[x^(m+1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] - 
  2*d/(m+1)*Int[x^(m+2)*E^(c+d*x^2)*Erfc[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[x_^m_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*E^(c+d*x^2)*Erfi[a+b*x]/(m+1) - 
  2*b/((m+1)*Sqrt[Pi])*Int[x^(m+1)*E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] - 
  2*d/(m+1)*Int[x^(m+2)*E^(c+d*x^2)*Erfi[a+b*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[Erf[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*Erf[a+b*x]^2/b -
  4/Sqrt[Pi]*Int[(a+b*x)*Erf[a+b*x]/E^(a+b*x)^2,x] /;
FreeQ[{a,b},x]


Int[Erfc[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*Erfc[a+b*x]^2/b +
  4/Sqrt[Pi]*Int[(a+b*x)*Erfc[a+b*x]/E^(a+b*x)^2,x] /;
FreeQ[{a,b},x]


Int[Erfi[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*Erfi[a+b*x]^2/b -
  4/Sqrt[Pi]*Int[(a+b*x)*E^(a+b*x)^2*Erfi[a+b*x],x] /;
FreeQ[{a,b},x]


Int[x_^m_.*Erf[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*Erf[b*x]^2/(m+1) -
  4*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)*E^(-b^2*x^2)*Erf[b*x],x] /;
FreeQ[b,x] && IntegerQ[m] && m!=-1 && (m>0 || OddQ[m])


Int[x_^m_.*Erfc[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*Erfc[b*x]^2/(m+1) +
  4*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)*E^(-b^2*x^2)*Erfc[b*x],x] /;
FreeQ[b,x] && IntegerQ[m] && m+1!=0 && (m>0 || OddQ[m])


Int[x_^m_.*Erfi[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*Erfi[b*x]^2/(m+1) -
  4*b/(Sqrt[Pi]*(m+1))*Int[x^(m+1)*E^(b^2*x^2)*Erfi[b*x],x] /;
FreeQ[b,x] && IntegerQ[m] && m+1!=0 && (m>0 || OddQ[m])


Int[x_^m_.*Erf[a_+b_.*x_]^2,x_Symbol] :=
  1/b*Subst[Int[(-a/b+x/b)^m*Erf[x]^2,x],x,a+b*x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m]


Int[x_^m_.*Erfc[a_+b_.*x_]^2,x_Symbol] :=
  1/b*Subst[Int[(-a/b+x/b)^m*Erfc[x]^2,x],x,a+b*x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m]


Int[x_^m_.*Erfi[a_+b_.*x_]^2,x_Symbol] :=
  1/b*Subst[Int[(-a/b+x/b)^m*Erfi[x]^2,x],x,a+b*x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m]





(* ::Subsection::Closed:: *)
(*8.2 Fresnel integral functions*)


Int[FresnelS[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*FresnelS[a+b*x]/b + Cos[Pi/2*(a+b*x)^2]/(b*Pi) /;
FreeQ[{a,b},x]


Int[FresnelC[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*FresnelC[a+b*x]/b - Sin[Pi/2*(a+b*x)^2]/(b*Pi) /;
FreeQ[{a,b},x]


Int[FresnelS[b_.*x_]/x_,x_Symbol] :=
  1/2*I*b*x*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},-1/2*I*b^2*Pi*x^2] - 
  1/2*I*b*x*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},1/2*I*b^2*Pi*x^2] /;
FreeQ[b,x]


Int[FresnelC[b_.*x_]/x_,x_Symbol] :=
  1/2*b*x*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},-1/2*I*b^2*Pi*x^2] + 
  1/2*b*x*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},1/2*I*b^2*Pi*x^2] /;
FreeQ[b,x]


Int[x_^m_.*FresnelS[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*FresnelS[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)*Sin[Pi/2*(a+b*x)^2],x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[x_^m_.*FresnelC[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*FresnelC[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)*Cos[Pi/2*(a+b*x)^2],x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[FresnelS[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*FresnelS[a+b*x]^2/b -
  2*Int[(a+b*x)*Sin[Pi/2*(a+b*x)^2]*FresnelS[a+b*x],x] /;
FreeQ[{a,b},x]


Int[FresnelC[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*FresnelC[a+b*x]^2/b -
  2*Int[(a+b*x)*Cos[Pi/2*(a+b*x)^2]*FresnelC[a+b*x],x] /;
FreeQ[{a,b},x]


Int[x_^m_*FresnelS[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*FresnelS[b*x]^2/(m+1) -
  2*b/(m+1)*Int[x^(m+1)*Sin[Pi/2*b^2*x^2]*FresnelS[b*x],x] /;
FreeQ[b,x] && IntegerQ[m] && m+1!=0 && (m>0 && EvenQ[m] || Mod[m,4]==3)


Int[x_^m_*FresnelC[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*FresnelC[b*x]^2/(m+1) -
  2*b/(m+1)*Int[x^(m+1)*Cos[Pi/2*b^2*x^2]*FresnelC[b*x],x] /;
FreeQ[b,x] && IntegerQ[m] && m+1!=0 && (m>0 && EvenQ[m] || Mod[m,4]==3)


(* Int[x_^m_.*FresnelS[a_+b_.*x_]^2,x_Symbol] :=
  1/b*Subst[Int[(-a/b+x/b)^m*FresnelS[x]^2,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0 *)


(* Int[x_^m_.*FresnelC[a_+b_.*x_]^2,x_Symbol] :=
  1/b*Subst[Int[(-a/b+x/b)^m*FresnelC[x]^2,x],x,a+b*x] /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0 *)


Int[x_*Sin[c_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  -Cos[Pi/2*b^2*x^2]*FresnelS[b*x]/(Pi*b^2) +
  1/(2*Pi*b)*Int[Sin[Pi*b^2*x^2],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2]


Int[x_*Cos[c_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  Sin[Pi/2*b^2*x^2]*FresnelC[b*x]/(Pi*b^2) -
  1/(2*Pi*b)*Int[Sin[Pi*b^2*x^2],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2]


Int[x_^m_*Sin[c_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  -x^(m-1)*Cos[Pi/2*b^2*x^2]*FresnelS[b*x]/(Pi*b^2) +
  1/(2*Pi*b)*Int[x^(m-1)*Sin[Pi*b^2*x^2],x] +
  (m-1)/(Pi*b^2)*Int[x^(m-2)*Cos[Pi/2*b^2*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2] && IntegerQ[m] && m>1 && Not[Mod[m,4]==2]


Int[x_^m_*Cos[c_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  x^(m-1)*Sin[Pi/2*b^2*x^2]*FresnelC[b*x]/(Pi*b^2) -
  1/(2*Pi*b)*Int[x^(m-1)*Sin[Pi*b^2*x^2],x] -
  (m-1)/(Pi*b^2)*Int[x^(m-2)*Sin[Pi/2*b^2*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2] && IntegerQ[m] && m>1 && Not[Mod[m,4]==2]


Int[x_^m_*Sin[c_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  x^(m+1)*Sin[Pi/2*b^2*x^2]*FresnelS[b*x]/(m+1) - b*x^(m+2)/(2*(m+1)*(m+2)) +
  b/(2*(m+1))*Int[x^(m+1)*Cos[Pi*b^2*x^2],x] -
  Pi*b^2/(m+1)*Int[x^(m+2)*Cos[Pi/2*b^2*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2] && IntegerQ[m] && m<-2 && Mod[m,4]==0


Int[x_^m_*Cos[c_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  x^(m+1)*Cos[Pi/2*b^2*x^2]*FresnelC[b*x]/(m+1) - b*x^(m+2)/(2*(m+1)*(m+2)) -
  b/(2*(m+1))*Int[x^(m+1)*Cos[Pi*b^2*x^2],x] +
  Pi*b^2/(m+1)*Int[x^(m+2)*Sin[Pi/2*b^2*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2] && IntegerQ[m] && m<-2 && Mod[m,4]==0


Int[x_*Cos[c_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  Sin[Pi/2*b^2*x^2]*FresnelS[b*x]/(Pi*b^2) - x/(2*Pi*b) +
  1/(2*Pi*b)*Int[Cos[Pi*b^2*x^2],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2]


Int[x_*Sin[c_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  -Cos[Pi/2*b^2*x^2]*FresnelC[b*x]/(Pi*b^2) + x/(2*Pi*b) +
  1/(2*Pi*b)*Int[Cos[Pi*b^2*x^2],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2]


Int[x_^m_*Cos[c_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  x^(m-1)*Sin[Pi/2*b^2*x^2]*FresnelS[b*x]/(Pi*b^2) - x^m/(2*b*m*Pi) +
  1/(2*Pi*b)*Int[x^(m-1)*Cos[Pi*b^2*x^2],x] -
  (m-1)/(Pi*b^2)*Int[x^(m-2)*Sin[Pi/2*b^2*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2] && IntegerQ[m] && m>1 && Not[Mod[m,4]==0]


Int[x_^m_*Sin[c_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  -x^(m-1)*Cos[Pi/2*b^2*x^2]*FresnelC[b*x]/(Pi*b^2) + x^m/(2*b*m*Pi) +
  1/(2*Pi*b)*Int[x^(m-1)*Cos[Pi*b^2*x^2],x] +
  (m-1)/(Pi*b^2)*Int[x^(m-2)*Cos[Pi/2*b^2*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2] && IntegerQ[m] && m>1 && Not[Mod[m,4]==0]


Int[x_^m_*Cos[c_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
  x^(m+1)*Cos[Pi/2*b^2*x^2]*FresnelS[b*x]/(m+1) -
  b/(2*(m+1))*Int[x^(m+1)*Sin[Pi*b^2*x^2],x] +
  Pi*b^2/(m+1)*Int[x^(m+2)*Sin[Pi/2*b^2*x^2]*FresnelS[b*x],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2] && IntegerQ[m] && m<-1 && Mod[m,4]==2


Int[x_^m_*Sin[c_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
  x^(m+1)*Sin[Pi/2*b^2*x^2]*FresnelC[b*x]/(m+1) -
  b/(2*(m+1))*Int[x^(m+1)*Sin[Pi*b^2*x^2],x] -
  Pi*b^2/(m+1)*Int[x^(m+2)*Cos[Pi/2*b^2*x^2]*FresnelC[b*x],x] /;
FreeQ[{b,c},x] && EqQ[c-Pi/2*b^2] && IntegerQ[m] && m<-1 && Mod[m,4]==2





(* ::Subsection::Closed:: *)
(*8.3 Exponential integral functions*)


Int[ExpIntegralE[n_,a_.+b_.*x_],x_Symbol] :=
  -ExpIntegralE[n+1,a+b*x]/b /;
FreeQ[{a,b,n},x]


Int[x_^m_.*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
  -x^m*ExpIntegralE[n+1,b*x]/b + 
  m/b*Int[x^(m-1)*ExpIntegralE[n+1,b*x],x] /;
FreeQ[b,x] && EqQ[m+n] && PositiveIntegerQ[m]


Int[ExpIntegralE[1,b_.*x_]/x_,x_Symbol] :=
  b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] - EulerGamma*Log[x] - 1/2*Log[b*x]^2 /;
FreeQ[b,x]


Int[x_^m_*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
  x^(m+1)*ExpIntegralE[n,b*x]/(m+1) +
  b/(m+1)*Int[x^(m+1)*ExpIntegralE[n-1,b*x],x] /;
FreeQ[b,x] && EqQ[m+n] && IntegerQ[m] && m<-1


Int[x_^m_*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
  x^m*Gamma[m+1]*Log[x]/(b*(b*x)^m) - x^(m+1)*HypergeometricPFQ[{m+1,m+1},{m+2,m+2},-b*x]/(m+1)^2 /;
FreeQ[{b,m,n},x] && EqQ[m+n] && Not[IntegerQ[m]]


Int[x_^m_.*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
  x^(m+1)*ExpIntegralE[n,b*x]/(m+n) - x^(m+1)*ExpIntegralE[-m,b*x]/(m+n) /;
FreeQ[{b,m,n},x] && NeQ[m+n]


Int[x_^m_.*ExpIntegralE[n_,a_+b_.*x_],x_Symbol] :=
  -x^m*ExpIntegralE[n+1,a+b*x]/b +
  m/b*Int[x^(m-1)*ExpIntegralE[n+1,a+b*x],x] /;
FreeQ[{a,b,m,n},x] && (PositiveIntegerQ[m] || NegativeIntegerQ[n] || RationalQ[m,n] && m>0 && n<-1)


Int[x_^m_.*ExpIntegralE[n_,a_+b_.*x_],x_Symbol] :=
  x^(m+1)*ExpIntegralE[n,a+b*x]/(m+1) +
  b/(m+1)*Int[x^(m+1)*ExpIntegralE[n-1,a+b*x],x] /;
FreeQ[{a,b,m},x] && (PositiveIntegerQ[n] || RationalQ[m,n] && m<-1 && n>0) && NeQ[m+1]


Int[ExpIntegralEi[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*ExpIntegralEi[a+b*x]/b - E^(a+b*x)/b /;
FreeQ[{a,b},x]


Int[x_^m_.*ExpIntegralEi[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*ExpIntegralEi[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)*E^(a+b*x)/(a+b*x),x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[ExpIntegralEi[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*ExpIntegralEi[a+b*x]^2/b -
  2*Int[E^(a+b*x)*ExpIntegralEi[a+b*x],x] /;
FreeQ[{a,b},x]


Int[x_^m_.*ExpIntegralEi[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*ExpIntegralEi[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*E^(b*x)*ExpIntegralEi[b*x],x] /;
FreeQ[b,x] && PositiveIntegerQ[m]


Int[x_^m_.*ExpIntegralEi[a_+b_.*x_]^2,x_Symbol] :=
  x^(m+1)*ExpIntegralEi[a+b*x]^2/(m+1) +
  a*x^m*ExpIntegralEi[a+b*x]^2/(b*(m+1)) -
  2/(m+1)*Int[x^m*E^(a+b*x)*ExpIntegralEi[a+b*x],x] -
  a*m/(b*(m+1))*Int[x^(m-1)*ExpIntegralEi[a+b*x]^2,x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m]


(* Int[x_^m_.*ExpIntegralEi[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*ExpIntegralEi[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*ExpIntegralEi[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*E^(a+b*x)*ExpIntegralEi[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*ExpIntegralEi[a+b*x]^2,x] /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)


Int[E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
  E^(a+b*x)*ExpIntegralEi[c+d*x]/b -
  d/b*Int[E^(a+c+(b+d)*x)/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[x_^m_.*E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
  x^m*E^(a+b*x)*ExpIntegralEi[c+d*x]/b -
  d/b*Int[x^m*E^(a+c+(b+d)*x)/(c+d*x),x] -
  m/b*Int[x^(m-1)*E^(a+b*x)*ExpIntegralEi[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_*E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*E^(a+b*x)*ExpIntegralEi[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*E^(a+c+(b+d)*x)/(c+d*x),x] -
  b/(m+1)*Int[x^(m+1)*E^(a+b*x)*ExpIntegralEi[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[LogIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*LogIntegral[a+b*x]/b - ExpIntegralEi[2*Log[a+b*x]]/b /;
FreeQ[{a,b},x]


Int[LogIntegral[b_.*x_]/x_,x_Symbol] :=
  -b*x + Log[b*x]*LogIntegral[b*x] /;
FreeQ[b,x]


Int[x_^m_.*LogIntegral[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*LogIntegral[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)/Log[a+b*x],x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]





(* ::Subsection::Closed:: *)
(*8.4 Trig integral functions*)


Int[SinIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*SinIntegral[a+b*x]/b + Cos[a+b*x]/b/;
FreeQ[{a,b},x]


Int[CosIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*CosIntegral[a+b*x]/b - Sin[a+b*x]/b /;
FreeQ[{a,b},x]


Int[SinIntegral[b_.*x_]/x_,x_Symbol] :=
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-I*b*x] + 
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},I*b*x] /;
FreeQ[b,x]


Int[CosIntegral[b_.*x_]/x_,x_Symbol] :=
  -1/2*I*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-I*b*x] + 
  1/2*I*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},I*b*x] + 
  EulerGamma*Log[x] + 
  1/2*Log[b*x]^2 /;
FreeQ[b,x]


Int[x_^m_.*SinIntegral[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*SinIntegral[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)*Sin[a+b*x]/(a+b*x),x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[x_^m_.*CosIntegral[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*CosIntegral[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)*Cos[a+b*x]/(a+b*x),x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[SinIntegral[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*SinIntegral[a+b*x]^2/b -
  2*Int[Sin[a+b*x]*SinIntegral[a+b*x],x] /;
FreeQ[{a,b},x]


Int[CosIntegral[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*CosIntegral[a+b*x]^2/b -
  2*Int[Cos[a+b*x]*CosIntegral[a+b*x],x] /;
FreeQ[{a,b},x]


Int[x_^m_.*SinIntegral[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*SinIntegral[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*Sin[b*x]*SinIntegral[b*x],x] /;
FreeQ[b,x] && PositiveIntegerQ[m]


Int[x_^m_.*CosIntegral[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*CosIntegral[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*Cos[b*x]*CosIntegral[b*x],x] /;
FreeQ[b,x] && PositiveIntegerQ[m]


Int[x_^m_.*SinIntegral[a_+b_.*x_]^2,x_Symbol] :=
  x^(m+1)*SinIntegral[a+b*x]^2/(m+1) +
  a*x^m*SinIntegral[a+b*x]^2/(b*(m+1)) -
  2/(m+1)*Int[x^m*Sin[a+b*x]*SinIntegral[a+b*x],x] -
  a*m/(b*(m+1))*Int[x^(m-1)*SinIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m]


Int[x_^m_.*CosIntegral[a_+b_.*x_]^2,x_Symbol] :=
  x^(m+1)*CosIntegral[a+b*x]^2/(m+1) +
  a*x^m*CosIntegral[a+b*x]^2/(b*(m+1)) -
  2/(m+1)*Int[x^m*Cos[a+b*x]*CosIntegral[a+b*x],x] -
  a*m/(b*(m+1))*Int[x^(m-1)*CosIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m]


(* Int[x_^m_.*SinIntegral[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*SinIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*SinIntegral[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*Sin[a+b*x]*SinIntegral[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*SinIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)


(* Int[x_^m_.*CosIntegral[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*CosIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*CosIntegral[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*Cos[a+b*x]*CosIntegral[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*CosIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)


Int[Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  -Cos[a+b*x]*SinIntegral[c+d*x]/b +
  d/b*Int[Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  Sin[a+b*x]*CosIntegral[c+d*x]/b -
  d/b*Int[Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[x_^m_.*Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  -x^m*Cos[a+b*x]*SinIntegral[c+d*x]/b +
  d/b*Int[x^m*Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] +
  m/b*Int[x^(m-1)*Cos[a+b*x]*SinIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_.*Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  x^m*Sin[a+b*x]*CosIntegral[c+d*x]/b -
  d/b*Int[x^m*Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] -
  m/b*Int[x^(m-1)*Sin[a+b*x]*CosIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_*Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*Sin[a+b*x]*SinIntegral[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] -
  b/(m+1)*Int[x^(m+1)*Cos[a+b*x]*SinIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[x_^m_.*Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*Cos[a+b*x]*CosIntegral[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] +
  b/(m+1)*Int[x^(m+1)*Sin[a+b*x]*CosIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  Sin[a+b*x]*SinIntegral[c+d*x]/b -
  d/b*Int[Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  -Cos[a+b*x]*CosIntegral[c+d*x]/b +
  d/b*Int[Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[x_^m_.*Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  x^m*Sin[a+b*x]*SinIntegral[c+d*x]/b -
  d/b*Int[x^m*Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] -
  m/b*Int[x^(m-1)*Sin[a+b*x]*SinIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_.*Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  -x^m*Cos[a+b*x]*CosIntegral[c+d*x]/b +
  d/b*Int[x^m*Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] +
  m/b*Int[x^(m-1)*Cos[a+b*x]*CosIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_.*Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*Cos[a+b*x]*SinIntegral[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] +
  b/(m+1)*Int[x^(m+1)*Sin[a+b*x]*SinIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[x_^m_*Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*Sin[a+b*x]*CosIntegral[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] -
  b/(m+1)*Int[x^(m+1)*Cos[a+b*x]*CosIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1





(* ::Subsection::Closed:: *)
(*8.5 Hyperbolic integral functions*)


Int[SinhIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*SinhIntegral[a+b*x]/b - Cosh[a+b*x]/b/;
FreeQ[{a,b},x]


Int[CoshIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*CoshIntegral[a+b*x]/b - Sinh[a+b*x]/b /;
FreeQ[{a,b},x]


Int[SinhIntegral[b_.*x_]/x_,x_Symbol] :=
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] + 
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},b*x] /;
FreeQ[b,x]


Int[CoshIntegral[b_.*x_]/x_,x_Symbol] :=
  -1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] + 
  1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},b*x] + 
  EulerGamma*Log[x] + 
  1/2*Log[b*x]^2 /;
FreeQ[b,x]


Int[x_^m_.*SinhIntegral[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*SinhIntegral[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)*Sinh[a+b*x]/(a+b*x),x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[x_^m_.*CoshIntegral[a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*CoshIntegral[a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)*Cosh[a+b*x]/(a+b*x),x] /;
FreeQ[{a,b,m},x] && NeQ[m+1]


Int[SinhIntegral[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*SinhIntegral[a+b*x]^2/b -
  2*Int[Sinh[a+b*x]*SinhIntegral[a+b*x],x] /;
FreeQ[{a,b},x]


Int[CoshIntegral[a_.+b_.*x_]^2,x_Symbol] :=
  (a+b*x)*CoshIntegral[a+b*x]^2/b -
  2*Int[Cosh[a+b*x]*CoshIntegral[a+b*x],x] /;
FreeQ[{a,b},x]


Int[x_^m_.*SinhIntegral[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*SinhIntegral[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*Sinh[b*x]*SinhIntegral[b*x],x] /;
FreeQ[b,x] && PositiveIntegerQ[m]


Int[x_^m_.*CoshIntegral[b_.*x_]^2,x_Symbol] :=
  x^(m+1)*CoshIntegral[b*x]^2/(m+1) -
  2/(m+1)*Int[x^m*Cosh[b*x]*CoshIntegral[b*x],x] /;
FreeQ[b,x] && PositiveIntegerQ[m]


Int[x_^m_.*SinhIntegral[a_+b_.*x_]^2,x_Symbol] :=
  x^(m+1)*SinhIntegral[a+b*x]^2/(m+1) +
  a*x^m*SinhIntegral[a+b*x]^2/(b*(m+1)) -
  2/(m+1)*Int[x^m*Sinh[a+b*x]*SinhIntegral[a+b*x],x] -
  a*m/(b*(m+1))*Int[x^(m-1)*SinhIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m]


Int[x_^m_.*CoshIntegral[a_+b_.*x_]^2,x_Symbol] :=
  x^(m+1)*CoshIntegral[a+b*x]^2/(m+1) +
  a*x^m*CoshIntegral[a+b*x]^2/(b*(m+1)) -
  2/(m+1)*Int[x^m*Cosh[a+b*x]*CoshIntegral[a+b*x],x] -
  a*m/(b*(m+1))*Int[x^(m-1)*CoshIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m]


(* Int[x_^m_.*SinhIntegral[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*SinhIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*SinhIntegral[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*Sinh[a+b*x]*SinhIntegral[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*SinhIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)


(* Int[x_^m_.*CoshIntegral[a_+b_.*x_]^2,x_Symbol] :=
  b*x^(m+2)*CoshIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*CoshIntegral[a+b*x]^2/(m+1) -
  2*b/(a*(m+1))*Int[x^(m+1)*Cosh[a+b*x]*CoshIntegral[a+b*x],x] -
  b*(m+2)/(a*(m+1))*Int[x^(m+1)*CoshIntegral[a+b*x]^2,x] /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)


Int[Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  Cosh[a+b*x]*SinhIntegral[c+d*x]/b -
  d/b*Int[Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  Sinh[a+b*x]*CoshIntegral[c+d*x]/b -
  d/b*Int[Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[x_^m_.*Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  x^m*Cosh[a+b*x]*SinhIntegral[c+d*x]/b -
  d/b*Int[x^m*Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
  m/b*Int[x^(m-1)*Cosh[a+b*x]*SinhIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0


Int[x_^m_.*Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  x^m*Sinh[a+b*x]*CoshIntegral[c+d*x]/b -
  d/b*Int[x^m*Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
  m/b*Int[x^(m-1)*Sinh[a+b*x]*CoshIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0


Int[x_^m_*Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*Sinh[a+b*x]*SinhIntegral[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
  b/(m+1)*Int[x^(m+1)*Cosh[a+b*x]*SinhIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[x_^m_.*Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*Cosh[a+b*x]*CoshIntegral[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
  b/(m+1)*Int[x^(m+1)*Sinh[a+b*x]*CoshIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  Sinh[a+b*x]*SinhIntegral[c+d*x]/b -
  d/b*Int[Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  Cosh[a+b*x]*CoshIntegral[c+d*x]/b -
  d/b*Int[Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d},x]


Int[x_^m_.*Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  x^m*Sinh[a+b*x]*SinhIntegral[c+d*x]/b -
  d/b*Int[x^m*Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
  m/b*Int[x^(m-1)*Sinh[a+b*x]*SinhIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_.*Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  x^m*Cosh[a+b*x]*CoshIntegral[c+d*x]/b -
  d/b*Int[x^m*Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
  m/b*Int[x^(m-1)*Cosh[a+b*x]*CoshIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && PositiveIntegerQ[m]


Int[x_^m_.*Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*Cosh[a+b*x]*SinhIntegral[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
  b/(m+1)*Int[x^(m+1)*Sinh[a+b*x]*SinhIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1


Int[x_^m_*Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
  x^(m+1)*Sinh[a+b*x]*CoshIntegral[c+d*x]/(m+1) -
  d/(m+1)*Int[x^(m+1)*Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
  b/(m+1)*Int[x^(m+1)*Cosh[a+b*x]*CoshIntegral[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1





(* ::Subsection::Closed:: *)
(*8.6 Gamma functions*)


Int[Gamma[n_,a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*Gamma[n,a+b*x]/b -
  Gamma[n+1,a+b*x]/b /;
FreeQ[{a,b},x]


Int[Gamma[n_,b_*x_]/x_,x_Symbol] :=
  Gamma[n]*Log[x] - (b*x)^n/n^2*HypergeometricPFQ[{n,n},{1+n,1+n},-b*x] /;
FreeQ[{b,n},x] && Not[IntegerQ[n] && n<=0]


Int[x_^m_.*Gamma[n_,b_*x_],x_Symbol] :=
  x^(m+1)*Gamma[n,b*x]/(m+1) - 
  x^m*Gamma[m+n+1,b*x]/(b*(m+1)*(b*x)^m) /;
FreeQ[{b,m,n},x] && NeQ[m+1]


Int[x_^m_.*Gamma[n_,a_+b_.*x_],x_Symbol] :=
  Block[{$UseGamma=True},
    x^(m+1)*Gamma[n,a+b*x]/(m+1) + 
    b/(m+1)*Int[x^(m+1)*(a+b*x)^(n-1)/E^(a+b*x),x]] /;
FreeQ[{a,b,m,n},x] && (PositiveIntegerQ[m] || PositiveIntegerQ[n] || IntegersQ[m,n]) && NeQ[m+1]


(* Int[x_^m_.*Gamma[n_,a_+b_.*x_],x_Symbol] :=
  x^m*(a+b*x)*Gamma[n,a+b*x]/(b*(m+1)) -
  x^m*Gamma[n+1,a+b*x]/(b*(m+1)) -
  a*m/(b*(m+1))*Int[x^(m-1)*Gamma[n,a+b*x],x] +
  m/(b*(m+1))*Int[x^(m-1)*Gamma[n+1,a+b*x],x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>0 *)


Int[LogGamma[a_.+b_.*x_],x_Symbol] :=
  PolyGamma[-2,a+b*x]/b /;
FreeQ[{a,b},x]


Int[x_^m_.*LogGamma[a_.+b_.*x_],x_Symbol] :=
  x^m*PolyGamma[-2,a+b*x]/b -
  m/b*Int[x^(m-1)*PolyGamma[-2,a+b*x],x] /;
FreeQ[{a,b},x] && RationalQ[m] && m>0


Int[PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
  PolyGamma[n-1,a+b*x]/b /;
FreeQ[{a,b,n},x]


Int[x_^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
  x^m*PolyGamma[n-1,a+b*x]/b -
  m/b*Int[x^(m-1)*PolyGamma[n-1,a+b*x],x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>0


Int[x_^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*PolyGamma[n,a+b*x]/(m+1) -
  b/(m+1)*Int[x^(m+1)*PolyGamma[n+1,a+b*x],x] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1


Int[Gamma[a_.+b_.*x_]^n_.*PolyGamma[0,a_.+b_.*x_],x_Symbol] :=
  Gamma[a+b*x]^n/(b*n) /;
FreeQ[{a,b,n},x]


Int[((a_.+b_.*x_)!)^n_.*PolyGamma[0,c_.+b_.*x_],x_Symbol] :=
  ((a+b*x)!)^n/(b*n) /;
FreeQ[{a,b,c,n},x] && EqQ[a-c+1]





(* ::Subsection::Closed:: *)
(*8.7 Zeta function*)


Int[Zeta[2,a_.+b_.*x_],x_Symbol] :=
  Int[PolyGamma[1,a+b*x],x] /;
FreeQ[{a,b},x]


Int[Zeta[s_,a_.+b_.*x_],x_Symbol] :=
  -Zeta[s-1,a+b*x]/(b*(s-1)) /;
FreeQ[{a,b,s},x] && NeQ[s-1] && NeQ[s-2]


Int[x_^m_.*Zeta[2,a_.+b_.*x_],x_Symbol] :=
  Int[x^m*PolyGamma[1,a+b*x],x] /;
FreeQ[{a,b},x] && RationalQ[m]


Int[x_^m_.*Zeta[s_,a_.+b_.*x_],x_Symbol] :=
  -x^m*Zeta[s-1,a+b*x]/(b*(s-1)) +
  m/(b*(s-1))*Int[x^(m-1)*Zeta[s-1,a+b*x],x] /;
FreeQ[{a,b,s},x] && NeQ[s-1] && NeQ[s-2] && RationalQ[m] && m>0


Int[x_^m_.*Zeta[s_,a_.+b_.*x_],x_Symbol] :=
  x^(m+1)*Zeta[s,a+b*x]/(m+1) +
  b*s/(m+1)*Int[x^(m+1)*Zeta[s+1,a+b*x],x] /;
FreeQ[{a,b,s},x] && NeQ[s-1] && NeQ[s-2] && RationalQ[m] && m<-1





(* ::Subsection::Closed:: *)
(*8.8 Polylogarithm function*)


Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  x*PolyLog[n,a*(b*x^p)^q] -
  p*q*Int[PolyLog[n-1,a*(b*x^p)^q],x] /;
FreeQ[{a,b,p,q},x] && RationalQ[n] && n>0


Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  x*PolyLog[n+1,a*(b*x^p)^q]/(p*q) -
  1/(p*q)*Int[PolyLog[n+1,a*(b*x^p)^q],x] /;
FreeQ[{a,b,p,q},x] && RationalQ[n] && n<-1


Int[PolyLog[n_,c_.*(a_.+b_.*x_)^p_.]/(d_.+e_.*x_),x_Symbol] :=
  PolyLog[n+1,c*(a+b*x)^p]/(e*p) /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*d-a*e]


Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.]/x_,x_Symbol] :=
  PolyLog[n+1,a*(b*x^p)^q]/(p*q) /;
FreeQ[{a,b,n,p,q},x]


Int[x_^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  x^(m+1)*PolyLog[n,a*(b*x^p)^q]/(m+1) -
  p*q/(m+1)*Int[x^m*PolyLog[n-1,a*(b*x^p)^q],x] /;
FreeQ[{a,b,m,p,q},x] && NeQ[m+1] && RationalQ[n] && n>0


Int[x_^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
  x^(m+1)*PolyLog[n+1,a*(b*x^p)^q]/(p*q) -
  (m+1)/(p*q)*Int[x^m*PolyLog[n+1,a*(b*x^p)^q],x] /;
FreeQ[{a,b,m,p,q},x] && NeQ[m+1] && RationalQ[n] && n<-1


Int[Log[c_.*x_^m_.]^r_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.]/x_,x_Symbol] :=
  Log[c*x^m]^r*PolyLog[n+1,a*(b*x^p)^q]/(p*q) - 
  m*r/(p*q)*Int[Log[c*x^m]^(r-1)*PolyLog[n+1,a*(b*x^p)^q]/x,x] /;
FreeQ[{a,b,c,m,n,q,r},x] && RationalQ[r] && r>0


Int[PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
  x*PolyLog[n,c*(a+b*x)^p] -
  p*Int[PolyLog[n-1,c*(a+b*x)^p],x] +
  a*p*Int[PolyLog[n-1,c*(a+b*x)^p]/(a+b*x),x] /;
FreeQ[{a,b,c,p},x] && RationalQ[n] && n>0


Int[PolyLog[2,c_.*(a_.+b_.*x_)]/(d_.+e_.*x_),x_Symbol] :=
  Log[d+e*x]*PolyLog[2,c*(a+b*x)]/e + b/e*Int[Log[d+e*x]*Log[1-a*c-b*c*x]/(a+b*x),x] /;
FreeQ[{a,b,c,d,e},x]


Int[(d_.+e_.*x_)^m_.*PolyLog[2,c_.*(a_.+b_.*x_)],x_Symbol] :=
  (d+e*x)^(m+1)*PolyLog[2,c*(a+b*x)]/(e*(m+1)) + b/(e*(m+1))*Int[(d+e*x)^(m+1)*Log[1-a*c-b*c*x]/(a+b*x),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]


(* Int[x_^m_.*PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
  x^(m+1)*PolyLog[n,c*(a+b*x)^p]/(m+1) -
  b*p/(m+1)*Int[x^(m+1)*PolyLog[n-1,c*(a+b*x)^p]/(a+b*x),x] /;
FreeQ[{a,b,c,m,p},x] && RationalQ[n] && n>0 && PositiveIntegerQ[m] *)


Int[x_^m_.*PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
  -(a^(m+1)-b^(m+1)*x^(m+1))*PolyLog[n,c*(a+b*x)^p]/((m+1)*b^(m+1)) +
  p/((m+1)*b^m)*Int[ExpandIntegrand[PolyLog[n-1,c*(a+b*x)^p],(a^(m+1)-b^(m+1)*x^(m+1))/(a+b*x),x],x] /;
FreeQ[{a,b,c,p},x] && GtQ[n,0] && IntegerQ[m] && Not[EqQ[m,-1]]


Int[PolyLog[n_,d_.*(F_^(c_.*(a_.+b_.*x_)))^p_.],x_Symbol] :=
  PolyLog[n+1,d*(F^(c*(a+b*x)))^p]/(b*c*p*Log[F]) /;
FreeQ[{F,a,b,c,d,n,p},x]


Int[(e_.+f_.*x_)^m_.*PolyLog[n_,d_.*(F_^(c_.*(a_.+b_.*x_)))^p_.],x_Symbol] :=
  (e+f*x)^m*PolyLog[n+1,d*(F^(c*(a+b*x)))^p]/(b*c*p*Log[F]) - 
  f*m/(b*c*p*Log[F])*Int[(e+f*x)^(m-1)*PolyLog[n+1,d*(F^(c*(a+b*x)))^p],x] /;
FreeQ[{F,a,b,c,d,e,f,n,p},x] && RationalQ[m] && m>0


Int[u_*PolyLog[n_,v_],x_Symbol] :=
  With[{w=DerivativeDivides[v,u*v,x]},
  w*PolyLog[n+1,v] /;
 Not[FalseQ[w]]] /;
FreeQ[n,x]


Int[u_*Log[w_]*PolyLog[n_,v_],x_Symbol] :=
  With[{z=DerivativeDivides[v,u*v,x]},
  z*Log[w]*PolyLog[n+1,v] - 
  Int[SimplifyIntegrand[z*D[w,x]*PolyLog[n+1,v]/w,x],x] /;
 Not[FalseQ[z]]] /;
FreeQ[n,x] && InverseFunctionFreeQ[w,x]





(* ::Subsection::Closed:: *)
(*8.9 Product logarithm function*)


Int[(c_.*ProductLog[a_.+b_.*x_])^p_,x_Symbol] :=
  (a+b*x)*(c*ProductLog[a+b*x])^p/(b*(p+1)) +
  p/(c*(p+1))*Int[(c*ProductLog[a+b*x])^(p+1)/(1+ProductLog[a+b*x]),x] /;
FreeQ[{a,b,c},x] && RationalQ[p] && p<-1


Int[(c_.*ProductLog[a_.+b_.*x_])^p_.,x_Symbol] :=
  (a+b*x)*(c*ProductLog[a+b*x])^p/b -
  p*Int[(c*ProductLog[a+b*x])^p/(1+ProductLog[a+b*x]),x] /;
FreeQ[{a,b,c},x] && Not[RationalQ[p] && p<-1]


Int[x_^m_.*(c_.*ProductLog[a_+b_.*x_])^p_.,x_Symbol] :=
  1/b*Subst[Int[ExpandIntegrand[(c*ProductLog[x])^p,(-a/b+x/b)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,p},x] && PositiveIntegerQ[m]


Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
  x*(c*ProductLog[a*x^n])^p -
  n*p*Int[(c*ProductLog[a*x^n])^p/(1+ProductLog[a*x^n]),x] /;
FreeQ[{a,c,n,p},x] && (EqQ[n*(p-1)+1] || IntegerQ[p-1/2] && EqQ[n*(p-1/2)+1])


Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
  x*(c*ProductLog[a*x^n])^p/(n*p+1) +
  n*p/(c*(n*p+1))*Int[(c*ProductLog[a*x^n])^(p+1)/(1+ProductLog[a*x^n]),x] /;
FreeQ[{a,c,n},x] && (IntegerQ[p] && EqQ[n*(p+1)+1] || IntegerQ[p-1/2] && EqQ[n*(p+1/2)+1])


Int[(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(c*ProductLog[a*x^(-n)])^p/x^2,x],x,1/x] /;
FreeQ[{a,c,p},x] && NegativeIntegerQ[n]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_.,x_Symbol] :=
  x^(m+1)*(c*ProductLog[a*x^n])^p/(m+1) -
  n*p/(m+1)*Int[x^m*(c*ProductLog[a*x^n])^p/(1+ProductLog[a*x^n]),x] /;
FreeQ[{a,c,m,n,p},x] && NeQ[m+1] &&
(IntegerQ[p-1/2] && IntegerQ[2*Simplify[p+(m+1)/n]] && Simplify[p+(m+1)/n]>0 ||
 Not[IntegerQ[p-1/2]] && IntegerQ[Simplify[p+(m+1)/n]] && Simplify[p+(m+1)/n]>=0)


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_.,x_Symbol] :=
  x^(m+1)*(c*ProductLog[a*x^n])^p/(m+n*p+1) +
  n*p/(c*(m+n*p+1))*Int[x^m*(c*ProductLog[a*x^n])^(p+1)/(1+ProductLog[a*x^n]),x] /;
FreeQ[{a,c,m,n,p},x] &&
(EqQ[m+1] ||
 IntegerQ[p-1/2] && IntegerQ[Simplify[p+(m+1)/n]-1/2] && Simplify[p+(m+1)/n]<0 ||
 Not[IntegerQ[p-1/2]] && IntegerQ[Simplify[p+(m+1)/n]] && Simplify[p+(m+1)/n]<0)


Int[x_^m_.*(c_.*ProductLog[a_.*x_])^p_.,x_Symbol] :=
  Int[x^m*(c*ProductLog[a*x])^p/(1+ProductLog[a*x]),x] +
  1/c*Int[x^m*(c*ProductLog[a*x])^(p+1)/(1+ProductLog[a*x]),x] /;
FreeQ[{a,c,m},x]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(c*ProductLog[a*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,p},x] && IntegersQ[m,n] && n<0 && NeQ[m+1]


Int[1/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  (a+b*x)/(b*d*ProductLog[a+b*x]) /;
FreeQ[{a,b,d},x]


Int[ProductLog[a_.+b_.*x_]/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  d*x - 
  Int[1/(d+d*ProductLog[a+b*x]),x] /;
FreeQ[{a,b,d},x]


Int[(c_.*ProductLog[a_.+b_.*x_])^p_/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  c*(a+b*x)*(c*ProductLog[a+b*x])^(p-1)/(b*d) -
  c*p*Int[(c*ProductLog[a+b*x])^(p-1)/(d+d*ProductLog[a+b*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[p] && p>0


Int[1/(ProductLog[a_.+b_.*x_]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
  ExpIntegralEi[ProductLog[a+b*x]]/(b*d) /;
FreeQ[{a,b,d},x]


Int[1/(Sqrt[c_.*ProductLog[a_.+b_.*x_]]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
  Rt[Pi*c,2]*Erfi[Sqrt[c*ProductLog[a+b*x]]/Rt[c,2]]/(b*c*d) /;
FreeQ[{a,b,c,d},x] && PosQ[c]


Int[1/(Sqrt[c_.*ProductLog[a_.+b_.*x_]]*(d_+d_.*ProductLog[a_.+b_.*x_])),x_Symbol] :=
  Rt[-Pi*c,2]*Erf[Sqrt[c*ProductLog[a+b*x]]/Rt[-c,2]]/(b*c*d) /;
FreeQ[{a,b,c,d},x] && NegQ[c]


Int[(c_.*ProductLog[a_.+b_.*x_])^p_/(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  (a+b*x)*(c*ProductLog[a+b*x])^p/(b*d*(p+1)) -
  1/(c*(p+1))*Int[(c*ProductLog[a+b*x])^(p+1)/(d+d*ProductLog[a+b*x]),x] /;
FreeQ[{a,b,c,d},x] && RationalQ[p] && p<-1


Int[(c_.*ProductLog[a_.+b_.*x_])^p_./(d_+d_.*ProductLog[a_.+b_.*x_]),x_Symbol] :=
  Gamma[p+1,-ProductLog[a+b*x]]*(c*ProductLog[a+b*x])^p/(b*d*(-ProductLog[a+b*x])^p) /;
FreeQ[{a,b,c,d,p},x]


Int[x_^m_./(d_+d_.*ProductLog[a_+b_.*x_]),x_Symbol] :=
  1/b*Subst[Int[ExpandIntegrand[1/(d+d*ProductLog[x]),(-a/b+x/b)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,d},x] && PositiveIntegerQ[m]


Int[x_^m_.*(c_.*ProductLog[a_+b_.*x_])^p_./(d_+d_.*ProductLog[a_+b_.*x_]),x_Symbol] :=
  1/b*Subst[Int[ExpandIntegrand[(c*ProductLog[x])^p/(d+d*ProductLog[x]),(-a/b+x/b)^m,x],x],x,a+b*x] /;
FreeQ[{a,b,c,d,p},x] && PositiveIntegerQ[m]


Int[1/(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
  -Subst[Int[1/(x^2*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
FreeQ[{a,d},x] && NegativeIntegerQ[n]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  c*x*(c*ProductLog[a*x^n])^(p-1)/d /;
FreeQ[{a,c,d,n,p},x] && EqQ[n*(p-1)+1]


Int[ProductLog[a_.*x_^n_.]^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  a^p*ExpIntegralEi[-p*ProductLog[a*x^n]]/(d*n) /;
FreeQ[{a,d},x] && IntegerQ[1/n] && EqQ[p+1/n]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  Rt[Pi*c*n,2]/(d*n*a^(1/n)*c^(1/n))*Erfi[Sqrt[c*ProductLog[a*x^n]]/Rt[c*n,2]] /;
FreeQ[{a,c,d},x] && IntegerQ[1/n] && EqQ[p-1/2+1/n] && PosQ[c*n]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  Rt[-Pi*c*n,2]/(d*n*a^(1/n)*c^(1/n))*Erf[Sqrt[c*ProductLog[a*x^n]]/Rt[-c*n,2]] /;
FreeQ[{a,c,d},x] && IntegerQ[1/n] && EqQ[p-1/2+1/n] && NegQ[c*n]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  c*x*(c*ProductLog[a*x^n])^(p-1)/d -
  c*(n*(p-1)+1)*Int[(c*ProductLog[a*x^n])^(p-1)/(d+d*ProductLog[a*x^n]),x] /;
FreeQ[{a,c,d},x] && RationalQ[n,p] && n>0 && n*(p-1)+1>0


Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  x*(c*ProductLog[a*x^n])^p/(d*(n*p+1)) -
  1/(c*(n*p+1))*Int[(c*ProductLog[a*x^n])^(p+1)/(d+d*ProductLog[a*x^n]),x] /;
FreeQ[{a,c,d},x] && RationalQ[n,p] && n>0 && n*p+1<0


Int[(c_.*ProductLog[a_.*x_^n_])^p_./(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
  -Subst[Int[(c*ProductLog[a*x^(-n)])^p/(x^2*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
FreeQ[{a,c,d,p},x] && NegativeIntegerQ[n]


Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
  x^(m+1)/(d*(m+1)*ProductLog[a*x]) -
  m/(m+1)*Int[x^m/(ProductLog[a*x]*(d+d*ProductLog[a*x])),x] /;
FreeQ[{a,d},x] && RationalQ[m] && m>0


Int[1/(x_*(d_+d_.*ProductLog[a_.*x_])),x_Symbol] :=
  Log[ProductLog[a*x]]/d /;
FreeQ[{a,d},x]


Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
  x^(m+1)/(d*(m+1)) -
  Int[x^m*ProductLog[a*x]/(d+d*ProductLog[a*x]),x] /;
FreeQ[{a,d},x] && RationalQ[m] && m<-1


Int[x_^m_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
  x^m*Gamma[m+1,-(m+1)*ProductLog[a*x]]/
	(a*d*(m+1)*E^(m*ProductLog[a*x])*(-(m+1)*ProductLog[a*x])^m) /;
FreeQ[{a,d,m},x] && Not[IntegerQ[m]]


Int[1/(x_*(d_+d_.*ProductLog[a_.*x_^n_.])),x_Symbol] :=
  Log[ProductLog[a*x^n]]/(d*n) /;
FreeQ[{a,d,n},x]


Int[x_^m_./(d_+d_.*ProductLog[a_.*x_^n_]),x_Symbol] :=
  -Subst[Int[1/(x^(m+2)*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
FreeQ[{a,d},x] && IntegersQ[m,n] && n<0 && NeQ[m+1]


Int[(c_.*ProductLog[a_.*x_^n_.])^p_./(x_*(d_+d_.*ProductLog[a_.*x_^n_.])),x_Symbol] :=
  (c*ProductLog[a*x^n])^p/(d*n*p) /;
FreeQ[{a,c,d,n,p},x]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  c*x^(m+1)*(c*ProductLog[a*x^n])^(p-1)/(d*(m+1)) /;
FreeQ[{a,c,d,m,n,p},x] && NeQ[m+1] && EqQ[m+n*(p-1)+1]


Int[x_^m_.*ProductLog[a_.*x_^n_.]^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  a^p*ExpIntegralEi[-p*ProductLog[a*x^n]]/(d*n) /;
FreeQ[{a,d,m,n},x] && IntegerQ[p] && EqQ[m+n*p+1]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  a^(p-1/2)*c^(p-1/2)*Rt[Pi*c/(p-1/2),2]*Erf[Sqrt[c*ProductLog[a*x^n]]/Rt[c/(p-1/2),2]]/(d*n) /;
FreeQ[{a,c,d,m,n},x] && NeQ[m+1] && IntegerQ[p-1/2] && EqQ[m+n*(p-1/2)+1] && PosQ[c/(p-1/2)]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_/(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  a^(p-1/2)*c^(p-1/2)*Rt[-Pi*c/(p-1/2),2]*Erfi[Sqrt[c*ProductLog[a*x^n]]/Rt[-c/(p-1/2),2]]/(d*n) /;
FreeQ[{a,c,d,m,n},x] && NeQ[m+1] && IntegerQ[p-1/2] && EqQ[m+n*(p-1/2)+1] && NegQ[c/(p-1/2)]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  c*x^(m+1)*(c*ProductLog[a*x^n])^(p-1)/(d*(m+1)) -
  c*(m+n*(p-1)+1)/(m+1)*Int[x^m*(c*ProductLog[a*x^n])^(p-1)/(d+d*ProductLog[a*x^n]),x] /;
FreeQ[{a,c,d,m,n,p},x] && NeQ[m+1] && RationalQ[Simplify[p+(m+1)/n]] && Simplify[p+(m+1)/n]>1


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  x^(m+1)*(c*ProductLog[a*x^n])^p/(d*(m+n*p+1)) -
  (m+1)/(c*(m+n*p+1))*Int[x^m*(c*ProductLog[a*x^n])^(p+1)/(d+d*ProductLog[a*x^n]),x] /;
FreeQ[{a,c,d,m,n,p},x] && NeQ[m+1] && RationalQ[Simplify[p+(m+1)/n]] && Simplify[p+(m+1)/n]<0


Int[x_^m_.*(c_.*ProductLog[a_.*x_])^p_./(d_+d_.*ProductLog[a_.*x_]),x_Symbol] :=
  x^m*Gamma[m+p+1,-(m+1)*ProductLog[a*x]]*(c*ProductLog[a*x])^p/
	(a*d*(m+1)*E^(m*ProductLog[a*x])*(-(m+1)*ProductLog[a*x])^(m+p)) /;
FreeQ[{a,c,d,m,p},x] && NeQ[m+1]


Int[x_^m_.*(c_.*ProductLog[a_.*x_^n_.])^p_./(d_+d_.*ProductLog[a_.*x_^n_.]),x_Symbol] :=
  -Subst[Int[(c*ProductLog[a*x^(-n)])^p/(x^(m+2)*(d+d*ProductLog[a*x^(-n)])),x],x,1/x] /;
FreeQ[{a,c,d,p},x] && NeQ[m+1] && IntegersQ[m,n] && n<0


Int[u_,x_Symbol] :=
  Subst[Int[SimplifyIntegrand[(x+1)*E^x*SubstFor[ProductLog[x],u,x],x],x],x,ProductLog[x]] /;
FunctionOfQ[ProductLog[x],u,x]



