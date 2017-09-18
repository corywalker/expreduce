(* ::Package:: *)

(* ::Section:: *)
(*Secant Function Rules*)


(* ::Subsection::Closed:: *)
(*4.3.1.1 (a+b sec)^n*)


Int[csc[c_.+d_.*x_]^n_,x_Symbol] :=
  -1/d*Subst[Int[ExpandIntegrand[(1+x^2)^(n/2-1),x],x],x,Cot[c+d*x]] /;
FreeQ[{c,d},x] && PositiveIntegerQ[n/2]


Int[(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(b*Csc[c+d*x])^(n-1)/(d*(n-1)) + 
  b^2*(n-2)/(n-1)*Int[(b*Csc[c+d*x])^(n-2),x] /;
FreeQ[{b,c,d},x] && n>1 && IntegerQ[2*n]


Int[(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Cos[c+d*x]*(b*Csc[c+d*x])^(n+1)/(b*d*n) + 
  (n+1)/(b^2*n)*Int[(b*Csc[c+d*x])^(n+2),x] /;
FreeQ[{b,c,d},x] && n<-1 && IntegerQ[2*n]


Int[csc[c_.+d_.*x_],x_Symbol] :=
(* -ArcCoth[Cos[c+d*x]]/d /; *)
  -ArcTanh[Cos[c+d*x]]/d /;
FreeQ[{c,d},x]


(* Int[1/csc[c_.+d_.*x_],x_Symbol] :=
  -Cos[c+d*x]/d /;
FreeQ[{c,d},x] *)


Int[(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Csc[c+d*x])^n*Sin[c+d*x]^n*Int[1/Sin[c+d*x]^n,x] /;
FreeQ[{b,c,d},x] && EqQ[n^2-1/4]


Int[(b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Csc[c+d*x])^(n-1)*((Sin[c+d*x]/b)^(n-1)*Int[1/(Sin[c+d*x]/b)^n,x]) /;
FreeQ[{b,c,d,n},x] && Not[IntegerQ[n]]


Int[(a_+b_.*csc[c_.+d_.*x_])^2,x_Symbol] :=
  a^2*x + 2*a*b*Int[Csc[c+d*x],x] + b^2*Int[Csc[c+d*x]^2,x] /;
FreeQ[{a,b,c,d},x]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  -2*b/d*Subst[Int[1/(a+x^2),x],x,b*Cot[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-2)/(d*(n-1)) + 
  a/(n-1)*Int[(a+b*Csc[c+d*x])^(n-2)*(a*(n-1)+b*(3*n-4)*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[1/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  1/a*Int[Sqrt[a+b*Csc[c+d*x]],x] - 
  b/a*Int[Csc[c+d*x]/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  1/(a^2*(2*n+1))*Int[(a+b*Csc[c+d*x])^(n+1)*(a*(2*n+1)-b*(n+1)*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a^n*Cot[c+d*x]/(d*Sqrt[1+Csc[c+d*x]]*Sqrt[1-Csc[c+d*x]])*
    Subst[Int[(1+b*x/a)^(n-1/2)/(x*Sqrt[1-b*x/a]),x],x,Csc[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[2*n]] && PositiveQ[a]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a^IntPart[n]*(a+b*Csc[c+d*x])^FracPart[n]/(1+b/a*Csc[c+d*x])^FracPart[n]*Int[(1+b/a*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[2*n]] && Not[PositiveQ[a]]


Int[Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  2*(a+b*Csc[c+d*x])/(d*Rt[a+b,2]*Cot[c+d*x])*Sqrt[b*(1+Csc[c+d*x])/(a+b*Csc[c+d*x])]*Sqrt[-b*(1-Csc[c+d*x])/(a+b*Csc[c+d*x])]*
    EllipticPi[a/(a+b),ArcSin[Rt[a+b,2]/Sqrt[a+b*Csc[c+d*x]]],(a-b)/(a+b)] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^(3/2),x_Symbol] :=
  Int[(a^2+b*(2*a-b)*Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] + 
  b^2*Int[Csc[c+d*x]*(1+Csc[c+d*x])/Sqrt[a+b*Csc[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-2)/(d*(n-1)) + 
  1/(n-1)*Int[(a+b*Csc[c+d*x])^(n-3)*
    Simp[a^3*(n-1)+(b*(b^2*(n-2)+3*a^2*(n-1)))*Csc[c+d*x]+(a*b^2*(3*n-4))*Csc[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[1/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  x/a - 1/a*Int[1/(1+a/b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*csc[c_.+d_.*x_]],x_Symbol] :=
  2*Rt[a+b,2]/(a*d*Cot[c+d*x])*Sqrt[b*(1-Csc[c+d*x])/(a+b)]*Sqrt[-b*(1+Csc[c+d*x])/(a-b)]*
    EllipticPi[(a+b)/a,ArcSin[Sqrt[a+b*Csc[c+d*x]]/Rt[a+b,2]],(a+b)/(a-b)] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  1/(a*(n+1)*(a^2-b^2))*Int[(a+b*Csc[c+d*x])^(n+1)*Simp[(a^2-b^2)*(n+1)-a*b*(n+1)*Csc[c+d*x]+b^2*(n+2)*Csc[c+d*x]^2,x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[a^2-b^2] && Not[IntegerQ[2*n]]





(* ::Subsection::Closed:: *)
(*4.3.1.2 (d sec)^n (a+b sec)^m*)


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  a*Int[(d*Csc[e+f*x])^n,x] + b/d*Int[(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,n},x]


Int[(a_+b_.*csc[e_.+f_.*x_])^2*(d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  2*a*b/d*Int[(d*Csc[e+f*x])^(n+1),x] + Int[(d*Csc[e+f*x])^n*(a^2+b^2*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x]


Int[csc[e_.+f_.*x_]^2/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  1/b*Int[Csc[e+f*x],x] - a/b*Int[Csc[e+f*x]/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x]


Int[csc[e_.+f_.*x_]^3/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -Cot[e+f*x]/(b*f) - a/b*Int[Csc[e+f*x]^2/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(a+b*csc[e+f*x])^m*(d*csc[e+f*x])^n,x],x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && PositiveIntegerQ[m] && RationalQ[n]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*b*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]) /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)/(f*m) + a*(2*m-1)/m*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && RationalQ[m] && m>1/2 && IntegerQ[2*m]


Int[csc[e_.+f_.*x_]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -Cot[e+f*x]/(f*(b+a*Csc[e+f*x])) /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2]


Int[csc[e_.+f_.*x_]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2/f*Subst[Int[1/(2*a+x^2),x],x,b*Cot[e+f*x]/Sqrt[a+b*Csc[e+f*x]]] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  b*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) + (m+1)/(a*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2 && IntegerQ[2*m]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(2*m+1)) + 
  m/(b*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  a*m/(b*(m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[csc[e_.+f_.*x_]^3*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  b*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(a*m-b*(2*m+1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]^3*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*(b*(m+1)-a*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*a/(b*f)*Sqrt[a*d/b]*Subst[Int[1/Sqrt[1+x^2/a],x],x,b*Cot[e+f*x]/Sqrt[a+b*Csc[e+f*x]]] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && PositiveQ[a*d/b]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*b*d/f*Subst[Int[1/(b-d*x^2),x],x,b*Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]])] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && Not[PositiveQ[a*d/b]]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*d*Cot[e+f*x]*(d*Csc[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Csc[e+f*x]]) + 
  2*a*d*(n-1)/(b*(2*n-1))*Int[Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*a*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]]) /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n*Sqrt[a+b*Csc[e+f*x]]) + 
  a*(2*n+1)/(2*b*d*n)*Int[Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[n] && n<-1/2 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*d*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[a-b*Csc[e+f*x]])*Subst[Int[(d*x)^(n-1)/Sqrt[a-b*x],x],x,Csc[e+f*x]] /;
FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -Sqrt[2]*Sqrt[a]/(b*f)*Subst[Int[1/Sqrt[1+x^2],x],x,b*Cot[e+f*x]/(a+b*Csc[e+f*x])] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && EqQ[d-a/b] && PositiveQ[a]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*b*d/(a*f)*Subst[Int[1/(2*b-d*x^2),x],x,b*Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]])] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*m) + 
  b*(2*m-1)/(d*m)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && EqQ[m+n] && RationalQ[m] && m>1/2 && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(a*f*(2*m+1)) + 
  d*(m+1)/(b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && EqQ[m+n] && RationalQ[m] && m<-1/2 && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(2*m+1)) + 
  m/(a*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[m,n] && m+n+1==0 && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+1)) + 
  a*m/(b*d*(m+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && EqQ[m+n+1] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n/(f*n) - 
  a/(d*n)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^(n+1)*(b*(m-2*n-2)-a*(m+2*n-1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[m,n] && m>1 && (n<-1 || m==3/2 && n==-1/2) && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n/(f*(m+n-1)) + 
  b/(m+n-1)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n*(b*(m+2*n-1)+a*(3*m+2*n-4)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2] && RationalQ[m] && m>1 && NeQ[m+n-1] && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(a*f*(2*m+1)) - 
  d/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*(a*(n-1)-b*(m+n)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 1<n<2 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)/(f*(2*m+1)) + 
  d^2/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)*(b*(n-2)+a*(m-n+2)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>2 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*(a*(2*m+n+1)-b*(m+n+1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1 && (IntegersQ[2*m,2*n] || IntegerQ[m])


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d^2*Cot[e+f*x]*(d*Csc[e+f*x])^(n-2)/(f*(a+b*Csc[e+f*x])) - 
  d^2/(a*b)*Int[(d*Csc[e+f*x])^(n-2)*(b*(n-2)-a*(n-1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[n] && n>1


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(a+b*Csc[e+f*x])) - 
  1/a^2*Int[(d*Csc[e+f*x])^n*(a*(n-1)-b*n*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[n] && n<0


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*d*Cot[e+f*x]*(d*Csc[e+f*x])^(n-1)/(a*f*(a+b*Csc[e+f*x])) + 
  d*(n-1)/(a*b)*Int[(d*Csc[e+f*x])^(n-1)*(a-b*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  d/b*Int[Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]],x] - 
  a*d/b*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^n_/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*d^2*Cot[e+f*x]*(d*Csc[e+f*x])^(n-2)/(f*(2*n-3)*Sqrt[a+b*Csc[e+f*x]]) + 
  d^2/(b*(2*n-3))*Int[(d*Csc[e+f*x])^(n-2)*(2*b*(n-2)-a*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[(d_.*csc[e_.+f_.*x_])^n_/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n*Sqrt[a+b*Csc[e+f*x]]) + 
  1/(2*b*d*n)*Int[(d*Csc[e+f*x])^(n+1)*(a+b*(2*n+1)*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[n] && n<0 && IntegerQ[2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)/(f*(m+n-1)) + 
  d^2/(b*(m+n-1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)*(b*(n-2)+a*m*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,m},x] && EqQ[a^2-b^2] && RationalQ[n] && n>2 && NeQ[m+n-1] && IntegerQ[n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -(a*d/b)^n*Cot[e+f*x]/(a^(n-2)*f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[a-b*Csc[e+f*x]])*
    Subst[Int[(a-x)^(n-1)*(2*a-x)^(m-1/2)/Sqrt[x],x],x,a-b*Csc[e+f*x]] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && PositiveQ[a] && Not[IntegerQ[n]] && PositiveQ[a*d/b]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -(-a*d/b)^n*Cot[e+f*x]/(a^(n-1)*f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[a-b*Csc[e+f*x]])*
    Subst[Int[x^(m-1/2)*(a-x)^(n-1)/Sqrt[2*a-x],x],x,a+b*Csc[e+f*x]] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && PositiveQ[a] && Not[IntegerQ[n]] && NegativeQ[a*d/b]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^2*d*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[a-b*Csc[e+f*x]])*
    Subst[Int[(d*x)^(n-1)*(a+b*x)^(m-1/2)/Sqrt[a-b*x],x],x,Csc[e+f*x]] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && PositiveQ[a]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^IntPart[m]*(a+b*Csc[e+f*x])^FracPart[m]/(1+b/a*Csc[e+f*x])^FracPart[m]*Int[(1+b/a*Csc[e+f*x])^m*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && Not[PositiveQ[a]]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  (a-b)*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] + b*Int[Csc[e+f*x]*(1+Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)/(f*m) + 
  1/m*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(b^2*(m-1)+a^2*m+a*b*(2*m-1)*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2] && RationalQ[m] && m>1 && IntegerQ[2*m]


(* Int[csc[e_.+f_.*x_]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -2/f*Subst[Int[1/(a+b-(a-b)*x^2),x],x,Cot[e+f*x]/(1+Csc[e+f*x])] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2] *)


Int[csc[e_.+f_.*x_]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  1/b*Int[1/(1+a/b*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*Rt[a+b,2]/(b*f*Cot[e+f*x])*Sqrt[(b*(1-Csc[e+f*x]))/(a+b)]*Sqrt[-b*(1+Csc[e+f*x])/(a-b)]*
    EllipticF[ArcSin[Sqrt[a+b*Csc[e+f*x]]/Rt[a+b,2]],(a+b)/(a-b)] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(a*(m+1)-b*(m+2)*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
 Cot[e+f*x]/(f*Sqrt[1+Csc[e+f*x]]*Sqrt[1-Csc[e+f*x]])*Subst[Int[(a+b*x)^m/(Sqrt[1+x]*Sqrt[1-x]),x],x,Csc[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2] && Not[IntegerQ[2*m]]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  m/(m+1)*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(b+a*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  a*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) - 
  1/((m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(b*(m+1)-a*(m+2)*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^2/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] + 
  Int[Csc[e+f*x]*(1+Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -a/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] + 1/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]^3*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -a^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*Simp[a*b*(m+1)-(a^2+b^2*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^3*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*(b*(m+1)-a*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-3)*(d*Csc[e+f*x])^(n+1)*
    Simp[a^2*b*(m-2*n-2)-a*(3*b^2*n+a^2*(n+1))*Csc[e+f*x]-b*(b^2*n+a^2*(m+n-1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[m,n] && m>2 && (IntegerQ[m] && n<-1 || IntegersQ[m+1/2,2*n] && n<=-1)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n/(f*(m+n-1)) + 
  1/(d*(m+n-1))*Int[(a+b*Csc[e+f*x])^(m-3)*(d*Csc[e+f*x])^n*
    Simp[a^3*d*(m+n-1)+a*b^2*d*n+b*(b^2*d*(m+n-2)+3*a^2*d*(m+n-1))*Csc[e+f*x]+a*b^2*d*(3*m+2*n-4)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2] && RationalQ[m] && m>2 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[IntegerQ[n] && n>2 && Not[IntegerQ[m]]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[b*d*(n-1)+a*d*(m+1)*Csc[e+f*x]-b*d*(m+n+1)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 0<n<1 && IntegersQ[2*m,2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)/(f*(m+1)*(a^2-b^2)) - 
  d^2/((m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)*(a*(n-2)+b*(m+1)*Csc[e+f*x]-a*(m+n)*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 1<n<2 && IntegersQ[2*m,2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -a^2*d^3*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-3)/(b*f*(m+1)*(a^2-b^2)) + 
  d^3/(b*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-3)*
    Simp[a^2*(n-3)+a*b*(m+1)*Csc[e+f*x]-(a^2*(n-2)+b^2*(m+1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[m,n] && m<-1 && (IntegerQ[n] && n>3 || IntegersQ[n+1/2,2*m] && n>2)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*n) - 
  1/(a*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*
    Simp[b*(m+n+1)-a*(n+1)*Csc[e+f*x]-b*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && NegativeIntegerQ[m+1/2,n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    (a^2*(m+1)-b^2*(m+n+1)-a*b*(m+1)*Csc[e+f*x]+b^2*(m+n+2)*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegersQ[2*m,2*n]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  Sqrt[d*Sin[e+f*x]]*Sqrt[d*Csc[e+f*x]]/d*Int[Sqrt[d*Sin[e+f*x]]/(b+a*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^(3/2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d*Sqrt[d*Sin[e+f*x]]*Sqrt[d*Csc[e+f*x]]*Int[1/(Sqrt[d*Sin[e+f*x]]*(b+a*Sin[e+f*x])),x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^(5/2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[(d*Csc[e+f*x])^(3/2),x] - a*d/b*Int[(d*Csc[e+f*x])^(3/2)/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -d^3*Cot[e+f*x]*(d*Csc[e+f*x])^(n-3)/(b*f*(n-2)) + 
  d^3/(b*(n-2))*Int[(d*Csc[e+f*x])^(n-3)*Simp[a*(n-3)+b*(n-3)*Csc[e+f*x]-a*(n-2)*Csc[e+f*x]^2,x]/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[n] && n>3


Int[1/(Sqrt[d_.*csc[e_.+f_.*x_]]*(a_+b_.*csc[e_.+f_.*x_])),x_Symbol] :=
  b^2/(a^2*d^2)*Int[(d*Csc[e+f*x])^(3/2)/(a+b*Csc[e+f*x]),x] + 
  1/a^2*Int[(a-b*Csc[e+f*x])/Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^n_/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  Cot[e+f*x]*(d*Csc[e+f*x])^n/(a*f*n) - 
  1/(a*d*n)*Int[(d*Csc[e+f*x])^(n+1)/(a+b*Csc[e+f*x])*
    Simp[b*n-a*(n+1)*Csc[e+f*x]-b*(n+1)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  a*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] + 
  b/d*Int[(d*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*d*Cos[e+f*x]*Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^(n-1)/(f*(2*n-1)) + 
  d^2/(2*n-1)*Int[(d*Csc[e+f*x])^(n-2)*Simp[2*a*(n-2)+b*(2*n-3)*Csc[e+f*x]+a*Csc[e+f*x]^2,x]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[a+b*Csc[e+f*x]]/(Sqrt[d*Csc[e+f*x]]*Sqrt[b+a*Sin[e+f*x]])*Int[Sqrt[b+a*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Cot[e+f*x]*Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^n/(f*n) - 
  1/(2*d*n)*Int[(d*Csc[e+f*x])^(n+1)*Simp[b-2*a*(n+1)*Csc[e+f*x]-b*(2*n+3)*Csc[e+f*x]^2,x]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegerQ[2*n]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[d*Csc[e+f*x]]*Sqrt[b+a*Sin[e+f*x]]/Sqrt[a+b*Csc[e+f*x]]*Int[1/Sqrt[b+a*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  d*Sqrt[d*Csc[e+f*x]]*Sqrt[b+a*Sin[e+f*x]]/Sqrt[a+b*Csc[e+f*x]]*Int[1/(Sin[e+f*x]*Sqrt[b+a*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^n_/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*d^2*Cos[e+f*x]*(d*Csc[e+f*x])^(n-2)*Sqrt[a+b*Csc[e+f*x]]/(b*f*(2*n-3)) + 
  d^3/(b*(2*n-3))*Int[(d*Csc[e+f*x])^(n-3)/Sqrt[a+b*Csc[e+f*x]]*
     Simp[2*a*(n-3)+b*(2*n-5)*Csc[e+f*x]-2*a*(n-2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[n] && n>2 && IntegerQ[2*n]


Int[1/(csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  -Cos[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/(a*f) - b/(2*a)*Int[(1+Csc[e+f*x]^2)/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2]


Int[1/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[d_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  1/a*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[d*Csc[e+f*x]],x] - 
  b/(a*d)*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^n_/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Cos[e+f*x]*(d*Csc[e+f*x])^(n+1)*Sqrt[a+b*Csc[e+f*x]]/(a*d*f*n) + 
  1/(2*a*d*n)*Int[(d*Csc[e+f*x])^(n+1)/Sqrt[a+b*Csc[e+f*x]]*
    Simp[-b*(2*n+1)+2*a*(n+1)*Csc[e+f*x]+b*(2*n+3)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*Cot[e+f*x]*Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^n/(f*n) + 
  1/(2*d*n)*Int[(d*Csc[e+f*x])^(n+1)/Sqrt[a+b*Csc[e+f*x]]*
    Simp[a*b*(2*n-1)+2*(b^2*n+a^2*(n+1))*Csc[e+f*x]+a*b*(2*n+3)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[n] && n<=-1 && IntegersQ[2*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d^3*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-3)/(b*f*(m+n-1)) + 
  d^3/(b*(m+n-1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-3)*
    Simp[a*(n-3)+b*(m+n-2)*Csc[e+f*x]-a*(n-2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NeQ[a^2-b^2] && RationalQ[n] && n>3 && 
  (IntegerQ[n] || IntegersQ[2*m,2*n]) && Not[IntegerQ[m] && m>2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n-1)/(f*(m+n-1)) + 
  d/(m+n-1)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^(n-1)*
    Simp[a*b*(n-1)+(b^2*(m+n-2)+a^2*(m+n-1))*Csc[e+f*x]+a*b*(2*m+n-2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[m,n] && 0<m<2 && 0<n<3 && NeQ[m+n-1] && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)/(f*(m+n-1)) + 
  d^2/(b*(m+n-1))*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n-2)*
    Simp[a*b*(n-2)+b^2*(m+n-2)*Csc[e+f*x]+a*b*m*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && RationalQ[m,n] && -1<m<2 && 1<n<3 && NeQ[m+n-1] && 
  (IntegerQ[n] || IntegersQ[2*m,2*n])


Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)/Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  a*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[d*Csc[e+f*x]],x] + 
  b/d*Int[Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b/d*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1),x] + 
  a*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,n},x] && PositiveIntegerQ[m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,m,n},x]


Int[(d_.*cos[e_.+f_.*x_])^m_*(a_.+b_.*sec[e_.+f_.*x_])^p_,x_Symbol] :=
  (d*Cos[e+f*x])^FracPart[m]*(Sec[e+f*x]/d)^FracPart[m]*Int[(Sec[e+f*x]/d)^(-m)*(a+b*Sec[e+f*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*4.3.1.3 (d sin)^n (a+b sec)^m*)


Int[(g_.*cos[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_.,x_Symbol] :=
  Int[(g*Cos[e+f*x])^p*(b+a*Sin[e+f*x])^m/Sin[e+f*x]^m,x] /;
FreeQ[{a,b,e,f,g,p},x] && IntegerQ[m]


Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -1/(f*b^(p-1))*Subst[Int[(-a+b*x)^((p-1)/2)*(a+b*x)^(m+(p-1)/2)/x^(p+1),x],x,Csc[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && EqQ[a^2-b^2]


Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  -1/f*Subst[Int[(-1+x)^((p-1)/2)*(1+x)^((p-1)/2)*(a+b*x)^m/x^(p+1),x],x,Csc[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_/cos[e_.+f_.*x_]^2,x_Symbol] :=
  Tan[e+f*x]*(a+b*Csc[e+f*x])^m/f + b*m*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,m},x]


Int[(g_.*cos[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  Sin[e+f*x]^FracPart[m]*(a+b*Csc[e+f*x])^FracPart[m]/(b+a*Sin[e+f*x])^FracPart[m]*
    Int[(g*Cos[e+f*x])^p*(b+a*Sin[e+f*x])^m/Sin[e+f*x]^m,x] /;
FreeQ[{a,b,e,f,g,m,p},x] && (EqQ[a^2-b^2] || IntegersQ[2*m,p])


Int[(g_.*cos[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_.,x_Symbol] :=
  Defer[Int][(g*Cos[e+f*x])^p*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,g,m,p},x]


(* Int[(g_.*sec[e_.+f_.*x_])^p_*(a_+b_.*csc[e_.+f_.*x_])^m_.,x_Symbol] :=
  Int[(g*Sec[e+f*x])^p*(b+a*Sin[e+f*x])^m/Sin[e+f*x]^m,x] /;
FreeQ[{a,b,e,f,g,p},x] && Not[IntegerQ[p]] && IntegerQ[m] *)


Int[(g_.*sec[e_.+f_.*x_])^p_*(a_+b_.*csc[e_.+f_.*x_])^m_.,x_Symbol] :=
  g^IntPart[p]*(g*Sec[e+f*x])^FracPart[p]*Cos[e+f*x]^FracPart[p]*Int[(a+b*Csc[e+f*x])^m/Cos[e+f*x]^p,x] /;
FreeQ[{a,b,e,f,g,m,p},x] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*4.3.1.4 (d tan)^n (a+b sec)^m*)


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  1/(a^(m-n-1)*b^n*d)*Subst[Int[(a-b*x)^((m-1)/2)*(a+b*x)^((m-1)/2+n)/x^(m+n),x],x,Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[(m-1)/2] && EqQ[a^2-b^2] && IntegerQ[n]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -1/(d*b^(m-1))*Subst[Int[(-a+b*x)^((m-1)/2)*(a+b*x)^((m-1)/2+n)/x,x],x,Csc[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[(m-1)/2] && EqQ[a^2-b^2] && Not[IntegerQ[n]]


Int[(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -e*(e*Cot[c+d*x])^(m-1)*(a*m+b*(m-1)*Csc[c+d*x])/(d*m*(m-1)) - 
  e^2/m*Int[(e*Cot[c+d*x])^(m-2)*(a*m+b*(m-1)*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1


Int[(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -(e*Cot[c+d*x])^(m+1)*(a+b*Csc[c+d*x])/(d*e*(m+1)) - 
  1/(e^2*(m+1))*Int[(e*Cot[c+d*x])^(m+2)*(a*(m+1)+b*(m+2)*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1


Int[(a_+b_.*csc[c_.+d_.*x_])/cot[c_.+d_.*x_],x_Symbol] :=
  Int[(b+a*Sin[c+d*x])/Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x]


Int[(e_.*cot[c_.+d_.*x_])^m_.*(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  a*Int[(e*Cot[c+d*x])^m,x] + b*Int[(e*Cot[c+d*x])^m*Csc[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m},x]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -(-1)^((m-1)/2)/(d*b^(m-1))*Subst[Int[(b^2-x^2)^((m-1)/2)*(a+x)^n/x,x],x,b*Csc[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[(m-1)/2] && NeQ[a^2-b^2]


Int[(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(e*Cot[c+d*x])^m,(a+b*Csc[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && PositiveIntegerQ[n]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  -2*a^(m/2+n+1/2)/d*Subst[Int[x^m*(2+a*x^2)^(m/2+n-1/2)/(1+a*x^2),x],x,Cot[c+d*x]/Sqrt[a+b*Csc[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2] && IntegerQ[m/2] && IntegerQ[n-1/2]


Int[(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  a^(2*n)*e^(-2*n)*Int[(e*Cot[c+d*x])^(m+2*n)/(-a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[a^2-b^2] && NegativeIntegerQ[n]


Int[(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  -2^(m+n+1)*(e*Cot[c+d*x])^(m+1)*(a+b*Csc[c+d*x])^n/(d*e*(m+1))*(a/(a+b*Csc[c+d*x]))^(m+n+1)*
    AppellF1[(m+1)/2,m+n,1,(m+3)/2,-(a-b*Csc[c+d*x])/(a+b*Csc[c+d*x]),(a-b*Csc[c+d*x])/(a+b*Csc[c+d*x])] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[n]]


Int[Sqrt[e_.*cot[c_.+d_.*x_]]/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  1/a*Int[Sqrt[e*Cot[c+d*x]],x] - b/a*Int[Sqrt[e*Cot[c+d*x]]/(b+a*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2]


Int[(e_.*cot[c_.+d_.*x_])^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  -e^2/b^2*Int[(e*Cot[c+d*x])^(m-2)*(a-b*Csc[c+d*x]),x] + 
  e^2*(a^2-b^2)/b^2*Int[(e*Cot[c+d*x])^(m-2)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m-1/2]


Int[1/(Sqrt[e_.*cot[c_.+d_.*x_]]*(a_+b_.*csc[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[1/Sqrt[e*Cot[c+d*x]],x] - b/a*Int[1/(Sqrt[e*Cot[c+d*x]]*(b+a*Sin[c+d*x])),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2]


Int[(e_.*cot[c_.+d_.*x_])^m_/(a_+b_.*csc[c_.+d_.*x_]),x_Symbol] :=
  1/(a^2-b^2)*Int[(e*Cot[c+d*x])^m*(a-b*Csc[c+d*x]),x] + 
  b^2/(e^2*(a^2-b^2))*Int[(e*Cot[c+d*x])^(m+2)/(a+b*Csc[c+d*x]),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2] && NegativeIntegerQ[m+1/2]


Int[cot[c_.+d_.*x_]^2*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[(-1+Csc[c+d*x]^2)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2]


Int[(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(e*Cot[c+d*x])^m,(a+b*Csc[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[a^2-b^2] && PositiveIntegerQ[n]


Int[cot[c_.+d_.*x_]^m_.*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[Cos[c+d*x]^m*(b+a*Sin[c+d*x])^n/Sin[c+d*x]^(m+n),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && IntegerQ[n] && IntegerQ[m] && (IntegerQ[m/2] || m<=1)


(* Int[cot[c_.+d_.*x_]^m_*(a_+b_.*csc[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*Csc[c+d*x])^n,(-1+Csc[c+d*x]^2)^(m/2),x],x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m/2] *)


Int[(e_.*cot[c_.+d_.*x_])^m_.*(a_.+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(e*Cot[c+d*x])^m*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(e_.*cot[c_.+d_.*x_])^m_*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x])^m*Tan[c+d*x]^m*Int[(a+b*Sec[c+d*x])^n/Tan[c+d*x]^m,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && Not[IntegerQ[m]]


Int[(e_.*tan[c_.+d_.*x_]^p_)^m_*(a_+b_.*sec[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Tan[c+d*x]^p)^m/(e*Tan[c+d*x])^(m*p)*Int[(e*Tan[c+d*x])^(m*p)*(a+b*Sec[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && Not[IntegerQ[m]]


Int[(e_.*cot[c_.+d_.*x_]^p_)^m_*(a_+b_.*csc[c_.+d_.*x_])^n_.,x_Symbol] :=
  (e*Cot[c+d*x]^p)^m/(e*Cot[c+d*x])^(m*p)*Int[(e*Cot[c+d*x])^(m*p)*(a+b*Csc[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && Not[IntegerQ[m]]





(* ::Subsection::Closed:: *)
(*4.3.2.1 (a+b sec)^m (c+d sec)^n*)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  c^n*Int[ExpandTrig[(1+d/c*csc[e+f*x])^n,(a+b*csc[e+f*x])^m,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[m] && NegativeIntegerQ[n] && m+n<2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  (-a*c)^m*Int[Cot[e+f*x]^(2*m)*(c+d*Csc[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m] && RationalQ[n] && Not[IntegerQ[n] && m-n>0]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  (-a*c)^(m+1/2)*Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*Int[Cot[e+f*x]^(2*m),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m+1/2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  2*a*c*Cot[e+f*x]*(c+d*Csc[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Csc[e+f*x]]) + 
  c*Int[Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && RationalQ[n] && n>1/2


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*a*Cot[e+f*x]*(c+d*Csc[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Csc[e+f*x]]) + 
  1/c*Int[Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  -4*a^2*Cot[e+f*x]*(c+d*Csc[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Csc[e+f*x]]) + 
  a/c*Int[Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  -2*a^2*Cot[e+f*x]*(c+d*Csc[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Csc[e+f*x]]) + 
  a*Int[Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && Not[RationalQ[n] && n<=-1/2]


Int[(a_+b_.*csc[e_.+f_.*x_])^(5/2)*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  -8*a^3*Cot[e+f*x]*(c+d*Csc[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Csc[e+f*x]]) + 
  a^2/c^2*Int[Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])^(n+2),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && RationalQ[n] && n<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*c*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*
    Subst[Int[(b+a*x)^(m-1/2)*(d+c*x)^(n-1/2)/x^(m+n),x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m-1/2] && EqQ[m+n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  a*c*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^(n-1/2)/x,x],x,Csc[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*c*x + b*d*Int[Csc[e+f*x]^2,x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d]


Int[(a_+b_.*csc[e_.+f_.*x_])*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*c*x + (b*c+a*d)*Int[Csc[e+f*x],x] + b*d*Int[Csc[e+f*x]^2,x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[b*c+a*d]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  c*Int[Sqrt[a+b*Csc[e+f*x]],x] + d*Int[Sqrt[a+b*Csc[e+f*x]]*Csc[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*c*Int[1/Sqrt[a+b*Csc[e+f*x]],x] + 
 Int[Csc[e+f*x]*(b*c+a*d+b*d*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)/(f*m) + 
  1/m*Int[(a+b*Csc[e+f*x])^(m-1)*Simp[a*c*m+(b*c*m+a*d*(2*m-1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && RationalQ[m] && m>1 && EqQ[a^2-b^2] && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)/(f*m) + 
  1/m*Int[(a+b*Csc[e+f*x])^(m-2)*
    Simp[a^2*c*m+(b^2*d*(m-1)+2*a*b*c*m+a^2*d*m)*Csc[e+f*x]+b*(b*c*m+a*d*(2*m-1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && RationalQ[m] && m>1 && NeQ[a^2-b^2] && IntegerQ[2*m]


Int[(c_+d_.*csc[e_.+f_.*x_])/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  c*x/a - (b*c-a*d)/a*Int[Csc[e+f*x]/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d]


Int[(c_+d_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  c/a*Int[Sqrt[a+b*Csc[e+f*x]],x] - (b*c-a*d)/a*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[(c_+d_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  c*Int[1/Sqrt[a+b*Csc[e+f*x]],x] + d*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(b*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*Simp[a*c*(2*m+1)-(b*c-a*d)*(m+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && RationalQ[m] && m<-1 && EqQ[a^2-b^2] && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  b*(b*c-a*d)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*
    Simp[c*(a^2-b^2)*(m+1)-(a*(b*c-a*d)*(m+1))*Csc[e+f*x]+b*(b*c-a*d)*(m+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && RationalQ[m] && m<-1 && NeQ[a^2-b^2] && IntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  c*Int[(a+b*Csc[e+f*x])^m,x] + d*Int[(a+b*Csc[e+f*x])^m*Csc[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d] && Not[IntegerQ[2*m]]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  1/c*Int[Sqrt[a+b*Csc[e+f*x]],x] - d/c*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && (EqQ[a^2-b^2] || EqQ[c^2-d^2])


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a/c*Int[1/Sqrt[a+b*Csc[e+f*x]],x] + (b*c-a*d)/c*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a/c*Int[Sqrt[a+b*Csc[e+f*x]],x] + (b*c-a*d)/c*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && (EqQ[a^2-b^2] || EqQ[c^2-d^2])


(* Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  b/d*Int[Sqrt[a+b*Csc[e+f*x]],x] - (b*c-a*d)/d*Int[Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] *)


Int[(a_+b_.*csc[e_.+f_.*x_])^(3/2)/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  1/(c*d)*Int[(a^2*d+b^2*c*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] - 
  (b*c-a*d)^2/(c*d)*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[1/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  1/(c*(b*c-a*d))*Int[(b*c-a*d-b*d*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] + 
  d^2/(c*(b*c-a*d))*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && (EqQ[a^2-b^2] || EqQ[c^2-d^2])


Int[1/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  1/c*Int[1/Sqrt[a+b*Csc[e+f*x]],x] - d/c*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]]/Cot[e+f*x]*Int[Cot[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && EqQ[c^2-d^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  c*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]],x] + 
  d*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  1/c*Int[Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]],x] - 
  d/c*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && EqQ[c^2-d^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*a/f*Subst[Int[1/(1+a*c*x^2),x],x,Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  a/c*Int[Sqrt[c+d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] + 
  (b*c-a*d)/c*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && EqQ[c^2-d^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  2*(a+b*Csc[e+f*x])/(c*f*Rt[(a+b)/(c+d),2]*Cot[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Csc[e+f*x])/((c-d)*(a+b*Csc[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Csc[e+f*x])/((c+d)*(a+b*Csc[e+f*x]))]*
    EllipticPi[a*(c+d)/(c*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[1/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[c_+d_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*Int[1/Cot[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && EqQ[c^2-d^2]


Int[1/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[c_+d_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  1/a*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]],x] - 
  b/a*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_])^(3/2),x_Symbol] :=
  1/c*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]],x] - 
  d/c*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x])^(3/2),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[c^2-d^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^2*(Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[a-b*Csc[e+f*x]]))*
    Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^n/(x*Sqrt[a-b*x]),x],x,Csc[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && IntegerQ[m-1/2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^(m+n),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d] && IntegerQ[m] && IntegerQ[n] && MemberQ[{0,-1,-2},m+n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Sqrt[d+c*Sin[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]/(Sqrt[b+a*Sin[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*
    Int[(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^(m+n),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d] && IntegerQ[m+1/2] && IntegerQ[n+1/2] && MemberQ[{0,-1,-2},m+n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Sin[e+f*x]^(m+n)*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/((b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n)*
    Int[(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^Simplify[m+n],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d] && EqQ[m+n] && Not[IntegerQ[2*m]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(a+b*csc[e+f*x])^m,(c+d*csc[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && PositiveIntegerQ[n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(d_./sec[e_.+f_.*x_])^n_,x_Symbol] :=
  d^m*Int[(b+a*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n-m),x] /;
FreeQ[{a,b,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[(a_.+b_.*csc[e_.+f_.*x_])^m_.*(d_./csc[e_.+f_.*x_])^n_,x_Symbol] :=
  d^m*Int[(b+a*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[(a_.+b_.*sec[e_.+f_.*x_])^m_.*(c_.*(d_.*sec[e_.+f_.*x_])^p_)^n_,x_Symbol] :=
  c^IntPart[n]*(c*(d*Sec[e + f*x])^p)^FracPart[n]/(d*Sec[e + f*x])^(p*FracPart[n])*
    Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n*p),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[n]]


Int[(a_.+b_.*csc[e_.+f_.*x_])^m_.*(c_.*(d_.*csc[e_.+f_.*x_])^p_)^n_,x_Symbol] :=
  c^IntPart[n]*(c*(d*Csc[e + f*x])^p)^FracPart[n]/(d*Csc[e + f*x])^(p*FracPart[n])*
    Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n*p),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[n]]





(* ::Subsection::Closed:: *)
(*4.3.2.2 (g sec)^p (a+b sec)^m (c+d sec)^n*)


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  b*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/(a*f*(2*m+1)) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && EqQ[m+n+1] && NeQ[2*m+1]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  b*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/(a*f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(c+d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && NegativeIntegerQ[m+n+1] && NeQ[2*m+1] && 
  Not[RationalQ[n] && n<0] && Not[PositiveIntegerQ[n+1/2] && n+1/2<-(m+n)]


Int[csc[e_.+f_.*x_]*Sqrt[c_+d_.*csc[e_.+f_.*x_]]/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  a*c*Log[1+b/a*Csc[e+f*x]]*Cot[e+f*x]/(b*f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_.*Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  2*a*c*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(b*f*(2*m+1)*Sqrt[c+d*Csc[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && NeQ[m+1/2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  2*a*c*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^(n-1)/(b*f*(2*m+1)) - 
  d*(2*n-1)/(b*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(c+d*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[n-1/2] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^(n-1)/(f*(m+n)) + 
  c*(2*n-1)/(m+n)*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[n-1/2] && Not[RationalQ[m] && m<-1/2] && 
  Not[PositiveIntegerQ[m-1/2] && m<n]


Int[csc[e_.+f_.*x_]*(c_+d_.*csc[e_.+f_.*x_])^n_./Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*d*Cot[e+f*x]*(c+d*Csc[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Csc[e+f*x]]) + 
  2*c*(2*n-1)/(2*n-1)*Int[Csc[e+f*x]*(c+d*Csc[e+f*x])^(n-1)/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[n]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  2*a*c*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^(n-1)/(b*f*(2*m+1)) - 
  d*(2*n-1)/(b*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(c+d*Csc[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[n] && m<-1/2 && IntegerQ[2*m]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  (-a*c)^m*Int[ExpandTrig[csc[e+f*x]*cot[e+f*x]^(2*m),(c+d*csc[e+f*x])^(n-m),x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegersQ[m,n] && n-m>=0 && m*n>0


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  (-a*c)^(m+1/2)*Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*Int[Csc[e+f*x]*Cot[e+f*x]^(2*m),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m+1/2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/(a*f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(c+d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && (NegativeIntegerQ[m,n-1/2] || NegativeIntegerQ[m-1/2,n-1/2] && m<n)


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*c*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^(n-1/2),x],x,Csc[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  (-a*c)^m*Int[ExpandTrig[(g*csc[e+f*x])^p*cot[e+f*x]^(2*m),(c+d*csc[e+f*x])^(n-m),x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegersQ[m,n] && n-m>=0 && m*n>0


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^m_,x_Symbol] :=
  (-a*c)^(m+1/2)*Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*Int[(g*Csc[e+f*x])^p*Cot[e+f*x]^(2*m),x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m+1/2]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a*c*g*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*
    Subst[Int[(g*x)^(p-1)*(a+b*x)^(m-1/2)*(c+d*x)^(n-1/2),x],x,Csc[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[Sqrt[g_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -2*b*g/f*Subst[Int[1/(b*c+a*d-c*g*x^2),x],x,b*Cot[e+f*x]/(Sqrt[g*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[Sqrt[g_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a/c*Int[Sqrt[g*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] + 
  (b*c-a*d)/(c*g)*Int[(g*Csc[e+f*x])^(3/2)/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -2*b/f*Subst[Int[1/(b*c+a*d+d*x^2),x],x,b*Cot[e+f*x]/Sqrt[a+b*Csc[e+f*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -Sqrt[a+b*Csc[e+f*x]]*Sqrt[c/(c+d*Csc[e+f*x])]/(d*f*Sqrt[c*d*(a+b*Csc[e+f*x])/((b*c+a*d)*(c+d*Csc[e+f*x]))])*
    EllipticE[ArcSin[c*Cot[e+f*x]/(c+d*Csc[e+f*x])],-(b*c-a*d)/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && EqQ[c^2-d^2]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  b/d*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] - 
  (b*c-a*d)/d*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(g_.*csc[e_.+f_.*x_])^(3/2)*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  g/d*Int[Sqrt[g*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]],x] - 
  c*g/d*Int[Sqrt[g*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[(g_.*csc[e_.+f_.*x_])^(3/2)*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_]),x_Symbol] :=
  b/d*Int[(g*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] - 
  (b*c-a*d)/d*Int[(g*Csc[e+f*x])^(3/2)/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] - 
  d/(b*c-a*d)*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && (EqQ[a^2-b^2] || EqQ[c^2-d^2])


Int[csc[e_.+f_.*x_]/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  -2*Cot[e+f*x]/(f*(c+d)*Sqrt[a+b*Csc[e+f*x]]*Sqrt[-Cot[e+f*x]^2])*Sqrt[(a+b*Csc[e+f*x])/(a+b)]*
    EllipticPi[2*d/(c+d),ArcSin[Sqrt[1-Csc[e+f*x]]/Sqrt[2]],2*b/(a+b)] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(g_.*csc[e_.+f_.*x_])^(3/2)/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  -a*g/(b*c-a*d)*Int[Sqrt[g*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] + 
  c*g/(b*c-a*d)*Int[Sqrt[g*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[(g_.*csc[e_.+f_.*x_])^(3/2)/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  g*Sqrt[g*Csc[e+f*x]]*Sqrt[b+a*Sin[e+f*x]]/Sqrt[a+b*Csc[e+f*x]]*Int[1/(Sqrt[b+a*Sin[e+f*x]]*(d+c*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]^2/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  -a/(b*c-a*d)*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] + 
  c/(b*c-a*d)*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && (EqQ[a^2-b^2] || EqQ[c^2-d^2])


Int[csc[e_.+f_.*x_]^2/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  1/d*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] - 
  c/d*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(g_.*csc[e_.+f_.*x_])^(5/2)/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  -c^2*g^2/(d*(b*c-a*d))*Int[Sqrt[g*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]/(c+d*Csc[e+f*x]),x] + 
  g^2/(d*(b*c-a*d))*Int[Sqrt[g*Csc[e+f*x]]*(a*c+(b*c-a*d)*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[(g_.*csc[e_.+f_.*x_])^(5/2)/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])),x_Symbol] :=
  g/d*Int[(g*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] - 
  c*g/d*Int[(g*Csc[e+f*x])^(3/2)/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*b/f*Subst[Int[1/(1-b*d*x^2),x],x,Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -(b*c-a*d)/d*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]]),x] + 
  b/d*Int[Csc[e+f*x]*Sqrt[c+d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && EqQ[c^2-d^2]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/Sqrt[c_+d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*(a+b*Csc[e+f*x])/(d*f*Sqrt[(a+b)/(c+d)]*Cot[e+f*x])*
    Sqrt[-(b*c-a*d)*(1-Csc[e+f*x])/((c+d)*(a+b*Csc[e+f*x]))]*Sqrt[(b*c-a*d)*(1+Csc[e+f*x])/((c-d)*(a+b*Csc[e+f*x]))]*
    EllipticPi[b*(c+d)/(d*(a+b)),ArcSin[Sqrt[(a+b)/(c+d)]*Sqrt[c+d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[csc[e_.+f_.*x_]/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[c_+d_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  -2*a/(b*f)*Subst[Int[1/(2+(a*c-b*d)*x^2),x],x,Cot[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[csc[e_.+f_.*x_]/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[c_+d_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  -2*(c+d*Csc[e+f*x])/(f*(b*c-a*d)*Rt[(c+d)/(a+b),2]*Cot[e+f*x])*
    Sqrt[(b*c-a*d)*(1-Csc[e+f*x])/((a+b)*(c+d*Csc[e+f*x]))]*Sqrt[-(b*c-a*d)*(1+Csc[e+f*x])/((a-b)*(c+d*Csc[e+f*x]))]*
    EllipticF[ArcSin[Rt[(c+d)/(a+b),2]*(Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]])],(a+b)*(c-d)/((a-b)*(c+d))] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[csc[e_.+f_.*x_]^2/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*Sqrt[c_+d_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  -a/b*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]]),x] + 
  1/b*Int[Csc[e+f*x]*Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d]


Int[csc[e_.+f_.*x_]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]/(c_+d_.*csc[e_.+f_.*x_])^(3/2),x_Symbol] :=
  (a-b)/(c-d)*Int[Csc[e+f*x]/(Sqrt[a+b*Csc[e+f*x]]*Sqrt[c+d*Csc[e+f*x]]),x] + 
  (b*c-a*d)/(c-d)*Int[Csc[e+f*x]*(1+Csc[e+f*x])/(Sqrt[a+b*Csc[e+f*x]]*(c+d*Csc[e+f*x])^(3/2)),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*g*Cot[e+f*x]/(f*Sqrt[a+b*Csc[e+f*x]]*Sqrt[a-b*Csc[e+f*x]])*
    Subst[Int[(g*x)^(p-1)*(a+b*x)^(m-1/2)*(c+d*x)^n/Sqrt[a-b*x],x],x,Csc[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && (EqQ[p-1] || IntegerQ[m-1/2])


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  1/g^(m+n)*Int[(g*Csc[e+f*x])^(m+n+p)*(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b*c-a*d] && IntegerQ[m] && IntegerQ[n]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  (g*Csc[e+f*x])^(m+p)*(c+d*Csc[e+f*x])^n/(g^m*(d+c*Sin[e+f*x])^n)*Int[(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[b*c-a*d] && EqQ[m+n+p] && IntegerQ[m]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  (g*Csc[e+f*x])^p*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/((b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n)*
    Int[(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d] && EqQ[m+n+p] && Not[IntegerQ[m]]


Int[csc[e_.+f_.*x_]^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Sqrt[d+c*Sin[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]/(Sqrt[b+a*Sin[e+f*x]]*Sqrt[c+d*Csc[e+f*x]])*
    Int[(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^(m+n+p),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && IntegerQ[p] && MemberQ[{-1,-2},m+n+p]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*csc[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(g*csc[e+f*x])^p*(a+b*csc[e+f*x])^m*(c+d*csc[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d] && (IntegersQ[m,n] || IntegersQ[m,p] || IntegersQ[n,p])


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_.+b_.*csc[e_.+f_.*x_])^m_*(c_.+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Defer[Int][(g*Csc[e+f*x])^p*(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[sec[e_.+f_.*x_]*(A_+B_.*sec[e_.+f_.*x_])/(Sqrt[a_+b_.*sec[e_.+f_.*x_]]*(c_+d_.*sec[e_.+f_.*x_])^(3/2)),x_Symbol] :=
  2*A*(1+Sec[e+f*x])*Sqrt[(b*c-a*d)*(1-Sec[e+f*x])/((a+b)*(c+d*Sec[e+f*x]))]/
    (f*(b*c-a*d)*Rt[(c+d)/(a+b),2]*Tan[e+f*x]*Sqrt[-(b*c-a*d)*(1+Sec[e+f*x])/((a-b)*(c+d*Sec[e+f*x]))])*
    EllipticE[ArcSin[Rt[(c+d)/(a+b),2]*Sqrt[a+b*Sec[e+f*x]]/Sqrt[c+d*Sec[e+f*x]]],(a+b)*(c-d)/((a-b)*(c+d))] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && EqQ[A-B]


Int[csc[e_.+f_.*x_]*(A_+B_.*csc[e_.+f_.*x_])/(Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(c_+d_.*csc[e_.+f_.*x_])^(3/2)),x_Symbol] :=
  -2*A*(1+Csc[e+f*x])*Sqrt[(b*c-a*d)*(1-Csc[e+f*x])/((a+b)*(c+d*Csc[e+f*x]))]/
    (f*(b*c-a*d)*Rt[(c+d)/(a+b),2]*Cot[e+f*x]*Sqrt[-(b*c-a*d)*(1+Csc[e+f*x])/((a-b)*(c+d*Csc[e+f*x]))])*
    EllipticE[ArcSin[Rt[(c+d)/(a+b),2]*Sqrt[a+b*Csc[e+f*x]]/Sqrt[c+d*Csc[e+f*x]]],(a+b)*(c-d)/((a-b)*(c+d))] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && EqQ[A-B]





(* ::Subsection::Closed:: *)
(*4.3.3.1 (a+b sec)^m (d sec)^n (A+B sec)*)


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Csc[e+f*x])^(n+1)*Simp[n*(B*a+A*b)+(B*b*n+A*a*(n+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && RationalQ[n] && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_.*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(n+1)) + 
  1/(n+1)*Int[(d*Csc[e+f*x])^n*Simp[A*a*(n+1)+B*b*n+(A*b+B*a)*(n+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && Not[RationalQ[n] && n<=-1]


Int[csc[e_.+f_.*x_]*(A_+B_.*csc[e_.+f_.*x_])/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  B/b*Int[Csc[e+f*x],x] + (A*b-a*B)/b*Int[Csc[e+f*x]/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B},x] && NeQ[A*b-a*B]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) /;
FreeQ[{a,b,A,B,e,f,m},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && EqQ[a*B*m+A*b*(m+1)]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) + 
  (a*B*m+A*b*(m+1))/(a*b*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,A,B,e,f},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && NeQ[a*B*m+A*b*(m+1)] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  (a*B*m+A*b*(m+1))/(b*(m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,A,B,e,f,m},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && NeQ[a*B*m+A*b*(m+1)] && Not[RationalQ[m] && m<-1/2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*Simp[b*B*m+a*A*(m+1)+(a*B*m+A*b*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,A,B,e,f},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m] && m>0


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*Simp[(a*A-b*B)*(m+1)-(A*b-a*B)*(m+2)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,A,B,e,f},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]*(A_+B_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  -2*(A*b-a*B)*Rt[a+b*B/A,2]*Sqrt[b*(1-Csc[e+f*x])/(a+b)]*Sqrt[-b*(1+Csc[e+f*x])/(a-b)]/(b^2*f*Cot[e+f*x])*
    EllipticE[ArcSin[Sqrt[a+b*Csc[e+f*x]]/Rt[a+b*B/A,2]],(a*A+b*B)/(a*A-b*B)] /;
FreeQ[{a,b,e,f,A,B},x] && NeQ[a^2-b^2] && EqQ[A^2-B^2]


Int[csc[e_.+f_.*x_]*(A_+B_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  (A-B)*Int[Csc[e+f*x]/Sqrt[a+b*Csc[e+f*x]],x] + 
  B*Int[Csc[e+f*x]*(1+Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B},x] && NeQ[a^2-b^2] && NeQ[A^2-B^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  2*Sqrt[2]*A*(a+b*Csc[e+f*x])^m*(A-B*Csc[e+f*x])*Sqrt[(A+B*Csc[e+f*x])/A]/(B*f*Cot[e+f*x]*(A*(a+b*Csc[e+f*x])/(a*A+b*B))^m)*
    AppellF1[1/2,-(1/2),-m,3/2,(A-B*Csc[e+f*x])/(2*A),(b*(A-B*Csc[e+f*x]))/(A*b+a*B)] /;
FreeQ[{a,b,A,B,e,f},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && EqQ[A^2-B^2] && Not[IntegerQ[2*m]]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m,x] + B/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,A,B,e,f,m},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(b*f*(2*m+1)) + 
  1/(b^2*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*Simp[A*b*m-a*B*m+b*B*(2*m+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) - 
  1/(b*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[b*(A*b-a*B)*(m+1)-(a*A*b*(m+2)-B*(a^2+b^2*(m+1)))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*Simp[b*B*(m+1)+(A*b*(m+2)-a*B)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,m},x] && NeQ[A*b-a*B] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && EqQ[m+n+1] && EqQ[a*A*m-b*B*n]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(b*f*(2*m+1)) + 
  (a*A*m+b*B*(m+1))/(a^2*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && EqQ[m+n+1] && RationalQ[m] && m<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  (a*A*m-b*B*n)/(b*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && EqQ[m+n+1] && Not[RationalQ[m] && m<=-1]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -2*b*B*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Csc[e+f*x]]) /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && EqQ[A*b*(2*n+1)+2*a*B*n]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*b^2*Cot[e+f*x]*(d*Csc[e+f*x])^n/(a*f*n*Sqrt[a+b*Csc[e+f*x]]) + 
  (A*b*(2*n+1)+2*a*B*n)/(2*a*d*n)*Int[Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && NeQ[A*b*(2*n+1)+2*a*B*n] && RationalQ[n] && n<0


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -2*b*B*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Csc[e+f*x]]) + 
  (A*b*(2*n+1)+2*a*B*n)/(b*(2*n+1))*Int[Sqrt[a+b*Csc[e+f*x]]*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && NeQ[A*b*(2*n+1)+2*a*B*n] && Not[RationalQ[n] && n<0]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*n) - 
  b/(a*d*n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1)*Simp[a*A*(m-n-1)-b*B*n-(a*B*n+A*b*(m+n))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && RationalQ[m,n] && m>1/2 && n<-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n*Simp[a*A*d*(m+n)+B*(b*d*n)+(A*b*d*(m+n)+a*B*d*(2*m+n-1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && RationalQ[m] && m>1/2 && Not[RationalQ[n] && n<-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  d*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[A*(a*d*(n-1))-B*(b*d*(n-1))-d*(a*B*(m-n+1)+A*b*(m+n))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && RationalQ[m,n] && m<-1/2 && n>0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(b*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[b*B*n-a*A*(2*m+n+1)+(A*b-a*B)*(m+n+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2 && Not[RationalQ[n] && n>0]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(f*(m+n)) + 
  d/(b*(m+n))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)*Simp[b*B*(n-1)+(A*b*(m+n)+a*B*m)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && RationalQ[n] && n>1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*Simp[a*A*m-b*B*n-A*b*(m+n+1)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2] && RationalQ[n] && n<0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n,x] + 
  B/b*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NeQ[A*b-a*B] && EqQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^(n+1)*
    Simp[a*(a*B*n-A*b*(m-n-1))+(2*a*b*B*n+A*(b^2*n+a^2*(1+n)))*Csc[e+f*x]+b*(b*B*n+a*A*(m+n))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m,n] && m>1 && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n/(f*(m+n)) + 
  1/(m+n)*Int[(a+b*Csc[e+f*x])^(m-2)*(d*Csc[e+f*x])^n*
    Simp[a^2*A*(m+n)+a*b*B*n+(a*(2*A*b+a*B)*(m+n)+b^2*B*(m+n-1))*Csc[e+f*x]+b*(A*b*(m+n)+a*B*(2*m+n-1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m] && m>1 && 
  Not[IntegerQ[n] && n>1 && Not[IntegerQ[m]]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -d*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[d*(n-1)*(A*b-a*B)+d*(a*A-b*B)*(m+1)*Csc[e+f*x]-d*(A*b-a*B)*(m+n+1)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m,n] && m<-1 && 0<n<1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  a*d^2*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)/(b*f*(m+1)*(a^2-b^2)) - 
  d/(b*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)*
    Simp[a*d*(A*b-a*B)*(n-2)+b*d*(A*b-a*B)*(m+1)*Csc[e+f*x]-(a*A*b*d*(m+n)-d*B*(a^2*(n-1)+b^2*(m+1)))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  b*(A*b-a*B)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[A*(a^2*(m+1)-b^2*(m+n+1))+a*b*B*n-a*(A*b-a*B)*(m+1)*Csc[e+f*x]+b*(A*b-a*B)*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)/(f*(m+n)) + 
  d/(m+n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n-1)*
    Simp[a*B*(n-1)+(b*B*(m+n-1)+a*A*(m+n))*Csc[e+f*x]+(a*B*m+A*b*(m+n))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m,n] && 0<m<1 && n>0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1)*
    Simp[A*b*m-a*B*n-(b*B*n+a*A*(n+1))*Csc[e+f*x]-A*b*(m+n+1)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[m,n] && 0<m<1 && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  -B*d^2*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-2)/(b*f*(m+n)) + 
  d^2/(b*(m+n))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-2)*
    Simp[a*B*(n-2)+B*b*(m+n-1)*Csc[e+f*x]+(A*b*(m+n)-a*B*(n-1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[n] && n>1 && NeQ[m+n] && 
  Not[IntegerQ[m] && m>1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*
    Simp[a*B*n-A*b*(m+n+1)+A*a*(n+1)*Csc[e+f*x]+A*b*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,m},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(A_+B_.*csc[e_.+f_.*x_])/(Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  A/a*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[d*Csc[e+f*x]],x] - 
  (A*b-a*B)/(a*d)*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2]


Int[Sqrt[d_.*csc[e_.+f_.*x_]]*(A_+B_.*csc[e_.+f_.*x_])/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  A*Int[Sqrt[d*Csc[e+f*x]]/Sqrt[a+b*Csc[e+f*x]],x] + 
  B/d*Int[(d*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2]


Int[Sqrt[a_+b_.*csc[e_.+f_.*x_]]*(A_+B_.*csc[e_.+f_.*x_])/Sqrt[d_.*csc[e_.+f_.*x_]],x_Symbol] :=
  B/d*Int[Sqrt[a+b*Csc[e+f*x]]*Sqrt[d*Csc[e+f*x]],x] + 
  A*Int[Sqrt[a+b*Csc[e+f*x]]/Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2]


Int[(d_.*csc[e_.+f_.*x_])^n_*(A_+B_.*csc[e_.+f_.*x_])/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  A/a*Int[(d*Csc[e+f*x])^n,x] - (A*b-a*B)/(a*d)*Int[(d*Csc[e+f*x])^(n+1)/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,A,B,n},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_.*(A_+B_.*csc[e_.+f_.*x_]),x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*(A+B*Csc[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,A,B,m,n},x] && NeQ[A*b-a*B] && NeQ[a^2-b^2]


(* Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.*(A_.+B_.*csc[e_.+f_.*x_])^p_.,x_Symbol] :=
  (-a*c)^m*Int[Cot[e+f*x]^(2*m)*(c+d*Csc[e+f*x])^(n-m)*(A+B*Csc[e+f*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m] && 
  Not[IntegerQ[n] && (m<0 && n>0 || 0<n<m || m<n<0)] *)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.*(A_.+B_.*csc[e_.+f_.*x_])^p_.,x_Symbol] :=
  (-a*c)^m*Int[Cos[e+f*x]^(2*m)*(d+c*Sin[e+f*x])^(n-m)*(B+A*Sin[e+f*x])^p/Sin[e+f*x]^(m+n+p),x] /;
FreeQ[{a,b,c,d,e,f,A,B,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegersQ[m,n,p]





(* ::Subsection::Closed:: *)
(*4.3.4.1 (a+b sec)^m (A+B sec+C sec^2)*)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  1/b^2*Int[(a+b*Csc[e+f*x])^(m+1)*Simp[b*B-a*C+b*C*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && EqQ[A*b^2-a*b*B+a^2*C]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  C/b^2*Int[(a+b*Csc[e+f*x])^(m+1)*Simp[-a+b*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && EqQ[A*b^2+a^2*C]


Int[(b_.*csc[e_.+f_.*x_])^m_.*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(b*Csc[e+f*x])^m/(f*m) /;
FreeQ[{b,e,f,A,C,m},x] && EqQ[C*m+A*(m+1)]


Int[csc[e_.+f_.*x_]^m_.*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  Int[(C+A*Sin[e+f*x]^2)/Sin[e+f*x]^(m+2),x] /;
FreeQ[{e,f,A,C},x] && NeQ[C*m+A*(m+1)] && NegativeIntegerQ[(m+1)/2]


Int[(b_.*csc[e_.+f_.*x_])^m_.*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(b*Csc[e+f*x])^m/(f*m) + 
  (C*m+A*(m+1))/(b^2*m)*Int[(b*Csc[e+f*x])^(m+2),x] /;
FreeQ[{b,e,f,A,C},x] && NeQ[C*m+A*(m+1)] && RationalQ[m] && m<=-1


Int[(b_.*csc[e_.+f_.*x_])^m_.*(A_+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(b*Csc[e+f*x])^m/(f*(m+1)) + 
  (C*m+A*(m+1))/(m+1)*Int[(b*Csc[e+f*x])^m,x] /;
FreeQ[{b,e,f,A,C,m},x] && NeQ[C*m+A*(m+1)] && Not[RationalQ[m] && m<=-1]


Int[(b_.*csc[e_.+f_.*x_])^m_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  B/b*Int[(b*Csc[e+f*x])^(m+1),x] + Int[(b*Csc[e+f*x])^m*(A+C*Csc[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,B,C,m},x]


Int[(a_+b_.*csc[e_.+f_.*x_])*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Csc[e+f*x]*Cot[e+f*x]/(2*f) + 
  1/2*Int[Simp[2*A*a+(2*B*a+b*(2*A+C))*Csc[e+f*x]+2*(a*C+B*b)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x]


Int[(a_+b_.*csc[e_.+f_.*x_])*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Csc[e+f*x]*Cot[e+f*x]/(2*f) + 
  1/2*Int[Simp[2*A*a+b*(2*A+C)*Csc[e+f*x]+2*a*C*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x]


Int[(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  C/b*Int[Csc[e+f*x],x] + 1/b*Int[(A*b+(b*B-a*C)*Csc[e+f*x])/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,B,C},x]


Int[(A_.+C_.*csc[e_.+f_.*x_]^2)/(a_+b_.*csc[e_.+f_.*x_]),x_Symbol] :=
  C/b*Int[Csc[e+f*x],x] + 1/b*Int[(A*b-a*C*Csc[e+f*x])/(a+b*Csc[e+f*x]),x] /;
FreeQ[{a,b,e,f,A,C},x]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A-b*B+a*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*Simp[A*b*(2*m+1)+(b*B*(m+1)-a*(A*(m+1)-C*m))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A+C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*Simp[A*b*(2*m+1)-a*(A*(m+1)-C*m)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(b*(m+1))*Int[(a+b*Csc[e+f*x])^m*Simp[A*b*(m+1)+(a*C*m+b*B*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(b*(m+1))*Int[(a+b*Csc[e+f*x])^m*Simp[A*b*(m+1)+a*C*m*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Csc[e+f*x])^(m-1)*
    Simp[a*A*(m+1)+((A*b+a*B)*(m+1)+b*C*m)*Csc[e+f*x]+(b*B*(m+1)+a*C*m)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NeQ[a^2-b^2] && PositiveIntegerQ[2*m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Csc[e+f*x])^(m-1)*Simp[a*A*(m+1)+(A*b*(m+1)+b*C*m)*Csc[e+f*x]+a*C*m*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NeQ[a^2-b^2] && PositiveIntegerQ[2*m]


Int[(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Int[(A+(B-C)*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] + C*Int[Csc[e+f*x]*(1+Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NeQ[a^2-b^2]


Int[(A_.+C_.*csc[e_.+f_.*x_]^2)/Sqrt[a_+b_.*csc[e_.+f_.*x_]],x_Symbol] :=
  Int[(A-C*Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] + C*Int[Csc[e+f*x]*(1+Csc[e+f*x])/Sqrt[a+b*Csc[e+f*x]],x] /;
FreeQ[{a,b,e,f,A,C},x] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*
    Simp[A*(a^2-b^2)*(m+1)-a*(A*b-a*B+b*C)*(m+1)*Csc[e+f*x]+(A*b^2-a*b*B+a^2*C)*(m+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*
    Simp[A*(a^2-b^2)*(m+1)-a*b*(A+C)*(m+1)*Csc[e+f*x]+(A*b^2+a^2*C)*(m+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NeQ[a^2-b^2] && IntegerQ[2*m] && m<-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  1/b*Int[(a+b*Csc[e+f*x])^m*(A*b+(b*B-a*C)*Csc[e+f*x]),x] + C/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NeQ[a^2-b^2] && Not[IntegerQ[2*m]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  1/b*Int[(a+b*Csc[e+f*x])^m*(A*b-a*C*Csc[e+f*x]),x] + C/b*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NeQ[a^2-b^2] && Not[IntegerQ[2*m]]


Int[(b_.*cos[e_.+f_.*x_])^m_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  b^2*Int[(b*Cos[e+f*x])^(m-2)*(C+B*Cos[e+f*x]+A*Cos[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,B,C,m},x] && Not[IntegerQ[m]]


Int[(b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  b^2*Int[(b*Sin[e+f*x])^(m-2)*(C+B*Sin[e+f*x]+A*Sin[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,B,C,m},x] && Not[IntegerQ[m]]


Int[(b_.*cos[e_.+f_.*x_])^m_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  b^2*Int[(b*Cos[e+f*x])^(m-2)*(C+A*Cos[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,C,m},x] && Not[IntegerQ[m]]


Int[(b_.*sin[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  b^2*Int[(b*Sin[e+f*x])^(m-2)*(C+A*Sin[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,C,m},x] && Not[IntegerQ[m]]


Int[(a_.*(b_.*sec[e_.+f_.*x_])^p_)^m_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  a^IntPart[m]*(a*(b*Sec[e+f*x])^p)^FracPart[m]/(b*Sec[e+f*x])^(p*FracPart[m])*
    Int[(b*Sec[e+f*x])^(m*p)*(A+B*Sec[e+f*x]+C*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,e,f,A,B,C,m,p},x] && Not[IntegerQ[m]]


Int[(a_.*(b_.*csc[e_.+f_.*x_])^p_)^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  a^IntPart[m]*(a*(b*Csc[e+f*x])^p)^FracPart[m]/(b*Csc[e+f*x])^(p*FracPart[m])*
    Int[(b*Csc[e+f*x])^(m*p)*(A+B*Csc[e+f*x]+C*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,e,f,A,B,C,m,p},x] && Not[IntegerQ[m]]


Int[(a_.*(b_.*sec[e_.+f_.*x_])^p_)^m_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  a^IntPart[m]*(a*(b*Sec[e+f*x])^p)^FracPart[m]/(b*Sec[e+f*x])^(p*FracPart[m])*
    Int[(b*Sec[e+f*x])^(m*p)*(A+C*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,e,f,A,C,m,p},x] && Not[IntegerQ[m]]


Int[(a_.*(b_.*csc[e_.+f_.*x_])^p_)^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  a^IntPart[m]*(a*(b*Csc[e+f*x])^p)^FracPart[m]/(b*Csc[e+f*x])^(p*FracPart[m])*
    Int[(b*Csc[e+f*x])^(m*p)*(A+C*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,e,f,A,C,m,p},x] && Not[IntegerQ[m]]





(* ::Subsection::Closed:: *)
(*4.3.4.2 (a+b sec)^m (d sec)^n (A+B sec+C sec^2)*)


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Csc[e+f*x])^(n+1)*Simp[n*(B*a+A*b)+(n*(a*C+B*b)+A*a*(n+1))*Csc[e+f*x]+b*C*n*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && RationalQ[n] && n<-1


Int[(a_+b_.*csc[e_.+f_.*x_])*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*a*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*n) + 
  1/(d*n)*Int[(d*Csc[e+f*x])^(n+1)*Simp[A*b*n+a*(C*n+A*(n+1))*Csc[e+f*x]+b*C*n*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && RationalQ[n] && n<-1


Int[(d_.*csc[e_.+f_.*x_])^n_.*(a_+b_.*csc[e_.+f_.*x_])*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Csc[e+f*x]*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(n+2)) + 
  1/(n+2)*Int[(d*Csc[e+f*x])^n*Simp[A*a*(n+2)+(B*a*(n+2)+b*(C*(n+1)+A*(n+2)))*Csc[e+f*x]+(a*C+B*b)*(n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && Not[RationalQ[n] && n<-1]


Int[(d_.*csc[e_.+f_.*x_])^n_.*(a_+b_.*csc[e_.+f_.*x_])*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -b*C*Csc[e+f*x]*Cot[e+f*x]*(d*Csc[e+f*x])^n/(f*(n+2)) + 
  1/(n+2)*Int[(d*Csc[e+f*x])^n*Simp[A*a*(n+2)+b*(C*(n+1)+A*(n+2))*Csc[e+f*x]+a*C*(n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && Not[RationalQ[n] && n<-1]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A-b*B+a*C)*Cot[e+f*x]*Csc[e+f*x]*(a+b*Csc[e+f*x])^m/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[a*B-b*C-2*A*b*(m+1)-(b*B*(m+2)-a*(A*(m+2)-C*(m-1)))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && RationalQ[m] && m<-1 && EqQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(A+C)*Cot[e+f*x]*Csc[e+f*x]*(a+b*Csc[e+f*x])^m/(f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[-b*C-2*A*b*(m+1)+a*(A*(m+2)-C*(m-1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && RationalQ[m] && m<-1 && EqQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[b*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && RationalQ[m] && m<-1 && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[a*b*(A+C)*(m+1)-(A*b^2+a^2*C+b*(A*b+b*C)*(m+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && RationalQ[m] && m<-1 && NeQ[a^2-b^2]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*Simp[b*A*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && Not[RationalQ[m] && m<-1]


Int[csc[e_.+f_.*x_]*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*Simp[b*A*(m+2)+b*C*(m+1)-a*C*Csc[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -(a*A-b*B+a*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[a*B*n-b*C*n-A*b*(2*m+n+1)-(b*B*(m+n+1)-a*(A*(m+n+1)-C*(m-n)))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -a*(A+C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[b*C*n+A*b*(2*m+n+1)-(a*(A*(m+n+1)-C*(m-n)))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*Simp[a*A*m-b*B*n-b*(A*(m+n+1)+C*n)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && (RationalQ[n] && n<-1/2 || EqQ[m+n+1])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(b*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*Simp[a*A*m-b*(A*(m+n+1)+C*n)*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && (RationalQ[n] && n<-1/2 || EqQ[m+n+1])


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*Simp[A*b*(m+n+1)+b*C*n+(a*C*m+b*B*(m+n+1))*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m,n},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && Not[RationalQ[n] && n<-1/2] && NeQ[m+n+1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*Simp[A*b*(m+n+1)+b*C*n+a*C*m*Csc[e+f*x],x],x] /;
FreeQ[{a,b,d,e,f,A,C,m,n},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && Not[RationalQ[n] && n<-1/2] && NeQ[m+n+1]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[b*(m+1)*(-a*(b*B-a*C)+A*b^2)+
      (b*B*(a^2+b^2*(m+1))-a*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Csc[e+f*x]-
      b*C*(m+1)*(a^2-b^2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*
    Simp[b*(m+1)*(a^2*C+A*b^2)-a*(A*b^2*(m+2)+C*(a^2+b^2*(m+1)))*Csc[e+f*x]-b*C*(m+1)*(a^2-b^2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Csc[e+f*x]*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*
    Simp[a*C+b*(C*(m+2)+A*(m+3))*Csc[e+f*x]-(2*a*C-b*B*(m+3))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && NeQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[csc[e_.+f_.*x_]^2*(a_+b_.*csc[e_.+f_.*x_])^m_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Csc[e+f*x]*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[Csc[e+f*x]*(a+b*Csc[e+f*x])^m*Simp[a*C+b*(C*(m+2)+A*(m+3))*Csc[e+f*x]-2*a*C*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && NeQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1)*
    Simp[A*b*m-a*B*n-(b*B*n+a*(C*n+A*(n+1)))*Csc[e+f*x]-b*(C*n+A*(m+n+1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NeQ[a^2-b^2] && RationalQ[m,n] && m>0 && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*n) - 
  1/(d*n)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^(n+1)*
    Simp[A*b*m-a*(C*n+A*(n+1))*Csc[e+f*x]-b*(C*n+A*(m+n+1))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NeQ[a^2-b^2] && RationalQ[m,n] && m>0 && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+n+1)) + 
  1/(m+n+1)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n*
    Simp[a*A*(m+n+1)+a*C*n+((A*b+a*B)*(m+n+1)+b*C*(m+n))*Csc[e+f*x]+(b*B*(m+n+1)+a*C*m)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && NeQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[n] && n<=-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cot[e+f*x]*(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n/(f*(m+n+1)) + 
  1/(m+n+1)*Int[(a+b*Csc[e+f*x])^(m-1)*(d*Csc[e+f*x])^n*
    Simp[a*A*(m+n+1)+a*C*n+b*(A*(m+n+1)+C*(m+n))*Csc[e+f*x]+a*C*m*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && NeQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[n] && n<=-1]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -d*(A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(b*f*(a^2-b^2)*(m+1)) + 
  d/(b*(a^2-b^2)*(m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[A*b^2*(n-1)-a*(b*B-a*C)*(n-1)+
      b*(a*A-b*B+a*C)*(m+1)*Csc[e+f*x]-
      (b*(A*b-a*B)*(m+n+1)+C*(a^2*n+b^2*(m+1)))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NeQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -d*(A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(b*f*(a^2-b^2)*(m+1)) + 
  d/(b*(a^2-b^2)*(m+1))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)*
    Simp[A*b^2*(n-1)+a^2*C*(n-1)+a*b*(A+C)*(m+1)*Csc[e+f*x]-(A*b^2*(m+n+1)+C*(a^2*n+b^2*(m+1)))*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NeQ[a^2-b^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[a*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C)*(m+n+1)-
      a*(A*b-a*B+b*C)*(m+1)*Csc[e+f*x]+
      (A*b^2-a*b*B+a^2*C)*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b^2+a^2*C)*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*(m+1)*(a^2-b^2)) + 
  1/(a*(m+1)*(a^2-b^2))*Int[(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n*
    Simp[a^2*(A+C)*(m+1)-(A*b^2+a^2*C)*(m+n+1)-a*b*(A+C)*(m+1)*Csc[e+f*x]+(A*b^2+a^2*C)*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && Not[NegativeIntegerQ[m+1/2,n]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(b*f*(m+n+1)) + 
  d/(b*(m+n+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)*
    Simp[a*C*(n-1)+(A*b*(m+n+1)+b*C*(m+n))*Csc[e+f*x]+(b*B*(m+n+1)-a*C*n)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && NeQ[a^2-b^2] && RationalQ[n] && n>0 (* && Not[IntegerQ[m] && m>0 && Not[IntegerQ[n]]] *)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  -C*d*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^(n-1)/(b*f*(m+n+1)) + 
  d/(b*(m+n+1))*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n-1)*
    Simp[a*C*(n-1)+(A*b*(m+n+1)+b*C*(m+n))*Csc[e+f*x]-a*C*n*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && NeQ[a^2-b^2] && RationalQ[n] && n>0 (* && Not[IntegerQ[m] && m>0 && Not[IntegerQ[n]]] *)


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*
    Simp[a*B*n-A*b*(m+n+1)+a*(A+A*n+C*n)*Csc[e+f*x]+A*b*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,B,C,m},x] && NeQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(a_+b_.*csc[e_.+f_.*x_])^m_*(d_.*csc[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cot[e+f*x]*(a+b*Csc[e+f*x])^(m+1)*(d*Csc[e+f*x])^n/(a*f*n) + 
  1/(a*d*n)*Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n+1)*
    Simp[-A*b*(m+n+1)+a*(A+A*n+C*n)*Csc[e+f*x]+A*b*(m+n+2)*Csc[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,A,C,m},x] && NeQ[a^2-b^2] && RationalQ[n] && n<=-1


Int[(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)/(Sqrt[d_.*csc[e_.+f_.*x_]]*(a_+b_.*csc[e_.+f_.*x_])),x_Symbol] :=
  (A*b^2-a*b*B+a^2*C)/(a^2*d^2)*Int[(d*Csc[e+f*x])^(3/2)/(a+b*Csc[e+f*x]),x] + 
  1/a^2*Int[(a*A-(A*b-a*B)*Csc[e+f*x])/Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NeQ[a^2-b^2]


Int[(A_.+C_.*csc[e_.+f_.*x_]^2)/(Sqrt[d_.*csc[e_.+f_.*x_]]*(a_+b_.*csc[e_.+f_.*x_])),x_Symbol] :=
  (A*b^2+a^2*C)/(a^2*d^2)*Int[(d*Csc[e+f*x])^(3/2)/(a+b*Csc[e+f*x]),x] + 
  1/a^2*Int[(a*A-A*b*Csc[e+f*x])/Sqrt[d*Csc[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NeQ[a^2-b^2]


Int[(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2)/(Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  C/d^2*Int[(d*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] + 
  Int[(A+B*Csc[e+f*x])/(Sqrt[d*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NeQ[a^2-b^2]


Int[(A_.+C_.*csc[e_.+f_.*x_]^2)/(Sqrt[d_.*csc[e_.+f_.*x_]]*Sqrt[a_+b_.*csc[e_.+f_.*x_]]),x_Symbol] :=
  C/d^2*Int[(d*Csc[e+f*x])^(3/2)/Sqrt[a+b*Csc[e+f*x]],x] + 
  A*Int[1/(Sqrt[d*Csc[e+f*x]]*Sqrt[a+b*Csc[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NeQ[a^2-b^2]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*(A+B*Csc[e+f*x]+C*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,B,C,m,n},x]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*csc[e_.+f_.*x_])^n_.*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^n*(A+C*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,C,m,n},x]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  d^(m+2)*Int[(b+a*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n-m-2)*(C+B*Cos[e+f*x]+A*Cos[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  d^(m+2)*Int[(b+a*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n-m-2)*(C+B*Sin[e+f*x]+A*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,B,C,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(d_.*cos[e_.+f_.*x_])^n_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  d^(m+2)*Int[(b+a*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n-m-2)*(C+A*Cos[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  d^(m+2)*Int[(b+a*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n-m-2)*(C+A*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,A,C,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(c_.*(d_.*sec[e_.+f_.*x_])^p_)^n_*(A_.+B_.*sec[e_.+f_.*x_]+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  c^IntPart[n]*(c*(d*Sec[e+f*x])^p)^FracPart[n]/(d*Sec[e+f*x])^(p*FracPart[n])*
    Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n*p)*(A+B*Sec[e+f*x]+C*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && Not[IntegerQ[n]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_.*(d_.*csc[e_.+f_.*x_])^p_)^n_*(A_.+B_.*csc[e_.+f_.*x_]+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  c^IntPart[n]*(c*(d*Csc[e+f*x])^p)^FracPart[n]/(d*Csc[e+f*x])^(p*FracPart[n])*
    Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n*p)*(A+B*Csc[e+f*x]+C*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && Not[IntegerQ[n]]


Int[(a_+b_.*sec[e_.+f_.*x_])^m_.*(c_.*(d_.*sec[e_.+f_.*x_])^p_)^n_*(A_.+C_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  c^IntPart[n]*(c*(d*Sec[e+f*x])^p)^FracPart[n]/(d*Sec[e+f*x])^(p*FracPart[n])*
    Int[(a+b*Sec[e+f*x])^m*(d*Sec[e+f*x])^(n*p)*(A+C*Sec[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n,p},x] && Not[IntegerQ[n]]


Int[(a_+b_.*csc[e_.+f_.*x_])^m_.*(c_.*(d_.*csc[e_.+f_.*x_])^p_)^n_*(A_.+C_.*csc[e_.+f_.*x_]^2),x_Symbol] :=
  c^IntPart[n]*(c*(d*Csc[e+f*x])^p)^FracPart[n]/(d*Csc[e+f*x])^(p*FracPart[n])*
    Int[(a+b*Csc[e+f*x])^m*(d*Csc[e+f*x])^(n*p)*(A+C*Csc[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n,p},x] && Not[IntegerQ[n]]





(* ::Subsection::Closed:: *)
(*4.3.7 (d trig)^m (a+b (c sec)^n)^p*)


Int[u_.*(a_+b_.*sec[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  b^p*Int[ActivateTrig[u*tan[e+f*x]^(2*p)],x] /;
FreeQ[{a,b,e,f,p},x] && EqQ[a+b,0] && IntegerQ[p]


Int[u_.*(a_+b_.*sec[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  Int[ActivateTrig[u*(b*tan[e+f*x]^2)^p],x] /;
FreeQ[{a,b,e,f,p},x] && EqQ[a+b,0]


Int[(b_.*sec[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  b*ff/f*Subst[Int[(b+b*ff^2*x^2)^(p-1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{b,e,f,p},x] && Not[IntegerQ[p]]


Int[(b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  b^IntPart[p]*(b*(c*Sec[e+f*x])^n)^FracPart[p]/(c*Sec[e+f*x])^(n*FracPart[p])*Int[(c*Sec[e+f*x])^(n*p),x] /;
FreeQ[{b,c,e,f,n,p},x] && Not[IntegerQ[p]]


Int[tan[e_.+f_.*x_]^m_.*(b_.*sec[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
  b/(2*f)*Subst[Int[(-1+x)^((m-1)/2)*(b*x)^(p-1),x],x,Sec[e+f*x]^2] /;
FreeQ[{b,e,f,p},x] && Not[IntegerQ[p]] && IntegerQ[(m-1)/2]


Int[u_.*(b_.*sec[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Sec[e+f*x],x]},
  (b*ff^n)^IntPart[p]*(b*Sec[e+f*x]^n)^FracPart[p]/(Sec[e+f*x]/ff)^(n*FracPart[p])*
    Int[ActivateTrig[u]*(Sec[e+f*x]/ff)^(n*p),x]] /;
FreeQ[{b,e,f,n,p},x] && Not[IntegerQ[p]] && IntegerQ[n] && 
  (EqQ[u,1] || MatchQ[u,(d_.*trig_[e+f*x])^m_. /; FreeQ[{d,m},x] && MemberQ[{sin,cos,tan,cot,sec,csc},trig]])


Int[u_.*(b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  b^IntPart[p]*(b*(c*Sec[e+f*x])^n)^FracPart[p]/(c*Sec[e+f*x])^(n*FracPart[p])*
    Int[ActivateTrig[u]*(c*Sec[e+f*x])^(n*p),x] /;
FreeQ[{b,c,e,f,n,p},x] && Not[IntegerQ[p]] && Not[IntegerQ[n]] && 
  (EqQ[u,1] || MatchQ[u,(d_.*trig_[e+f*x])^m_. /; FreeQ[{d,m},x] && MemberQ[{sin,cos,tan,cot,sec,csc},trig]])


Int[1/(a_+b_.*sec[e_.+f_.*x_]^2),x_Symbol] :=
  x/a - b/a*Int[1/(b+a*Cos[e+f*x]^2),x] /;
FreeQ[{a,b,e,f},x] && NeQ[a+b,0]


Int[(a_+b_.*sec[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(a+b+b*ff^2*x^2)^p/(1+ff^2*x^2),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && NeQ[a+b,0] && NeQ[p,-1]


Int[(a_+b_.*sec[e_.+f_.*x_]^4)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(a+b+2*b*ff^2*x^2+b*ff^4*x^4)^p/(1+ff^2*x^2),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[2*p]


Int[(a_+b_.*sec[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(a+b*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[n/2] && IGtQ[p,-2]


Int[(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  Defer[Int][(a+b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,e,f,n,p},x]


Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sec[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff^(m+1)/f*Subst[Int[x^m*ExpandToSum[a+b*(1+ff^2*x^2)^(n/2),x]^p/(1+ff^2*x^2)^(m/2+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[m/2] && IntegerQ[n/2]


Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*sec[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Cos[e+f*x],x]},
  -ff/f*Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(b+a*(ff*x)^n)^p/(ff*x)^(n*p),x],x,Cos[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[(m-1)/2] && IntegerQ[n] && IntegerQ[p]


Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Cos[e+f*x],x]},
  1/(f*ff^m)*Subst[Int[(-1+ff^2*x^2)^((m-1)/2)*(a+b*(c*ff*x)^n)^p/x^(m+1),x],x,Sec[e+f*x]/ff]] /;
FreeQ[{a,b,c,e,f,n,p},x] && IntegerQ[(m-1)/2] && (m>0 || EqQ[n,2] || EqQ[n,4])


Int[(d_.*sin[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Defer[Int][(d*Sin[e+f*x])^m*(a+b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(d_.*cos[e_.+f_.*x_])^m_*(a_+b_.*sec[e_.+f_.*x_]^n_.)^p_.,x_Symbol] :=
  d^(n*p)*Int[(d*Cos[e+f*x])^(m-n*p)*(b+a*Cos[e+f*x]^n)^p,x] /;
FreeQ[{a,b,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && IntegersQ[n,p]


Int[(d_.*cos[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  (d*Cos[e+f*x])^FracPart[m]*(Sec[e+f*x]/d)^FracPart[m]*Int[(Sec[e+f*x]/d)^(-m)*(a+b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]


Int[tan[e_.+f_.*x_]^m_.*(a_+b_.*sec[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  Module[{ff=FreeFactors[Cos[e+f*x],x]},
  -1/(f*ff^(m+n*p-1))*Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(b+a*(ff*x)^n)^p/x^(m+n*p),x],x,Cos[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,n},x] && IntegerQ[(m-1)/2] && IntegerQ[n] && IntegerQ[p]


Int[tan[e_.+f_.*x_]^m_.*(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Sec[e+f*x],x]},
  1/f*Subst[Int[(-1+ff^2*x^2)^((m-1)/2)*(a+b*(c*ff*x)^n)^p/x,x],x,Sec[e+f*x]/ff]] /;
FreeQ[{a,b,c,e,f,n,p},x] && IntegerQ[(m-1)/2] && (m>0 || EqQ[n,2] || EqQ[n,4] || IGtQ[p,0] || IntegersQ[2*n,p])


Int[(d_.*tan[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  b*ff/f*Subst[Int[(d*ff*x)^m*(b+b*ff^2*x^2)^(p-1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{b,e,f,m,p},x]


Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sec[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(d*ff*x)^m*(a+b*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,m,p},x] && IntegerQ[n/2] && (IntegerQ[m/2] || EqQ[n,2])


Int[(d_.*tan[e_.+f_.*x_])^m_*(b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  d*(d*Tan[e+f*x])^(m-1)*(b*(c*Sec[e+f*x])^n)^p/(f*(p*n+m-1)) - 
  d^2*(m-1)/(p*n+m-1)*Int[(d*Tan[e+f*x])^(m-2)*(b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{b,d,c,e,f,p,n},x] && GtQ[m,1] && NeQ[p*n+m-1,0] && IntegersQ[2*p*n,2*m]


Int[(d_.*tan[e_.+f_.*x_])^m_*(b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  (d*Tan[e+f*x])^(m+1)*(b*(c*Sec[e+f*x])^n)^p/(d*f*(m+1)) - 
  (p*n+m+1)/(d^2*(m+1))*Int[(d*Tan[e+f*x])^(m+2)*(b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{b,d,c,e,f,p,n},x] && LtQ[m,-1] && NeQ[p*n+m+1,0] && IntegersQ[2*p*n,2*m]


Int[(d_.*tan[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Defer[Int][(d*Tan[e+f*x])^m*(a+b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(d_.*cot[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  (d*Cot[e+f*x])^FracPart[m]*(Tan[e+f*x]/d)^FracPart[m]*Int[(Tan[e+f*x]/d)^(-m)*(a+b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]


Int[sec[e_.+f_.*x_]^m_*(a_+b_.*sec[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(1+ff^2*x^2)^(m/2-1)*ExpandToSum[a+b*(1+ff^2*x^2)^(n/2),x]^p,x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[m/2] && IntegerQ[n/2]


Int[sec[e_.+f_.*x_]^m_.*(a_+b_.*sec[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x],x]},
  ff/f*Subst[Int[ExpandToSum[b+a*(1-ff^2*x^2)^(n/2),x]^p/(1-ff^2*x^2)^((m+n*p+1)/2),x],x,Sin[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[(m-1)/2] && IntegerQ[n/2] && IntegerQ[p]


Int[sec[e_.+f_.*x_]^m_.*(a_+b_.*sec[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x],x]},
  ff/f*Subst[Int[(a+b/(1-ff^2*x^2)^(n/2))^p/(1-ff^2*x^2)^((m+1)/2),x],x,Sin[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2] && IntegerQ[n/2] && Not[IntegerQ[p]]


Int[sec[e_.+f_.*x_]^m_.*(a_+b_.*sec[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[sec[e+f*x]^m*(a+b*sec[e+f*x]^n)^p,x],x] /;
FreeQ[{a,b,e,f},x] && IntegersQ[m,n,p]


Int[(d_.*sec[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Defer[Int][(d*Sec[e+f*x])^m*(a+b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(d_.*csc[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sec[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  (d*Csc[e+f*x])^FracPart[m]*(Sin[e+f*x]/d)^FracPart[m]*Int[(Sin[e+f*x]/d)^(-m)*(a+b*(c*Sec[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]





(* ::Subsection::Closed:: *)
(*4.3.9 trig^m (a+b sec^n+c sec^(2 n))^p*)


Int[(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Sec[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Csc[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sec[d+e*x]^n+c*Sec[d+e*x]^(2*n))^p/(b+2*c*Sec[d+e*x]^n)^(2*p)*Int[u*(b+2*c*Sec[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Csc[d+e*x]^n+c*Csc[d+e*x]^(2*n))^p/(b+2*c*Csc[d+e*x]^n)^(2*p)*Int[u*(b+2*c*Csc[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[1/(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Sec[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Sec[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c]


Int[1/(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Csc[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Csc[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[d+e*x],x]},
  -f/e*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(b+a*(f*x)^n)^p/(f*x)^(n*p),x],x,Cos[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && OddQ[m] && IntegersQ[n,p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[d+e*x],x]},
  f/e*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(b+a*(f*x)^n)^p/(f*x)^(n*p),x],x,Sin[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && OddQ[m] && IntegersQ[n,p]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*sec[d_.+e_.*x_]^n_+c_.*sec[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2)+c*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(m/2+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[n2-2*n] && EvenQ[m] && EvenQ[n]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*csc[d_.+e_.*x_]^n_+c_.*csc[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2)+c*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(m/2+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[n2-2*n] && EvenQ[m] && EvenQ[n]


Int[sec[d_.+e_.*x_]^m_.*(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Sec[d+e*x]^m*(b+2*c*Sec[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[csc[d_.+e_.*x_]^m_.*(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Csc[d+e*x]^m*(b+2*c*Csc[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[sec[d_.+e_.*x_]^m_.*(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sec[d+e*x]^n+c*Sec[d+e*x]^(2*n))^p/(b+2*c*Sec[d+e*x]^n)^(2*p)*Int[Sec[d+e*x]^m*(b+2*c*Sec[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[csc[d_.+e_.*x_]^m_.*(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Csc[d+e*x]^n+c*Csc[d+e*x]^(2*n))^p/(b+2*c*Csc[d+e*x]^n)^(2*p)*Int[Csc[d+e*x]^m*(b+2*c*Csc[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[sec[d_.+e_.*x_]^m_.*(a_.+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  Int[ExpandTrig[sec[d+e*x]^m*(a+b*sec[d+e*x]^n+c*sec[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && IntegersQ[m,n,p]


Int[csc[d_.+e_.*x_]^m_.*(a_.+b_.*csc[d_.+e_.*x_]^n_.+c_.*csc[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  Int[ExpandTrig[csc[d+e*x]^m*(a+b*csc[d+e*x]^n+c*csc[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && IntegersQ[m,n,p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*sec[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cos[d+e*x],x]},
  -1/(e*f^(m+n*p-1))*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(c+b*(f*x)^n+c*(f*x)^(2*n))^p/x^(m+2*n*p),x],x,Cos[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && OddQ[m] && IntegerQ[n] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*csc[d_.+e_.*x_]^n_.+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Sin[d+e*x],x]},
  1/(e*f^(m+n*p-1))*Subst[Int[(1-f^2*x^2)^((m-1)/2)*(c+b*(f*x)^n+c*(f*x)^(2*n))^p/x^(m+2*n*p),x],x,Sin[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && OddQ[m] && IntegerQ[n] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*sec[d_.+e_.*x_]^n_+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2)+c*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && EvenQ[n]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*csc[d_.+e_.*x_]^n_+c_.*sec[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[a+b*(1+f^2*x^2)^(n/2)+c*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && EvenQ[n]


Int[(A_+B_.*sec[d_.+e_.*x_])*(a_+b_.*sec[d_.+e_.*x_]+c_.*sec[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Sec[d+e*x])*(b+2*c*Sec[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*csc[d_.+e_.*x_])*(a_+b_.*csc[d_.+e_.*x_]+c_.*csc[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Csc[d+e*x])*(b+2*c*Csc[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*sec[d_.+e_.*x_])*(a_+b_.*sec[d_.+e_.*x_]+c_.*sec[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Sec[d+e*x]+c*Sec[d+e*x]^2)^n/(b+2*c*Sec[d+e*x])^(2*n)*Int[(A+B*Sec[d+e*x])*(b+2*c*Sec[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*csc[d_.+e_.*x_])*(a_+b_.*csc[d_.+e_.*x_]+c_.*csc[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Csc[d+e*x]+c*Csc[d+e*x]^2)^n/(b+2*c*Csc[d+e*x])^(2*n)*Int[(A+B*Csc[d+e*x])*(b+2*c*Csc[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*sec[d_.+e_.*x_])/(a_.+b_.*sec[d_.+e_.*x_]+c_.*sec[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Sec[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Sec[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c]


Int[(A_+B_.*csc[d_.+e_.*x_])/(a_.+b_.*csc[d_.+e_.*x_]+c_.*csc[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Csc[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Csc[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c]


Int[(A_+B_.*sec[d_.+e_.*x_])*(a_.+b_.*sec[d_.+e_.*x_]+c_.*sec[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*sec[d+e*x])*(a+b*sec[d+e*x]+c*sec[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*csc[d_.+e_.*x_])*(a_.+b_.*csc[d_.+e_.*x_]+c_.*csc[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*csc[d+e*x])*(a+b*csc[d+e*x]+c*csc[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c] && IntegerQ[n]





(* ::Subsection::Closed:: *)
(*4.3.10 (c+d x)^m (a+b sec)^n*)


Int[(c_.+d_.*x_)^m_.*csc[e_.+k_.*Pi+f_.*Complex[0,fz_]*x_],x_Symbol] :=
  -2*(c+d*x)^m*ArcTanh[E^(-I*k*Pi)*E^(-I*e+f*fz*x)]/(f*fz*I) - 
  d*m/(f*fz*I)*Int[(c+d*x)^(m-1)*Log[1-E^(-I*k*Pi)*E^(-I*e+f*fz*x)],x] + 
  d*m/(f*fz*I)*Int[(c+d*x)^(m-1)*Log[1+E^(-I*k*Pi)*E^(-I*e+f*fz*x)],x] /;
FreeQ[{c,d,e,f,fz},x] && IntegerQ[2*k] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*csc[e_.+k_.*Pi+f_.*x_],x_Symbol] :=
  -2*(c+d*x)^m*ArcTanh[E^(I*k*Pi)*E^(I*(e+f*x))]/f - 
  d*m/f*Int[(c+d*x)^(m-1)*Log[1-E^(I*k*Pi)*E^(I*(e+f*x))],x] + 
  d*m/f*Int[(c+d*x)^(m-1)*Log[1+E^(I*k*Pi)*E^(I*(e+f*x))],x] /;
FreeQ[{c,d,e,f},x] && IntegerQ[2*k] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*csc[e_.+f_.*Complex[0,fz_]*x_],x_Symbol] :=
  -2*(c+d*x)^m*ArcTanh[E^(-I*e+f*fz*x)]/(f*fz*I) - 
  d*m/(f*fz*I)*Int[(c+d*x)^(m-1)*Log[1-E^(-I*e+f*fz*x)],x] + 
  d*m/(f*fz*I)*Int[(c+d*x)^(m-1)*Log[1+E^(-I*e+f*fz*x)],x] /;
FreeQ[{c,d,e,f,fz},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*csc[e_.+f_.*x_],x_Symbol] :=
  -2*(c+d*x)^m*ArcTanh[E^(I*(e+f*x))]/f - 
  d*m/f*Int[(c+d*x)^(m-1)*Log[1-E^(I*(e+f*x))],x] + 
  d*m/f*Int[(c+d*x)^(m-1)*Log[1+E^(I*(e+f*x))],x] /;
FreeQ[{c,d,e,f},x] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*csc[e_.+f_.*x_]^2,x_Symbol] :=
  -(c+d*x)^m*Cot[e+f*x]/f + 
  d*m/f*Int[(c+d*x)^(m-1)*Cot[e+f*x],x] /;
FreeQ[{c,d,e,f},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*(c+d*x)*Cot[e+f*x]*(b*Csc[e+f*x])^(n-2)/(f*(n-1)) - 
  b^2*d*(b*Csc[e+f*x])^(n-2)/(f^2*(n-1)*(n-2)) + 
  b^2*(n-2)/(n-1)*Int[(c+d*x)*(b*Csc[e+f*x])^(n-2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[n] && n>1 && n!=2


Int[(c_.+d_.*x_)^m_*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*(c+d*x)^m*Cot[e+f*x]*(b*Csc[e+f*x])^(n-2)/(f*(n-1)) - 
  b^2*d*m*(c+d*x)^(m-1)*(b*Csc[e+f*x])^(n-2)/(f^2*(n-1)*(n-2)) + 
  b^2*(n-2)/(n-1)*Int[(c+d*x)^m*(b*Csc[e+f*x])^(n-2),x] + 
  b^2*d^2*m*(m-1)/(f^2*(n-1)*(n-2))*Int[(c+d*x)^(m-2)*(b*Csc[e+f*x])^(n-2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n>1 && n!=2 && m>1


Int[(c_.+d_.*x_)*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  d*(b*Csc[e+f*x])^n/(f^2*n^2) + 
  (c+d*x)*Cos[e+f*x]*(b*Csc[e+f*x])^(n+1)/(b*f*n) + 
  (n+1)/(b^2*n)*Int[(c+d*x)*(b*Csc[e+f*x])^(n+2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[n] && n<-1


Int[(c_.+d_.*x_)^m_*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  d*m*(c+d*x)^(m-1)*(b*Csc[e+f*x])^n/(f^2*n^2) + 
  (c+d*x)^m*Cos[e+f*x]*(b*Csc[e+f*x])^(n+1)/(b*f*n) + 
  (n+1)/(b^2*n)*Int[(c+d*x)^m*(b*Csc[e+f*x])^(n+2),x] - 
  d^2*m*(m-1)/(f^2*n^2)*Int[(c+d*x)^(m-2)*(b*Csc[e+f*x])^n,x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n<-1 && m>1


Int[(c_.+d_.*x_)^m_.*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*Sin[e+f*x])^n*(b*Csc[e+f*x])^n*Int[(c+d*x)^m/(b*Sin[e+f*x])^n,x] /;
FreeQ[{b,c,d,e,f,m,n},x] && Not[IntegerQ[n]]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*Csc[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[m,n]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,Sin[e+f*x]^(-n)/(b+a*Sin[e+f*x])^(-n),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NegativeIntegerQ[n] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*csc[e_.+f_.*x_]^n_.,x_Symbol] :=
  If[MatchQ[f,f1_.*Complex[0,j_]],
    If[MatchQ[e,e1_.+Pi/2],
      Defer[Int][(c+d*x)^m*Sech[I*(e-Pi/2)+I*f*x]^n,x],
    (-I)^n*Defer[Int][(c+d*x)^m*Csch[-I*e-I*f*x]^n,x]],
  If[MatchQ[e,e1_.+Pi/2],
    Defer[Int][(c+d*x)^m*Sec[e-Pi/2+f*x]^n,x],
  Defer[Int][(c+d*x)^m*Csc[e+f*x]^n,x]]] /;
FreeQ[{c,d,e,f,m,n},x] && IntegerQ[n]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(c+d*x)^m*(a+b*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[u_^m_.*(a_.+b_.*Sec[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Sec[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*(a_.+b_.*Csc[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Csc[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]





(* ::Subsection::Closed:: *)
(*4.3.11 (e x)^m (a+b sec(c+d x^n))^p*)


Int[(a_.+b_.*Sec[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Sec[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && PositiveIntegerQ[1/n] && IntegerQ[p]


Int[(a_.+b_.*Csc[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(1/n-1)*(a+b*Csc[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,p},x] && PositiveIntegerQ[1/n] && IntegerQ[p]


Int[(a_.+b_.*Sec[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][(a+b*Sec[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Csc[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][(a+b*Csc[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_.+b_.*Sec[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Sec[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u-x]


Int[(a_.+b_.*Csc[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Csc[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u-x]


Int[(a_.+b_.*Sec[u_])^p_.,x_Symbol] :=
  Int[(a+b*Sec[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*Csc[u_])^p_.,x_Symbol] :=
  Int[(a+b*Csc[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*(a_.+b_.*Sec[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Sec[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Csc[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Csc[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && PositiveIntegerQ[Simplify[(m+1)/n]] && IntegerQ[p]


Int[x_^m_.*(a_.+b_.*Sec[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*Sec[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[x_^m_.*(a_.+b_.*Csc[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Defer[Int][x^m*(a+b*Csc[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Sec[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sec[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Csc[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Csc[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_*x_)^m_.*(a_.+b_.*Sec[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Sec[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(e_*x_)^m_.*(a_.+b_.*Csc[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Csc[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*Sec[a_.+b_.*x_^n_.]^p_*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
  x^(m-n+1)*Sec[a+b*x^n]^(p-1)/(b*n*(p-1)) -
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Sec[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NeQ[p-1]


Int[x_^m_.*Csc[a_.+b_.*x_^n_.]^p_*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Csc[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  (m-n+1)/(b*n*(p-1))*Int[x^(m-n)*Csc[a+b*x^n]^(p-1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NeQ[p-1]



