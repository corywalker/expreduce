(* ::Package:: *)

(* ::Section:: *)
(*Trig Function Product Integration Rules*)


(* ::Subsection::Closed:: *)
(*4.1.0 (a sin)^m (b trg)^n*)


If[ShowSteps,

Int[u_,x_Symbol] :=
  Int[DeactivateTrig[u,x],x] /;
SimplifyFlag && FunctionOfTrigOfLinearQ[u,x],

Int[u_,x_Symbol] :=
  Int[DeactivateTrig[u,x],x] /;
FunctionOfTrigOfLinearQ[u,x]]


Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  (a*Sin[e+f*x])^(m+1)*(b*Cos[e+f*x])^(n+1)/(a*b*f*(m+1)) /;
FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n+2,0] && NeQ[m,-1]


Int[(a_.*sin[e_.+f_.*x_])^m_.*cos[e_.+f_.*x_]^n_.,x_Symbol] :=
  1/(a*f)*Subst[Int[x^m*(1-x^2/a^2)^((n-1)/2),x],x,a*Sin[e+f*x]] /;
FreeQ[{a,e,f,m},x] && IntegerQ[(n-1)/2] && Not[IntegerQ[(m-1)/2] && 0<m<n]


Int[(a_.*cos[e_.+f_.*x_])^m_.*sin[e_.+f_.*x_]^n_.,x_Symbol] :=
  -1/(a*f)*Subst[Int[x^m*(1-x^2/a^2)^((n-1)/2),x],x,a*Cos[e+f*x]] /;
FreeQ[{a,e,f,m},x] && IntegerQ[(n-1)/2] && Not[IntegerQ[(m-1)/2] && 0<m<=n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*(a*Sin[e+f*x])^(m-1)*(b*Cos[e+f*x])^(n+1)/(b*f*(n+1)) + 
  a^2*(m-1)/(b^2*(n+1))*Int[(a*Sin[e+f*x])^(m-2)*(b*Cos[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f},x] && GtQ[m,1] && LtQ[n,-1] && (IntegersQ[2*m,2*n] || EqQ[m+n,0])


Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a*(a*Cos[e+f*x])^(m-1)*(b*Sin[e+f*x])^(n+1)/(b*f*(n+1)) + 
  a^2*(m-1)/(b^2*(n+1))*Int[(a*Cos[e+f*x])^(m-2)*(b*Sin[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f},x] && GtQ[m,1] && LtQ[n,-1] && (IntegersQ[2*m,2*n] || EqQ[m+n,0])


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*(b*Cos[e+f*x])^(n+1)*(a*Sin[e+f*x])^(m-1)/(b*f*(m+n)) + 
  a^2*(m-1)/(m+n)*Int[(b*Cos[e+f*x])^n*(a*Sin[e+f*x])^(m-2),x] /;
FreeQ[{a,b,e,f,n},x] && GtQ[m,1] && NeQ[m+n,0] && IntegersQ[2*m,2*n]


Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a*(b*Sin[e+f*x])^(n+1)*(a*Cos[e+f*x])^(m-1)/(b*f*(m+n)) + 
  a^2*(m-1)/(m+n)*Int[(b*Sin[e+f*x])^n*(a*Cos[e+f*x])^(m-2),x] /;
FreeQ[{a,b,e,f,n},x] && GtQ[m,1] && NeQ[m+n,0] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*Cos[e+f*x])^(n+1)*(a*Sin[e+f*x])^(m+1)/(a*b*f*(m+1)) + 
  (m+n+2)/(a^2*(m+1))*Int[(b*Cos[e+f*x])^n*(a*Sin[e+f*x])^(m+2),x] /;
FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && IntegersQ[2*m,2*n]


Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b*Sin[e+f*x])^(n+1)*(a*Cos[e+f*x])^(m+1)/(a*b*f*(m+1)) + 
  (m+n+2)/(a^2*(m+1))*Int[(b*Sin[e+f*x])^n*(a*Cos[e+f*x])^(m+2),x] /;
FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && IntegersQ[2*m,2*n]


Int[Sqrt[a_.*sin[e_.+f_.*x_]]*Sqrt[b_.*cos[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[a*Sin[e+f*x]]*Sqrt[b*Cos[e+f*x]]/Sqrt[Sin[2*e+2*f*x]]*Int[Sqrt[Sin[2*e+2*f*x]],x] /;
FreeQ[{a,b,e,f},x]


Int[1/(Sqrt[a_.*sin[e_.+f_.*x_]]*Sqrt[b_.*cos[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[Sin[2*e+2*f*x]]/(Sqrt[a*Sin[e+f*x]]*Sqrt[b*Cos[e+f*x]])*Int[1/Sqrt[Sin[2*e+2*f*x]],x] /;
FreeQ[{a,b,e,f},x]


(* Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Sin[e+f*x])^m*(b*Cos[e+f*x])^n/(a*Tan[e+f*x])^m*Int[(a*Tan[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n,0] *)


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  With[{k=Denominator[m]},
  k*a*b/f*Subst[Int[x^(k*(m+1)-1)/(a^2+b^2*x^(2*k)),x],x,(a*Sin[e+f*x])^(1/k)/(b*Cos[e+f*x])^(1/k)]] /;
FreeQ[{a,b,e,f},x] && EqQ[m+n,0] && GtQ[m,0] && LtQ[m,1]


Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  With[{k=Denominator[m]},
  -k*a*b/f*Subst[Int[x^(k*(m+1)-1)/(a^2+b^2*x^(2*k)),x],x,(a*Cos[e+f*x])^(1/k)/(b*Sin[e+f*x])^(1/k)]] /;
FreeQ[{a,b,e,f},x] && EqQ[m+n,0] && GtQ[m,0] && LtQ[m,1]


(* Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b^(2*IntPart[(n-1)/2]+1)*(b*Cos[e+f*x])^(2*FracPart[(n-1)/2])/(a*f*(Cos[e+f*x]^2)^FracPart[(n-1)/2])*
    Subst[Int[x^m*(1-x^2/a^2)^((n-1)/2),x],x,a*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m,n},x] && (RationalQ[n] || Not[RationalQ[m]] && (EqQ[b-1] || NeQ[a-1])) *)


(* Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^(2*IntPart[(n-1)/2]+1)*(b*Sin[e+f*x])^(2*FracPart[(n-1)/2])/(a*f*(Sin[e+f*x]^2)^FracPart[(n-1)/2])*
    Subst[Int[x^m*(1-x^2/a^2)^((n-1)/2),x],x,a*Cos[e+f*x]] /;
FreeQ[{a,b,e,f,m,n},x] *)


Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^(2*IntPart[(n-1)/2]+1)*(b*Sin[e+f*x])^(2*FracPart[(n-1)/2])*(a*Cos[e+f*x])^(m+1)/(a*f*(m+1)*(Sin[e+f*x]^2)^FracPart[(n-1)/2])*
    Hypergeometric2F1[(1+m)/2,(1-n)/2,(3+m)/2,Cos[e+f*x]^2] /;
FreeQ[{a,b,e,f,m,n},x] && SimplerQ[n,m]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
  b^(2*IntPart[(n-1)/2]+1)*(b*Cos[e+f*x])^(2*FracPart[(n-1)/2])*(a*Sin[e+f*x])^(m+1)/(a*f*(m+1)*(Cos[e+f*x]^2)^FracPart[(n-1)/2])*
    Hypergeometric2F1[(1+m)/2,(1-n)/2,(3+m)/2,Sin[e+f*x]^2] /;
FreeQ[{a,b,e,f,m,n},x]


Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*sec[e_.+f_.*x_])^n_.,x_Symbol] :=
  b*(a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n-1)/(a*f*(m+1)) /;
FreeQ[{a,b,e,f,m,n},x] && EqQ[m-n+2,0] && NeQ[m,1]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  a*b*(a*Sin[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(n-1)) - 
  a^2*b^2*(m-1)/(n-1)*Int[(a*Sin[e+f*x])^(m-2)*(b*Sec[e+f*x])^(n-2),x] /;
FreeQ[{a,b,e,f},x] && GtQ[n,1] && GtQ[m,1] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n+1)/(a*b*f*(m-n)) - 
  (n+1)/(b^2*(m-n))*Int[(a*Sin[e+f*x])^m*(b*Sec[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f,m},x] && GtQ[n,1] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n+1)/(a*b*f*(m+1)) - 
  (n+1)/(a^2*b^2*(m+1))*Int[(a*Sin[e+f*x])^(m+2)*(b*Sec[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f},x] && LtQ[n,-1] && LtQ[m,-1] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n+1)/(a*b*f*(m-n)) - 
  (n+1)/(b^2*(m-n))*Int[(a*Sin[e+f*x])^m*(b*Sec[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f,m},x] && LtQ[n,-1] && NeQ[m-n,0] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*b*(a*Sin[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(m-n)) + 
  a^2*(m-1)/(m-n)*Int[(a*Sin[e+f*x])^(m-2)*(b*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,n},x] && GtQ[m,1] && NeQ[m-n,0] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n-1)/(a*f*(m+1)) + 
  (m-n+2)/(a^2*(m+1))*Int[(a*Sin[e+f*x])^(m+2)*(b*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*Cos[e+f*x])^n*(b*Sec[e+f*x])^n*Int[(a*Sin[e+f*x])^m/(b*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,m,n},x] && IntegerQ[m-1/2] && IntegerQ[n-1/2]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  1/b^2*(b*Cos[e+f*x])^(n+1)*(b*Sec[e+f*x])^(n+1)*Int[(a*Sin[e+f*x])^m/(b*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && LtQ[n,1]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*(b*Cos[e+f*x])^(n-1)*(b*Sec[e+f*x])^(n-1)*Int[(a*Sin[e+f*x])^m/(b*Cos[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]


Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*b)^IntPart[n]*(a*Sin[e+f*x])^FracPart[n]*(b*Csc[e+f*x])^FracPart[n]*Int[(a*Sin[e+f*x])^(m-n),x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]





(* ::Subsection::Closed:: *)
(*4.2.0 (a trg)^m (b tan)^n*)


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
  -b*(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*m) /;
FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n-1]


Int[sin[e_.+f_.*x_]^m_.*tan[e_.+f_.*x_]^n_.,x_Symbol] :=
  -1/f*Subst[Int[(1-x^2)^((m+n-1)/2)/x^n,x],x,Cos[e+f*x]] /;
FreeQ[{e,f},x] && IntegersQ[m,n,(m+n-1)/2]


Int[sin[e_.+f_.*x_]^m_*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  b*ff/f*Subst[Int[(ff*x)^(m+n)/(b^2+ff^2*x^2)^(m/2+1),x],x,b*Tan[e+f*x]/ff]] /;
FreeQ[{b,e,f,n},x] && IntegerQ[m/2]


Int[(a_.*sin[e_.+f_.*x_])^m_.*tan[e_.+f_.*x_]^n_.,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x],x]},
  ff/f*Subst[Int[(ff*x)^(m+n)/(a^2-ff^2*x^2)^((n+1)/2),x],x,a*Sin[e+f*x]/ff]] /;
FreeQ[{a,e,f,m},x] && IntegerQ[(n+1)/2]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a*Sin[e+f*x])^(m+2)*(b*Tan[e+f*x])^(n-1)/(a^2*f*(n-1)) - 
  b^2*(m+2)/(a^2*(n-1))*Int[(a*Sin[e+f*x])^(m+2)*(b*Tan[e+f*x])^(n-2),x] /;
FreeQ[{a,b,e,f},x] && GtQ[n,1] && (LtQ[m,-1] || EqQ[m,-1] && EqQ[n,3/2]) && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*(n-1)) - 
  b^2*(m+n-1)/(n-1)*Int[(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n-2),x] /;
FreeQ[{a,b,e,f,m},x] && GtQ[n,1] && IntegersQ[2*m,2*n] && Not[GtQ[m,1] && Not[IntegerQ[(m-1)/2]]]


Int[Sqrt[a_.*sin[e_.+f_.*x_]]/(b_.*tan[e_.+f_.*x_])^(3/2),x_Symbol]:=
  2*Sqrt[a*Sin[e+f*x]]/(b*f*Sqrt[b*Tan[e+f*x]]) + a^2/b^2*Int[Sqrt[b*Tan[e+f*x]]/(a*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,e,f},x]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*m) - 
  a^2*(n+1)/(b^2*m)*Int[(a*Sin[e+f*x])^(m-2)*(b*Tan[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f},x] && LtQ[n,-1] && GtQ[m,1] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
  (a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*(m+n+1)) - 
  (n+1)/(b^2*(m+n+1))*Int[(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f,m},x] && LtQ[n,-1] && NeQ[m+n+1,0] && IntegersQ[2*m,2*n] && Not[n==-3/2 && EqQ[m,1]]


Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol]:=
  -b*(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*m) + 
  a^2*(m+n-1)/m*Int[(a*Sin[e+f*x])^(m-2)*(b*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,n},x] && (GtQ[m,1] || EqQ[m,1] && EqQ[n,1/2]) && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol]:=
  b*(a*Sin[e+f*x])^(m+2)*(b*Tan[e+f*x])^(n-1)/(a^2*f*(m+n+1)) + 
  (m+2)/(a^2*(m+n+1))*Int[(a*Sin[e+f*x])^(m+2)*(b*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && NeQ[m+n+1,0] && IntegersQ[2*m,2*n]


Int[(a_.*sin[e_.+f_.*x_])^m_*tan[e_.+f_.*x_]^n_,x_Symbol]:=
  1/a^n*Int[(a*Sin[e+f*x])^(m+n)/Cos[e+f*x]^n,x] /;
FreeQ[{a,e,f,m},x] && IntegerQ[n] && Not[IntegerQ[m]]


Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
  Cos[e+f*x]^n*(b*Tan[e+f*x])^n/(a*Sin[e+f*x])^n*Int[(a*Sin[e+f*x])^(m+n)/Cos[e+f*x]^n,x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[n]] && (ILtQ[m,0] || EqQ[m,1] && EqQ[n,-1/2] || IntegersQ[m-1/2,n-1/2])


Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
  a*Cos[e+f*x]^(n+1)*(b*Tan[e+f*x])^(n+1)/(b*(a*Sin[e+f*x])^(n+1))*Int[(a*Sin[e+f*x])^(m+n)/Cos[e+f*x]^n,x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[n]]


Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Cos[e+f*x])^FracPart[m]*(Sec[e+f*x]/a)^FracPart[m]*Int[(b*Tan[e+f*x])^n/(Sec[e+f*x]/a)^m,x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]


Int[(a_.*cot[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Cot[e+f*x])^m*(b*Tan[e+f*x])^m*Int[(b*Tan[e+f*x])^(n-m),x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]


Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol] :=
  -(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*m) /;
FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n+1]


Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol] :=
  a/f*Subst[Int[(a*x)^(m-1)*(-1+x^2)^((n-1)/2),x],x,Sec[e+f*x]] /;
FreeQ[{a,e,f,m},x] && IntegerQ[(n-1)/2] && Not[IntegerQ[m/2] && 0<m<n+1]


Int[sec[e_.+f_.*x_]^m_*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/f*Subst[Int[(b*x)^n*(1+x^2)^(m/2-1),x],x,Tan[e+f*x]] /;
FreeQ[{b,e,f,n},x] && IntegerQ[m/2] && Not[IntegerQ[(n-1)/2] && 0<n<m-1]


Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*(a*Sec[e+f*x])^(m-2)*(b*Tan[e+f*x])^(n+1)/(b*f*(n+1)) - 
  a^2*(m-2)/(b^2*(n+1))*Int[(a*Sec[e+f*x])^(m-2)*(b*Tan[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f},x] && RationalQ[m,n] && n<-1 && (m>1 || m==1 && n==-3/2) && IntegersQ[2*m,2*n]


Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*(n+1)) - 
  (m+n+1)/(b^2*(n+1))*Int[(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f,m},x] && RationalQ[n] && n<-1 && IntegersQ[2*m,2*n]


Int[(a_.*sec[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*m) - 
  b^2*(n-1)/(a^2*m)*Int[(a*Sec[e+f*x])^(m+2)*(b*Tan[e+f*x])^(n-2),x] /;
FreeQ[{a,b,e,f},x] && RationalQ[m,n] && n>1 && (m<-1 || m==-1 && n==3/2) && IntegersQ[2*m,2*n]


Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*(m+n-1)) - 
  b^2*(n-1)/(m+n-1)*Int[(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n-2),x] /;
FreeQ[{a,b,e,f,m},x] && RationalQ[n] && n>1 && NeQ[m+n-1] && IntegersQ[2*m,2*n]


Int[(a_.*sec[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  -(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*m) + 
  (m+n+1)/(a^2*m)*Int[(a*Sec[e+f*x])^(m+2)*(b*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,n},x] && RationalQ[m] && (m<-1 || m==-1 && RationalQ[n] && n==-1/2) && IntegersQ[2*m,2*n]


Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*(a*Sec[e+f*x])^(m-2)*(b*Tan[e+f*x])^(n+1)/(b*f*(m+n-1)) + 
  a^2*(m-2)/(m+n-1)*Int[(a*Sec[e+f*x])^(m-2)*(b*Tan[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,n},x] && RationalQ[m] && (m>1 || m==1 && RationalQ[n] && n==1/2) && NeQ[m+n-1] && IntegersQ[2*m,2*n]


Int[sec[e_.+f_.*x_]/Sqrt[b_.*tan[e_.+f_.*x_]],x_Symbol]:=
  Sqrt[Sin[e+f*x]]/(Sqrt[Cos[e+f*x]]*Sqrt[b*Tan[e+f*x]])*Int[1/(Sqrt[Cos[e+f*x]]*Sqrt[Sin[e+f*x]]),x] /;
FreeQ[{b,e,f},x]


Int[Sqrt[b_.*tan[e_.+f_.*x_]]/sec[e_.+f_.*x_],x_Symbol]:=
  Sqrt[Cos[e+f*x]]*Sqrt[b*Tan[e+f*x]]/Sqrt[Sin[e+f*x]]*Int[Sqrt[Cos[e+f*x]]*Sqrt[Sin[e+f*x]],x] /;
FreeQ[{b,e,f},x]


Int[(a_.*sec[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
  a^(m+n)*(b*Tan[e+f*x])^n/((a*Sec[e+f*x])^n*(b*Sin[e+f*x])^n)*Int[(b*Sin[e+f*x])^n/Cos[e+f*x]^(m+n),x] /;
FreeQ[{a,b,e,f,m,n},x] && IntegerQ[n+1/2] && IntegerQ[m+1/2]


(* Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
  (a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)*(Cos[e+f*x]^2)^((m+n+1)/2)/(b*f*(b*Sin[e+f*x])^(n+1))*
    Subst[Int[x^n/(1-x^2/b^2)^((m+n+1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[(n-1)/2]] && Not[IntegerQ[m/2]] *)


Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
  (a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)*(Cos[e+f*x]^2)^((m+n+1)/2)/(b*f*(n+1))*
    Hypergeometric2F1[(n+1)/2,(m+n+1)/2,(n+3)/2,Sin[e+f*x]^2] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[(n-1)/2]] && Not[IntegerQ[m/2]]


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Csc[e+f*x])^FracPart[m]*(Sin[e+f*x]/a)^FracPart[m]*Int[(b*Tan[e+f*x])^n/(Sin[e+f*x]/a)^m,x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]





(* ::Subsection::Closed:: *)
(*4.3.0 (a csc)^m (b sec)^n*)


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  a*b*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(n-1)) /;
FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n-2] && NeQ[n-1]


Int[csc[e_.+f_.*x_]^m_.*sec[e_.+f_.*x_]^n_.,x_Symbol] :=
  1/f*Subst[Int[(1+x^2)^((m+n)/2-1)/x^m,x],x,Tan[e+f*x]] /;
FreeQ[{e,f},x] && IntegersQ[m,n,(m+n)/2]


Int[(a_.*csc[e_.+f_.*x_])^m_*sec[e_.+f_.*x_]^n_.,x_Symbol] :=
  -1/(f*a^n)*Subst[Int[x^(m+n-1)/(-1+x^2/a^2)^((n+1)/2),x],x,a*Csc[e+f*x]] /;
FreeQ[{a,e,f,m},x] && IntegerQ[(n+1)/2] && Not[IntegerQ[(m+1)/2] && 0<m<n]


Int[(a_.*sec[e_.+f_.*x_])^m_*csc[e_.+f_.*x_]^n_.,x_Symbol] :=
  1/(f*a^n)*Subst[Int[x^(m+n-1)/(-1+x^2/a^2)^((n+1)/2),x],x,a*Sec[e+f*x]] /;
FreeQ[{a,e,f,m},x] && IntegerQ[(n+1)/2] && Not[IntegerQ[(m+1)/2] && 0<m<n]


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n+1)/(f*b*(m-1)) + 
  a^2*(n+1)/(b^2*(m-1))*Int[(a*Csc[e+f*x])^(m-2)*(b*Sec[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f},x] && RationalQ[m,n] && m>1 && n<-1 && IntegersQ[2*m,2*n]


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(a*Csc[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n-1)/(f*a*(n-1)) + 
  b^2*(m+1)/(a^2*(n-1))*Int[(a*Csc[e+f*x])^(m+2)*(b*Sec[e+f*x])^(n-2),x] /;
FreeQ[{a,b,e,f},x] && RationalQ[m,n] && m<-1 && n>1 && IntegersQ[2*m,2*n]


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_.,x_Symbol] :=
  -a*b*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(m-1)) + 
  a^2*(m+n-2)/(m-1)*Int[(a*Csc[e+f*x])^(m-2)*(b*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,n},x] && GtQ[m,1] && IntegersQ[2*m,2*n] && Not[n>m]


Int[(a_.*csc[e_.+f_.*x_])^m_.*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  a*b*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(n-1)) + 
  b^2*(m+n-2)/(n-1)*Int[(a*Csc[e+f*x])^m*(b*Sec[e+f*x])^(n-2),x] /;
FreeQ[{a,b,e,f,m},x] && GtQ[n,1] && IntegersQ[2*m,2*n]


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_.,x_Symbol] :=
  b*(a*Csc[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n-1)/(a*f*(m+n)) + 
  (m+1)/(a^2*(m+n))*Int[(a*Csc[e+f*x])^(m+2)*(b*Sec[e+f*x])^n,x] /;
FreeQ[{a,b,e,f,n},x] && RationalQ[m] && m<-1 && NeQ[m+n] && IntegersQ[2*m,2*n]


Int[(a_.*csc[e_.+f_.*x_])^m_.*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  -a*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n+1)/(b*f*(m+n)) + 
  (n+1)/(b^2*(m+n))*Int[(a*Csc[e+f*x])^m*(b*Sec[e+f*x])^(n+2),x] /;
FreeQ[{a,b,e,f,m},x] && RationalQ[n] && n<-1 && NeQ[m+n] && IntegersQ[2*m,2*n]


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Csc[e+f*x])^m*(b*Sec[e+f*x])^n/Tan[e+f*x]^n*Int[Tan[e+f*x]^n,x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[n]] && EqQ[m+n]


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  (a*Csc[e+f*x])^m*(b*Sec[e+f*x])^n*(a*Sin[e+f*x])^m*(b*Cos[e+f*x])^n*Int[(a*Sin[e+f*x])^(-m)*(b*Cos[e+f*x])^(-n),x] /;
FreeQ[{a,b,e,f,m,n},x] && IntegerQ[m-1/2] && IntegerQ[n-1/2]


Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2/b^2*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n+1)*(a*Sin[e+f*x])^(m-1)*(b*Cos[e+f*x])^(n+1)*
    Int[(a*Sin[e+f*x])^(-m)*(b*Cos[e+f*x])^(-n),x] /;
FreeQ[{a,b,e,f,m,n},x] && Not[SimplerQ[-m,-n]]


Int[(a_.*sec[e_.+f_.*x_])^m_*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2/b^2*(a*Sec[e+f*x])^(m-1)*(b*Csc[e+f*x])^(n+1)*(a*Cos[e+f*x])^(m-1)*(b*Sin[e+f*x])^(n+1)*
    Int[(a*Cos[e+f*x])^(-m)*(b*Sin[e+f*x])^(-n),x] /;
FreeQ[{a,b,e,f,m,n},x]





(* ::Section:: *)
(*Sine Function Integration Rules*)


(* ::Subsection::Closed:: *)
(*4.1.1.1 (a+b sin)^n*)


Int[sin[c_.+d_.*x_]^n_,x_Symbol] :=
  -1/d*Subst[Int[Expand[(1-x^2)^((n-1)/2),x],x],x,Cos[c+d*x]] /;
FreeQ[{c,d},x] && PositiveIntegerQ[(n-1)/2]


Int[(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
(* -Cot[c+d*x]*(c*Sin[c+d*x])^n/(d*n) + b^2*(n-1)/n*Int[(b*Sin[c+d*x])^(n-2),x] *)
  -b*Cos[c+d*x]*(b*Sin[c+d*x])^(n-1)/(d*n) + b^2*(n-1)/n*Int[(b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{b,c,d},x] && IntegerQ[2*n] && n>1


Int[(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Cos[c+d*x]*(b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) + 
  (n+2)/(b^2*(n+1))*Int[(b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{b,c,d},x] && IntegerQ[2*n] && n<-1


Int[sin[c_.+Pi/2+d_.*x_],x_Symbol] :=
  Sin[c+d*x]/d /;
FreeQ[{c,d},x]


Int[sin[c_.+d_.*x_],x_Symbol] :=
  -Cos[c+d*x]/d /;
FreeQ[{c,d},x]


(* Int[1/sin[c_.+d_.*x_],x_Symbol] :=
  Int[Csc[c+d*x],x] /;
FreeQ[{c,d},x] *)


Int[Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  2/d*EllipticE[1/2*(c-Pi/2+d*x),2] /;
FreeQ[{c,d},x]


Int[Sqrt[b_*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[b*Sin[c+d*x]]/Sqrt[Sin[c+d*x]]*Int[Sqrt[Sin[c+d*x]],x] /;
FreeQ[{b,c,d},x]


Int[1/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
  2/d*EllipticF[1/2*(c-Pi/2+d*x),2] /;
FreeQ[{c,d},x]


Int[1/Sqrt[b_*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[Sin[c+d*x]]/Sqrt[b*Sin[c+d*x]]*Int[1/Sqrt[Sin[c+d*x]],x] /;
FreeQ[{b,c,d},x]


(* Int[(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Cos[c+d*x]/(b*d*Sqrt[Cos[c+d*x]^2])*Subst[Int[x^n/Sqrt[1-x^2/b^2],x],x,b*Sin[c+d*x]] /;
FreeQ[{b,c,d,n},x] && Not[IntegerQ[2*n]] *)


Int[(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Cos[c+d*x]*(b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*Sqrt[Cos[c+d*x]^2])*Hypergeometric2F1[1/2,(n+1)/2,(n+3)/2,Sin[c+d*x]^2] /;
FreeQ[{b,c,d,n},x] && Not[IntegerQ[2*n]]


Int[(a_+b_.*sin[c_.+d_.*x_])^2,x_Symbol] :=
  (2*a^2+b^2)*x/2 - 2*a*b*Cos[c+d*x]/d - b^2*Cos[c+d*x]*Sin[c+d*x]/(2*d) /;
FreeQ[{a,b,c,d},x]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(a+b*sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2] && PositiveIntegerQ[n]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2*b*Cos[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]]) /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) +
  a*(2*n-1)/n*Int[(a+b*Sin[c+d*x])^(n-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2] && PositiveIntegerQ[n-1/2]


Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]/(d*(b+a*Sin[c+d*x])) /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  -2/d*Subst[Int[1/(2*a-x^2),x],x,b*Cos[c+d*x]/Sqrt[a+b*Sin[c+d*x]]] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[(a+b*Sin[c+d*x])^(n+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


(* Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a^2*Cos[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]]*Sqrt[a-b*Sin[c+d*x]])*Subst[Int[(a+b*x)^(n-1/2)/Sqrt[a-b*x],x],x,Sin[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[2*n]] *)


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -2^(n+1/2)*a^(n-1/2)*b*Cos[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]])*Hypergeometric2F1[1/2,1/2-n,3/2,1/2*(1-b*Sin[c+d*x]/a)] /;
FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[2*n]] && PositiveQ[a]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a^IntPart[n]*(a+b*Sin[c+d*x])^FracPart[n]/(1+b/a*Sin[c+d*x])^FracPart[n]*Int[(1+b/a*Sin[c+d*x])^n,x] /;
FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[2*n]] && Not[PositiveQ[a]]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  2*Sqrt[a+b]/d*EllipticE[1/2*(c-Pi/2+d*x),2*b/(a+b)] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && PositiveQ[a+b]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  2*Sqrt[a-b]/d*EllipticE[1/2*(c+Pi/2+d*x),-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && PositiveQ[a-b]


Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[a+b*Sin[c+d*x]]/Sqrt[(a+b*Sin[c+d*x])/(a+b)]*Int[Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) + 
  1/n*Int[(a+b*Sin[c+d*x])^(n-2)*Simp[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Sin[c+d*x],x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  With[{q=Rt[a^2-b^2,2]},
  x/q + 2/(d*q)*ArcTan[b*Cos[c+d*x]/(a+q+b*Sin[c+d*x])]] /;
FreeQ[{a,b,c,d},x] && PositiveQ[a^2-b^2] && PosQ[a]


Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  With[{q=Rt[a^2-b^2,2]},
  -x/q - 2/(d*q)*ArcTan[b*Cos[c+d*x]/(a-q+b*Sin[c+d*x])]] /;
FreeQ[{a,b,c,d},x] && PositiveQ[a^2-b^2] && NegQ[a]


Int[1/(a_+b_.*sin[c_.+Pi/2+d_.*x_]),x_Symbol] :=
  With[{e=FreeFactors[Tan[(c+d*x)/2],x]},
  2*e/d*Subst[Int[1/(a+b+(a-b)*e^2*x^2),x],x,Tan[(c+d*x)/2]/e]] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2]


Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  With[{e=FreeFactors[Tan[(c+d*x)/2],x]},
  2*e/d*Subst[Int[1/(a+2*b*e*x+a*e^2*x^2),x],x,Tan[(c+d*x)/2]/e]] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  2/(d*Sqrt[a+b])*EllipticF[1/2*(c-Pi/2+d*x),2*b/(a+b)] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && PositiveQ[a+b]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  2/(d*Sqrt[a-b])*EllipticF[1/2*(c+Pi/2+d*x),-2*b/(a-b)] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && PositiveQ[a-b]


Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[(a+b*Sin[c+d*x])/(a+b)]/Sqrt[a+b*Sin[c+d*x]]*Int[1/Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && Not[PositiveQ[a+b]]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  1/((n+1)*(a^2-b^2))*Int[(a+b*Sin[c+d*x])^(n+1)*Simp[a*(n+1)-b*(n+2)*Sin[c+d*x],x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Cos[c+d*x]/(d*Sqrt[1+Sin[c+d*x]]*Sqrt[1-Sin[c+d*x]])*Subst[Int[(a+b*x)^n/(Sqrt[1+x]*Sqrt[1-x]),x],x,Sin[c+d*x]] /;
FreeQ[{a,b,c,d,n},x] && NeQ[a^2-b^2] && Not[IntegerQ[2*n]]


Int[(a_+b_.*sin[c_.+d_.*x_]*cos[c_.+d_.*x_])^n_,x_Symbol] :=
  Int[(a+b*Sin[2*c+2*d*x]/2)^n,x] /;
FreeQ[{a,b,c,d,n},x]





(* ::Subsection::Closed:: *)
(*4.1.1.2 (g cos)^p (a+b sin)^m*)


Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  1/(b^p*f)*Subst[Int[(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && EqQ[a^2-b^2] && (p>=-1 || Not[IntegerQ[m+1/2] && EqQ[a^2-b^2]])


Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  1/(b^p*f)*Subst[Int[(a+x)^m*(b^2-x^2)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && NeQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)/(f*g*(p+1)) + a*Int[(g*Cos[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g,p},x] && (IntegerQ[2*p] || NeQ[a^2-b^2])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (a/g)^(2*m)*Int[(g*Cos[e+f*x])^(2*m+p)/(a-b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2] && IntegerQ[m] && RationalQ[p] && p<-1 && 2*m+p>=0


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*m) /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && EqQ[Simplify[m+p+1]] && Not[NegativeIntegerQ[p]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*Simplify[2*m+p+1]) + 
  Simplify[m+p+1]/(a*Simplify[2*m+p+1])*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && NegativeIntegerQ[Simplify[m+p+1]] && NeQ[2*m+p+1] && Not[PositiveIntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m-1)) /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && EqQ[2*m+p-1] && NeQ[m-1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) + 
  a*(2*m+p-1)/(m+p)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && PositiveIntegerQ[Simplify[(2*m+p-1)/2]] && NeQ[m+p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(p+1)) + 
  a*(m+p+1)/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2] && RationalQ[m,p] && m>0 && p<=-2*m && IntegersQ[m+1/2,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -2*b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(p+1)) + 
  b^2*(2*m+p-1)/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-2),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2] && RationalQ[m,p] && m>1 && p<-1 && IntegersQ[2*m,2*p]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[g_.*cos[e_.+f_.*x_]],x_Symbol] :=
  a*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x])*Int[Sqrt[1+Cos[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] + 
  b*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x])*Int[Sin[e+f*x]/(Sqrt[g*Cos[e+f*x]]*Sqrt[1+Cos[e+f*x]]),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) + 
  a*(2*m+p-1)/(m+p)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && RationalQ[m] && m>0 && NeQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+p)) + 
  g^2*(p-1)/(a*(m+p))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && (m>-2 || EqQ[2*m+p+1] || m==-2 && IntegerQ[p]) && 
  NeQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  2*g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+p+1)) + 
  g^2*(p-1)/(b^2*(2*m+p+1))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+2),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2] && RationalQ[m,p] && m<=-2 && p>1 && NeQ[2*m+p+1] && Not[NegativeIntegerQ[m+p+1]] && 
  IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(2*m+p+1)) + 
  (m+p+1)/(a*(2*m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1 && NeQ[2*m+p+1] && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)/(b*f*(p-1)) + g^2/a*Int[(g*Cos[e+f*x])^(p-2),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2] && RationalQ[p] && p>1 && IntegerQ[2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)/(a*f*g*(p-1)*(a+b*Sin[e+f*x])) + 
  p/(a*(p-1))*Int[(g*Cos[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2] && Not[RationalQ[p] && p>=1] && IntegerQ[2*p]


Int[Sqrt[g_.*cos[e_.+f_.*x_]]/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  g*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x])*Int[Sqrt[1+Cos[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] - 
  g*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(b+b*Cos[e+f*x]+a*Sin[e+f*x])*Int[Sin[e+f*x]/(Sqrt[g*Cos[e+f*x]]*Sqrt[1+Cos[e+f*x]]),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  g*Sqrt[g*Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(b*f) + 
  g^2/(2*a)*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*b*(g*Cos[e+f*x])^(p+1)/(f*g*(2*p-1)*(a+b*Sin[e+f*x])^(3/2)) + 
  2*a*(p-2)/(2*p-1)*Int[(g*Cos[e+f*x])^p/(a+b*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2] && RationalQ[p] && p>2 && IntegerQ[2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)/(a*f*g*(p+1)*Sqrt[a+b*Sin[e+f*x]]) + 
  a*(2*p+1)/(2*g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)/(a+b*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2] && RationalQ[p] && p<-1 && IntegerQ[2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  a^m*(g*Cos[e+f*x])^(p+1)/(f*g*(1+Sin[e+f*x])^((p+1)/2)*(1-Sin[e+f*x])^((p+1)/2))*
    Subst[Int[(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2] && IntegerQ[m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  a^2*(g*Cos[e+f*x])^(p+1)/(f*g*(a+b*Sin[e+f*x])^((p+1)/2)*(a-b*Sin[e+f*x])^((p+1)/2))*
    Subst[Int[(a+b*x)^(m+(p-1)/2)*(a-b*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*Sin[e+f*x]/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1)*(a*(p+2)+b*(m+p+2)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2] && RationalQ[m,p] && 0<m<1 && p<-1 && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(b+a*Sin[e+f*x])/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-2)*(b^2*(m-1)+a^2*(p+2)+a*b*(m+p+1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2] && RationalQ[m,p] && m>1 && p<-1 && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) + 
  1/(m+p)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-2)*(b^2*(m-1)+a^2*(m+p)+a*b*(2*m+p-1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2] && RationalQ[m] && m>1 && NeQ[m+p] && (IntegersQ[2*m,2*p] || IntegerQ[m])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)) + 
  g^2*(p-1)/(b*(m+1))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1)*Sin[e+f*x],x] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a^2-b^2)*(m+1)) + 
  1/((a^2-b^2)*(m+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(a*(m+1)-b*(m+p+2)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+p)) + 
  g^2*(p-1)/(b*(m+p))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^m*(b+a*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m},x] && NeQ[a^2-b^2] && RationalQ[p] && p>1 && NeQ[m+p] && IntegersQ[2*m,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)*(b-a*Sin[e+f*x])/(f*g*(a^2-b^2)*(p+1)) + 
  1/(g^2*(a^2-b^2)*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m*(a^2*(p+2)-b^2*(m+p+2)+a*b*(m+p+3)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m},x] && NeQ[a^2-b^2] && RationalQ[p] && p<-1 && IntegersQ[2*m,2*p]


Int[1/(Sqrt[g_.*cos[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2*Sqrt[2]*Sqrt[g*Cos[e+f*x]]*Sqrt[(a+b*Sin[e+f*x])/((a-b)*(1-Sin[e+f*x]))]/
   (f*g*Sqrt[a+b*Sin[e+f*x]]*Sqrt[(1+Cos[e+f*x]+Sin[e+f*x])/(1+Cos[e+f*x]-Sin[e+f*x])])*
   Subst[Int[1/Sqrt[1+(a+b)*x^4/(a-b)],x],x,Sqrt[(1+Cos[e+f*x]+Sin[e+f*x])/(1+Cos[e+f*x]-Sin[e+f*x])]] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(1-Sin[e+f*x])*(a+b*Sin[e+f*x])^(m+1)*(-(a-b)*(1-Sin[e+f*x])/((a+b)*(1+Sin[e+f*x])))^(m/2)/
    (f*(a+b)*(m+1))*
    Hypergeometric2F1[m+1,m/2+1,m+2,2*(a+b*Sin[e+f*x])/((a+b)*(1+Sin[e+f*x]))] /;
FreeQ[{a,b,e,f,g,m,p},x] && NeQ[a^2-b^2] && EqQ[m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a-b)*(p+1)) + 
  a/(g^2*(a-b))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m/(1-Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && NeQ[a^2-b^2] && EqQ[m+p+2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a-b)*(p+1)) - 
  b*(m+p+2)/(g^2*(a-b)*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m,x] + 
  a/(g^2*(a-b))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m/(1-Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && NeQ[a^2-b^2] && NegativeIntegerQ[m+p+2]


Int[Sqrt[g_.*cos[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  With[{q=Rt[-a^2+b^2,2]},
  a*g/(2*b)*Int[1/(Sqrt[g*Cos[e+f*x]]*(q+b*Cos[e+f*x])),x] - 
  a*g/(2*b)*Int[1/(Sqrt[g*Cos[e+f*x]]*(q-b*Cos[e+f*x])),x] + 
  b*g/f*Subst[Int[Sqrt[x]/(g^2*(a^2-b^2)+b^2*x^2),x],x,g*Cos[e+f*x]]] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2]


Int[1/(Sqrt[g_.*cos[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
  With[{q=Rt[-a^2+b^2,2]},
  -a/(2*q)*Int[1/(Sqrt[g*Cos[e+f*x]]*(q+b*Cos[e+f*x])),x] - 
  a/(2*q)*Int[1/(Sqrt[g*Cos[e+f*x]]*(q-b*Cos[e+f*x])),x] + 
  b*g/f*Subst[Int[1/(Sqrt[x]*(g^2*(a^2-b^2)+b^2*x^2)),x],x,g*Cos[e+f*x]]] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/
    (b*f*(m+p)*(-b*(1-Sin[e+f*x])/(a+b*Sin[e+f*x]))^((p-1)/2)*(b*(1+Sin[e+f*x])/(a+b*Sin[e+f*x]))^((p-1)/2))*
  AppellF1[-p-m,(1-p)/2,(1-p)/2,1-p-m,(a+b)/(a+b*Sin[e+f*x]),(a-b)/(a+b*Sin[e+f*x])] /;
FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2] && NegativeIntegerQ[m] && Not[PositiveIntegerQ[m+p+1]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)/(f*(1-(a+b*Sin[e+f*x])/(a-b))^((p-1)/2)*(1-(a+b*Sin[e+f*x])/(a+b))^((p-1)/2))*
    Subst[Int[(-b/(a-b)-b*x/(a-b))^((p-1)/2)*(b/(a+b)-b*x/(a+b))^((p-1)/2)*(a+b*x)^m,x],x,Sin[e+f*x]] /;
FreeQ[{a,b,e,f,g,m,p},x] && NeQ[a^2-b^2] && Not[PositiveIntegerQ[m]]


Int[(g_.*sec[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  g^(2*IntPart[p])*(g*Cos[e+f*x])^FracPart[p]*(g*Sec[e+f*x])^FracPart[p]*Int[(a+b*Sin[e+f*x])^m/(g*Cos[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g,m,p},x] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*4.1.1.3 (g tan)^p (a+b sin)^m*)


Int[(g_.*tan[e_.+f_.*x_])^p_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  1/a*Int[Sec[e+f*x]^2*(g*Tan[e+f*x])^p,x] - 1/(b*g)*Int[Sec[e+f*x]*(g*Tan[e+f*x])^(p+1),x] /;
FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2] && NeQ[p+1]


Int[tan[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  1/f*Subst[Int[x^p*(a+x)^(m-(p+1)/2)/(a-x)^((p+1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && IntegerQ[(p+1)/2]


Int[tan[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  a^p*Int[Sin[e+f*x]^p/(a-b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && IntegersQ[m,p] && p==2*m


Int[tan[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  a^p*Int[ExpandIntegrand[Sin[e+f*x]^p*(a+b*Sin[e+f*x])^(m-p/2)/(a-b*Sin[e+f*x])^(p/2),x],x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && IntegersQ[m,p/2] && (p<0 || m-p/2>0)


Int[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  Int[ExpandIntegrand[(g*Tan[e+f*x])^p,(a+b*Sin[e+f*x])^m,x],x] /;
FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  a^(2*m)*Int[ExpandIntegrand[(g*Tan[e+f*x])^p*Sec[e+f*x]^(-m),(a*Sec[e+f*x]-b*Tan[e+f*x])^(-m),x],x] /;
FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2] && NegativeIntegerQ[m]


Int[tan[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(a+b*Sin[e+f*x])^m/(a*f*(2*m-1)*Cos[e+f*x]) - 
  1/(a^2*(2*m-1))*Int[(a+b*Sin[e+f*x])^(m+1)*(a*m-b*(2*m-1)*Sin[e+f*x])/Cos[e+f*x]^2,x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && RationalQ[m] && m<0


Int[tan[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -(a+b*Sin[e+f*x])^(m+1)/(b*f*m*Cos[e+f*x]) + 
  1/(b*m)*Int[(a+b*Sin[e+f*x])^m*(b*(m+1)+a*Sin[e+f*x])/Cos[e+f*x]^2,x] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && Not[RationalQ[m] && m<0]


Int[tan[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Int[(a+b*Sin[e+f*x])^m,x] - Int[(a+b*Sin[e+f*x])^m*(1-2*Sin[e+f*x]^2)/Cos[e+f*x]^4,x] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && IntegerQ[m-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^2,x_Symbol] :=
  -(a+b*Sin[e+f*x])^(m+1)/(a*f*Tan[e+f*x]) + 
  1/b^2*Int[(a+b*Sin[e+f*x])^(m+1)*(b*m-a*(m+1)*Sin[e+f*x])/Sin[e+f*x],x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && IntegerQ[m-1/2] && m<-1


Int[(a_+b_.*sin[e_.+f_.*x_])^m_./tan[e_.+f_.*x_]^2,x_Symbol] :=
  -(a+b*Sin[e+f*x])^m/(f*Tan[e+f*x]) + 
  1/a*Int[(a+b*Sin[e+f*x])^m*(b*m-a*(m+1)*Sin[e+f*x])/Sin[e+f*x],x] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && IntegerQ[m-1/2] && Not[m<-1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
  -2/(a*b)*Int[(a+b*Sin[e+f*x])^(m+2)/Sin[e+f*x]^3,x] + 
  1/a^2*Int[(a+b*Sin[e+f*x])^(m+2)*(1+Sin[e+f*x]^2)/Sin[e+f*x]^4,x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && IntegerQ[m-1/2] && m<-1


Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
  Int[(a+b*Sin[e+f*x])^m,x] + Int[(a+b*Sin[e+f*x])^m*(1-2*Sin[e+f*x]^2)/Sin[e+f*x]^4,x] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && IntegerQ[m-1/2] && Not[m<-1]


Int[tan[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]]/(b*f*Cos[e+f*x])*
    Subst[Int[x^p*(a+x)^(m-(p+1)/2)/(a-x)^((p+1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && IntegerQ[p/2]


Int[(g_.*tan[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (g*Tan[e+f*x])^(p+1)*(a-b*Sin[e+f*x])^((p+1)/2)*(a+b*Sin[e+f*x])^((p+1)/2)/(f*g*(b*Sin[e+f*x])^(p+1))*
    Subst[Int[x^p*(a+x)^(m-(p+1)/2)/(a-x)^((p+1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && Not[IntegerQ[p]]


Int[tan[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  1/f*Subst[Int[(x^p*(a+x)^m)/(b^2-x^2)^((p+1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2] && IntegerQ[(p+1)/2]


Int[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  Int[ExpandIntegrand[(g*Tan[e+f*x])^p,(a+b*Sin[e+f*x])^m,x],x] /;
FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^2,x_Symbol] :=
  Int[(a+b*Sin[e+f*x])^m*(1-Sin[e+f*x]^2)/Sin[e+f*x]^2,x] /;
FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
  -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(3*a*f*Sin[e+f*x]^3) - 
  (3*a^2+b^2*(m-2))*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(3*a^2*b*f*(m+1)*Sin[e+f*x]^2) - 
  1/(3*a^2*b*(m+1))*Int[(a+b*Sin[e+f*x])^(m+1)/Sin[e+f*x]^3*
    Simp[6*a^2-b^2*(m-1)*(m-2)+a*b*(m+1)*Sin[e+f*x]-(3*a^2-b^2*m*(m-2))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


(* Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
  -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(3*a*f*Sin[e+f*x]^3) - 
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*m*Sin[e+f*x]^2) - 
  1/(3*a*b*m)*Int[(a+b*Sin[e+f*x])^m/Sin[e+f*x]^3*
    Simp[6*a^2-b^2*m*(m-2)+a*b*(m+3)*Sin[e+f*x]-(3*a^2-b^2*m*(m-1))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && IntegerQ[2*m] *)


Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
  -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(3*a*f*Sin[e+f*x]^3) - 
  b*(m-2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(6*a^2*f*Sin[e+f*x]^2) - 
  1/(6*a^2)*Int[(a+b*Sin[e+f*x])^m/Sin[e+f*x]^2*
    Simp[8*a^2-b^2*(m-1)*(m-2)+a*b*m*Sin[e+f*x]-(6*a^2-b^2*m*(m-2))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2] && Not[RationalQ[m] && m<-1] && IntegerQ[2*m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^6,x_Symbol] :=
  -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(5*a*f*Sin[e+f*x]^5) - 
  b*(m-4)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(20*a^2*f*Sin[e+f*x]^4) + 
  a*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*m*(m-1)*Sin[e+f*x]^3) + 
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*m*Sin[e+f*x]^2) + 
  1/(20*a^2*b^2*m*(m-1))*Int[(a+b*Sin[e+f*x])^m/Sin[e+f*x]^4*
    Simp[60*a^4-44*a^2*b^2*(m-1)*m+b^4*m*(m-1)*(m-3)*(m-4)+a*b*m*(20*a^2-b^2*m*(m-1))*Sin[e+f*x]-
      (40*a^4+b^4*m*(m-1)*(m-2)*(m-4)-20*a^2*b^2*(m-1)*(2*m+1))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2] && NeQ[m-1] && IntegerQ[2*m]


Int[(g_.*tan[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a/(a^2-b^2)*Int[(g*Tan[e+f*x])^p/Sin[e+f*x]^2,x] - 
  b*g/(a^2-b^2)*Int[(g*Tan[e+f*x])^(p-1)/Cos[e+f*x],x] - 
  a^2*g^2/(a^2-b^2)*Int[(g*Tan[e+f*x])^(p-2)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*p] && p>1


Int[(g_.*tan[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  1/a*Int[(g*Tan[e+f*x])^p/Cos[e+f*x]^2,x] - 
  b/(a^2*g)*Int[(g*Tan[e+f*x])^(p+1)/Cos[e+f*x],x] - 
  (a^2-b^2)/(a^2*g^2)*Int[(g*Tan[e+f*x])^(p+2)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*p] && p<-1


Int[Sqrt[g_.*tan[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  Sqrt[Cos[e+f*x]]*Sqrt[g*Tan[e+f*x]]/Sqrt[Sin[e+f*x]]*Int[Sqrt[Sin[e+f*x]]/(Sqrt[Cos[e+f*x]]*(a+b*Sin[e+f*x])),x] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2]


Int[1/(Sqrt[g_*tan[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
  Sqrt[Sin[e+f*x]]/(Sqrt[Cos[e+f*x]]*Sqrt[g*Tan[e+f*x]])*Int[Sqrt[Cos[e+f*x]]/(Sqrt[Sin[e+f*x]]*(a+b*Sin[e+f*x])),x] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2]


Int[tan[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Int[ExpandIntegrand[Sin[e+f*x]^p*(a+b*Sin[e+f*x])^m/(1-Sin[e+f*x]^2)^(p/2),x],x] /;
FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2] && IntegersQ[m,p/2]


Int[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  Defer[Int][(g*Tan[e+f*x])^p*(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,g,m,p},x]


Int[(g_.*cot[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
  g^(2*IntPart[p])*(g*Cot[e+f*x])^FracPart[p]*(g*Tan[e+f*x])^FracPart[p]*Int[(a+b*Sin[e+f*x])^m/(g*Tan[e+f*x])^p,x] /;
FreeQ[{a,b,e,f,g,m,p},x] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*4.1.2.1 (a+b sin)^m (c+d sin)^n*)


Int[(a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (2*a*c+b*d)*x/2 - (b*c+a*d)*Cos[e+f*x]/f - b*d*Cos[e+f*x]*Sin[e+f*x]/(2*f) /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d]


Int[(a_.+b_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b*x/d - (b*c-a*d)/d*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^m*c^m*Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m] && Not[IntegerQ[n] && (m<0 && n>0 || 0<n<m || m<n<0)]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  a*c*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])*Int[Cos[e+f*x]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Sin[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && NeQ[n+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(2*n+1)) - 
  b*(2*m-1)/(d*(2*n+1))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[m-1/2] && RationalQ[n] && n<-1 && 
  Not[NegativeIntegerQ[m+n] && 2*m+n+1>0]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(m+n)) + 
  a*(2*m-1)/(m+n)*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[m-1/2] && Not[RationalQ[n] && n<-1] && 
  Not[PositiveIntegerQ[n-1/2] && n<m] && Not[NegativeIntegerQ[m+n] && 2*m+n+1>0]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])*Int[1/Cos[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && EqQ[m+n+1] && NeQ[m+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && NegativeIntegerQ[Simplify[m+n+1]] && NeQ[m+1/2] && 
  (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) + 
  (m+n+1)/(a*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && RationalQ[m] && m<-1 && 
  Not[RationalQ[n] && m<n<-1] && IntegersQ[2*m,2*n]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/Cos[e+f*x]^(2*FracPart[m])*
    Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && (FractionQ[m] || Not[FractionQ[n]])


Int[(a_.+b_.*sin[e_.+f_.*x_])^2/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b^2*Cos[e+f*x]/(d*f) + 1/d*Int[Simp[a^2*d-b*(b*c-2*a*d)*Sin[e+f*x],x]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*Sin[e+f*x]),x] - d/(b*c-a*d)*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d]


Int[(b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  c*Int[(b*Sin[e+f*x])^m,x] + d/b*Int[(b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{b,c,d,e,f,m},x]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && EqQ[a*d*m+b*c*(m+1)]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) + 
  (a*d*m+b*c*(m+1))/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) + 
  (a*d*m+b*c*(m+1))/(b*(m+1))*Int[(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(c_.+d_.*sin[e_.+f_.*x_])/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  (b*c-a*d)/b*Int[1/Sqrt[a+b*Sin[e+f*x]],x] + d/b*Int[Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(f*(m+1)) + 
  1/(m+1)*Int[(a+b*Sin[e+f*x])^(m-1)*Simp[b*d*m+a*c*(m+1)+(a*d*m+b*c*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[2*m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[(a*c-b*d)*(m+1)-(b*c-a*d)*(m+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  c*Cos[e+f*x]/(f*Sqrt[1+Sin[e+f*x]]*Sqrt[1-Sin[e+f*x]])*Subst[Int[(a+b*x)^m*Sqrt[1+d/c*x]/Sqrt[1-d/c*x],x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && Not[IntegerQ[2*m]] && EqQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)/b*Int[(a+b*Sin[e+f*x])^m,x] + d/b*Int[(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(a+b*sin[e+f*x])^m*(d*sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2] && PositiveIntegerQ[m] && RationalQ[n]


Int[sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) - 
  1/(a^2*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(a*m-b*(2*m+1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1/2


Int[sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*(b*(m+1)-a*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*c*d*(m-1)+b*(d^2+c^2*(m+1))+d*(a*d*(m-1)+b*c*(m+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  -d^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[b*(d^2*(m+1)+c^2*(m+2))-d*(a*d-2*b*c*(m+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)) + 
  b^2/(d*(n+1)*(b*c+a*d))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[a*c*(m-2)-b*d*(m-2*n-4)-(b*c*(m-1)-a*d*(m+2*n+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m>1 && n<-1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m+1/2] || IntegerQ[m] && EqQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^n*
    Simp[a*b*c*(m-2)+b^2*d*(n+1)+a^2*d*(m+n)-b*(b*c*(m-1)-a*d*(3*m+2*n-2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m>1 && 
  Not[RationalQ[n] && n<-1] && (IntegersQ[2*m,2*n] || IntegerQ[m+1/2] || IntegerQ[m] && EqQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*Simp[a*d*n-b*c*(m+1)-b*d*(m+n+1)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 0<n<1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m] && EqQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)/(a*f*(2*m+1)) + 
  1/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-2)*
    Simp[b*(c^2*(m+1)+d^2*(n-1))+a*c*d*(m-n+1)+d*(a*d*(m-n+1)+b*c*(m+n))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m<-1 && n>1 && 
  (IntegersQ[2*m,2*n] || IntegerQ[m] && EqQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(a*f*(2*m+1)*(b*c-a*d)) + 
  1/(a*(2*m+1)*(b*c-a*d))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[b*c*(m+1)-a*d*(2*m+n+2)+b*d*(m+n+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  Not[RationalQ[n] && n>0] && (IntegersQ[2*m,2*n] || IntegerQ[m] && EqQ[c])


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n-1)/(a*f*(a+b*Sin[e+f*x])) - 
  d/(a*b)*Int[(c+d*Sin[e+f*x])^(n-2)*Simp[b*d*(n-1)-a*c*n+(b*c*(n-1)-a*d*n)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n>1 && 
  (IntegerQ[2*n] || EqQ[c])


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b^2*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(a*f*(b*c-a*d)*(a+b*Sin[e+f*x])) + 
  d/(a*(b*c-a*d))*Int[(c+d*Sin[e+f*x])^n*(a*n-b*(n+1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n<0 && (IntegerQ[2*n] || EqQ[c])


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(a*f*(a+b*Sin[e+f*x])) + 
  d*n/(a*b)*Int[(c+d*Sin[e+f*x])^(n-1)*(a-b*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && (IntegerQ[2*n] || EqQ[c])


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*Cos[e+f*x]*(c+d*Sin[e+f*x])^n/(f*(2*n+1)*Sqrt[a+b*Sin[e+f*x]]) + 
  2*n*(b*c+a*d)/(b*(2*n+1))*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n>0 && IntegerQ[2*n]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_.+d_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  -2*b^2*Cos[e+f*x]/(f*(b*c+a*d)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (b*c-a*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)*Sqrt[a+b*Sin[e+f*x]]) + 
  (2*n+3)*(b*c-a*d)/(2*b*(n+1)*(c^2-d^2))*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n<-1 && NeQ[2*n+3] && IntegerQ[2*n]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*b/f*Subst[Int[1/(b*c+a*d-d*x^2),x],x,b*Cos[e+f*x]/Sqrt[a+b*Sin[e+f*x]]] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2/f*Subst[Int[1/Sqrt[1-x^2/a],x],x,b*Cos[e+f*x]/Sqrt[a+b*Sin[e+f*x]]] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && EqQ[d-a/b]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*b/f*Subst[Int[1/(b+d*x^2),x],x,b*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^2*Cos[e+f*x]/(f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]])*Subst[Int[(c+d*x)^n/Sqrt[a-b*x],x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && Not[IntegerQ[2*n]]


Int[Sqrt[c_.+d_.*sin[e_.+f_.*x_]]/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  d/b*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  (b*c-a*d)/b*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*d*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n-1)/(f*(2*n-1)*Sqrt[a+b*Sin[e+f*x]]) - 
  1/(b*(2*n-1))*Int[(c+d*Sin[e+f*x])^(n-2)/Sqrt[a+b*Sin[e+f*x]]*
    Simp[a*c*d-b*(2*d^2*(n-1)+c^2*(2*n-1))+d*(a*d-b*c*(4*n-3))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n>1 && IntegerQ[2*n]


Int[(c_.+d_.*sin[e_.+f_.*x_])^n_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -d*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)*Sqrt[a+b*Sin[e+f*x]]) - 
  1/(2*b*(n+1)*(c^2-d^2))*Int[(c+d*Sin[e+f*x])^(n+1)*Simp[a*d-2*b*c*(n+1)+b*d*(2*n+3)*Sin[e+f*x],x]/Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n<-1 && IntegerQ[2*n]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/Sqrt[a+b*Sin[e+f*x]],x] - d/(b*c-a*d)*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -Sqrt[2]/(Sqrt[a]*f)*Subst[Int[1/Sqrt[1-x^2],x],x,b*Cos[e+f*x]/(a+b*Sin[e+f*x])] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && EqQ[d-a/b] && PositiveQ[a]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*a/f*Subst[Int[1/(2*b^2-(a*c-b*d)*x^2),x],x,b*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -d*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)/(f*(m+n)) + 
  1/(b*(m+n))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-2)*
    Simp[d*(a*c*m+b*d*(n-1))+b*c^2*(m+n)+d*(a*d*m+b*c*(m+2*n-1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n>1 && IntegerQ[n]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^m*Cos[e+f*x]/(f*Sqrt[1+Sin[e+f*x]]*Sqrt[1-Sin[e+f*x]])*Subst[Int[(1+b/a*x)^(m-1/2)*(c+d*x)^n/Sqrt[1-b/a*x],x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && IntegerQ[m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(d/b)^n*Cos[e+f*x]/(f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]])*
    Subst[Int[(a-x)^n*(2*a-x)^(m-1/2)/Sqrt[x],x],x,a-b*Sin[e+f*x]] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && PositiveQ[a] && PositiveQ[d/b]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  (d/b)^IntPart[n]*(d*Sin[e+f*x])^FracPart[n]/(b*Sin[e+f*x])^FracPart[n]*Int[(a+b*Sin[e+f*x])^m*(b*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && PositiveQ[a] && Not[PositiveQ[d/b]]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]/(1+b/a*Sin[e+f*x])^FracPart[m]*
    Int[(1+b/a*Sin[e+f*x])^m*(d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]] && Not[PositiveQ[a]]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^2*Cos[e+f*x]/(f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]])*Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^n/Sqrt[a-b*x],x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && Not[IntegerQ[m]]


Int[(b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  2*c*d/b*Int[(b*Sin[e+f*x])^(m+1),x] + Int[(b*Sin[e+f*x])^m*(c^2+d^2*Sin[e+f*x]^2),x] /;
FreeQ[{b,c,d,e,f,m},x]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  -(b^2*c^2-2*a*b*c*d+a^2*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) - 
  1/(b*(m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*
    Simp[b*(m+1)*(2*b*c*d-a*(c^2+d^2))+(a^2*d^2-2*a*b*c*d*(m+2)+b^2*(d^2*(m+1)+c^2*(m+2)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  -d^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[b*(d^2*(m+1)+c^2*(m+2))-d*(a*d-2*b*c*(m+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


(* Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[(a+b*sin[e+f*x])^m*(d*sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m] *)


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b^2*c^2-2*a*b*c*d+a^2*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^(m-3)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[b*(m-2)*(b*c-a*d)^2+a*d*(n+1)*(c*(a^2+b^2)-2*a*b*d)+
      (b*(n+1)*(a*b*c^2+c*d*(a^2+b^2)-3*a*b*d^2)-a*(n+2)*(b*c-a*d)^2)*Sin[e+f*x]+
      b*(b^2*(c^2-d^2)-m*(b*c-a*d)^2+d*n*(2*a*b*c-d*(a^2+b^2)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m>2 && n<-1 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Sin[e+f*x])^(m-3)*(c+d*Sin[e+f*x])^n*
    Simp[a^3*d*(m+n)+b^2*(b*c*(m-2)+a*d*(n+1))-
      b*(a*b*c-b^2*d*(m+n-1)-3*a^2*d*(m+n))*Sin[e+f*x]-
      b^2*(b*c*(m-1)-a*d*(3*m+2*n-2))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m>2 && 
  (IntegerQ[m] || IntegersQ[2*m,2*n]) && Not[IntegerQ[n] && n>2 && (Not[IntegerQ[m]] || EqQ[a] && NeQ[c])]


Int[Sqrt[d_.*sin[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  -2*a*d*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) - 
  d^2/(a^2-b^2)*Int[Sqrt[a+b*Sin[e+f*x]]/(d*Sin[e+f*x])^(3/2),x] /; 
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[Sqrt[c_+d_.*sin[e_.+f_.*x_]]/(a_.+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  (c-d)/(a-b)*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] - 
  (b*c-a*d)/(a-b)*Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /; 
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[a*c*(m+1)+b*d*n+(a*d*(m+1)-b*c*(m+2))*Sin[e+f*x]-b*d*(m+n+2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 0<n<1 && 
  IntegersQ[2*m,2*n]


Int[(d_.*sin[e_.+f_.*x_])^(3/2)/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  d/b*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] - 
  a*d/b*Int[Sqrt[d*Sin[e+f*x]]/(a+b*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(c_+d_.*sin[e_.+f_.*x_])^(3/2)/(a_.+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  d^2/b^2*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  (b*c-a*d)/b^2*Int[Simp[b*c+a*d+2*b*d*Sin[e+f*x],x]/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-2)*
    Simp[c*(a*c-b*d)*(m+1)+d*(b*c-a*d)*(n-1)+(d*(a*c-b*d)*(m+1)-c*(b*c-a*d)*(m+2))*Sin[e+f*x]-d*(b*c-a*d)*(m+n+1)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m<-1 && 1<n<2 && 
  IntegersQ[2*m,2*n]


Int[1/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2*b*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) + 
  d/(a^2-b^2)*Int[(b+a*Sin[e+f*x])/(Sqrt[a+b*Sin[e+f*x]]*(d*Sin[e+f*x])^(3/2)),x] /; 
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  1/(a-b)*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] - 
  b/(a-b)*Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b^2*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[a*(b*c-a*d)*(m+1)+b^2*d*(m+n+2)-(b^2*c+b*(b*c-a*d)*(m+1))*Sin[e+f*x]-b^2*d*(m+n+3)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  IntegersQ[2*m,2*n] && 
  (EqQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || EqQ[a])])


Int[Sqrt[c_.+d_.*sin[e_.+f_.*x_]]/(a_.+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[1/Sqrt[c+d*Sin[e+f*x]],x] + 
  (b*c-a*d)/b*Int[1/((a+b*Sin[e+f*x])*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^(3/2)/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b/d*Int[Sqrt[a+b*Sin[e+f*x]],x] - (b*c-a*d)/d*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2/(f*(a+b)*Sqrt[c+d])*EllipticPi[2*b/(a+b),1/2*(e-Pi/2+f*x),2*d/(c+d)] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && PositiveQ[c+d]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2/(f*(a-b)*Sqrt[c-d])*EllipticPi[-2*b/(a-b),1/2*(e+Pi/2+f*x),-2*d/(c-d)] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && PositiveQ[c-d]


Int[1/((a_.+b_.*sin[e_.+f_.*x_])*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[(c+d*Sin[e+f*x])/(c+d)]/Sqrt[c+d*Sin[e+f*x]]*Int[1/((a+b*Sin[e+f*x])*Sqrt[c/(c+d)+d/(c+d)*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && Not[PositiveQ[c+d]]


Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  2*c*Rt[b*(c+d),2]*Tan[e+f*x]*Sqrt[1+Csc[e+f*x]]*Sqrt[1-Csc[e+f*x]]/(d*f*Sqrt[c^2-d^2])*
    EllipticPi[(c+d)/d,ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f},x] && PositiveQ[c^2-d^2] && PosQ[(c+d)/b] && PositiveQ[c^2]


Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  2*b*Tan[e+f*x]/(d*f)*Rt[(c+d)/b,2]*Sqrt[c*(1+Csc[e+f*x])/(c-d)]*Sqrt[c*(1-Csc[e+f*x])/(c+d)]*
    EllipticPi[(c+d)/d,ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f},x] && NeQ[c^2-d^2] && PosQ[(c+d)/b]


Int[Sqrt[b_.*sin[e_.+f_.*x_]]/Sqrt[c_+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[b*Sin[e+f*x]]/Sqrt[-b*Sin[e+f*x]]*Int[Sqrt[-b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] /;
FreeQ[{b,c,d,e,f},x] && NeQ[c^2-d^2] && NegQ[(c+d)/b]


(* Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  a*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]),x] + 
  b/d*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] *)


(* Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  2*(a+b*Sin[e+f*x])/(d*f*Rt[(a+b)/d,2]*Cos[e+f*x])*Sqrt[a*(1-Sin[e+f*x])/(a+b*Sin[e+f*x])]*Sqrt[a*(1+Sin[e+f*x])/(a+b*Sin[e+f*x])]*
    EllipticPi[b/(a+b),ArcSin[Rt[(a+b)/d,2]*(Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]])],-(a-b)/(a+b)] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && PosQ[(a+b)/d] *)


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  2*(a+b*Sin[e+f*x])/(d*f*Rt[(a+b)/(c+d),2]*Cos[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Sin[e+f*x])/((c-d)*(a+b*Sin[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Sin[e+f*x])/((c+d)*(a+b*Sin[e+f*x]))]*
    EllipticPi[b*(c+d)/(d*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && PosQ[(a+b)/(c+d)]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  Sqrt[-c-d*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]]*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[-c-d*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && NegQ[(a+b)/(c+d)]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*d/(f*Sqrt[a+b*d])*EllipticF[ArcSin[Cos[e+f*x]/(1+d*Sin[e+f*x])],-(a-b*d)/(a+b*d)] /;
FreeQ[{a,b,d,e,f},x] && NegativeQ[a^2-b^2] && EqQ[d^2-1] && PositiveQ[b*d]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[Sign[b]*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[Sign[b]*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f},x] && NegativeQ[a^2-b^2] && PositiveQ[b^2] && Not[EqQ[d^2-1] && PositiveQ[b*d]]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*Sqrt[a^2]*Sqrt[-Cot[e+f*x]^2]/(a*f*Sqrt[a^2-b^2]*Cot[e+f*x])*Rt[(a+b)/d,2]*
    EllipticF[ArcSin[Sqrt[a+b*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]/Rt[(a+b)/d,2]],-(a+b)/(a-b)] /;
FreeQ[{a,b,d,e,f},x] && PositiveQ[a^2-b^2] && PosQ[(a+b)/d] && PositiveQ[a^2]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*Tan[e+f*x]/(a*f)*Rt[(a+b)/d,2]*Sqrt[a*(1-Csc[e+f*x])/(a+b)]*Sqrt[a*(1+Csc[e+f*x])/(a-b)]*
    EllipticF[ArcSin[Sqrt[a+b*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]/Rt[(a+b)/d,2]],-(a+b)/(a-b)] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && PosQ[(a+b)/d]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-d*Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[-d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && NegQ[(a+b)/d]


Int[1/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2*(c+d*Sin[e+f*x])/(f*(b*c-a*d)*Rt[(c+d)/(a+b),2]*Cos[e+f*x])*
    Sqrt[(b*c-a*d)*(1-Sin[e+f*x])/((a+b)*(c+d*Sin[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1+Sin[e+f*x])/((a-b)*(c+d*Sin[e+f*x]))]*
    EllipticF[ArcSin[Rt[(c+d)/(a+b),2]*(Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]])],(a+b)*(c-d)/((a-b)*(c+d))] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && PosQ[(c+d)/(a+b)]


Int[1/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-a-b*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]*Int[1/(Sqrt[-a-b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && NegQ[(c+d)/(a+b)]


Int[(d_.*sin[e_.+f_.*x_])^(3/2)/Sqrt[a_.+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -a*d/(2*b)*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] + 
  d/(2*b)*Int[Sqrt[d*Sin[e+f*x]]*(a+2*b*Sin[e+f*x])/Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*(m+n)) + 
  1/(d*(m+n))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[a^2*c*d*(m+n)+b*d*(b*c*(m-1)+a*d*n)+
      (a*d*(2*b*c+a*d)*(m+n)-b*d*(a*c-b*d*(m+n-1)))*Sin[e+f*x]+
      b*d*(b*c*n+a*d*(2*m+n-1))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && 0<m<2 && -1<n<2 && 
  NeQ[m+n] && (IntegerQ[m] || IntegersQ[2*m,2*n])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b/d*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] - 
  (b*c-a*d)/d*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d] && PositiveIntegerQ[m]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Defer[Int][(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


(* Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(d_./sin[e_.+f_.*x_])^n_,x_Symbol] :=
  d^m*Int[(d*Csc[e+f*x])^(n-m)*(b+a*Csc[e+f*x])^m,x] /;
FreeQ[{a,b,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m] *)


(* Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(d_./cos[e_.+f_.*x_])^n_,x_Symbol] :=
  d^m*Int[(d*Sec[e+f*x])^(n-m)*(b+a*Sec[e+f*x])^m,x] /;
FreeQ[{a,b,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m] *)


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.*(d_.*sin[e_.+f_.*x_])^p_)^n_,x_Symbol] :=
  c^IntPart[n]*(c*(d*Sin[e + f*x])^p)^FracPart[n]/(d*Sin[e + f*x])^(p*FracPart[n])*
    Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n*p),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[n]]


Int[(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.*(d_.*cos[e_.+f_.*x_])^p_)^n_,x_Symbol] :=
  c^IntPart[n]*(c*(d*Cos[e + f*x])^p)^FracPart[n]/(d*Cos[e + f*x])^(p*FracPart[n])*
    Int[(a+b*Cos[e+f*x])^m*(d*Cos[e+f*x])^(n*p),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[n]]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^n,x] /;
FreeQ[{a,b,c,d,e,f,m},x] && IntegerQ[n]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/Csc[e+f*x]^m,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[(b+a*Sec[e+f*x])^m*(c+d*Sec[e+f*x])^n/Sec[e+f*x]^m,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Sin[e+f*x]^n*(c+d*Csc[e+f*x])^n/(d+c*Sin[e+f*x])^n*Int[(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[n]] && Not[IntegerQ[m]]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
  Cos[e+f*x]^n*(c+d*Sec[e+f*x])^n/(d+c*Cos[e+f*x])^n*Int[(a+b*Cos[e+f*x])^m*(d+c*Cos[e+f*x])^n/Cos[e+f*x]^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[n]] && Not[IntegerQ[m]]





(* ::Subsection::Closed:: *)
(*4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n*)


Int[cos[e_.+f_.*x_]*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/(b*f)*Subst[Int[(a+x)^m*(c+d/b*x)^n,x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_.*(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a*Int[Cos[e+f*x]^p*(d*Sin[e+f*x])^n,x] + b/d*Int[Cos[e+f*x]^p*(d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,n,p},x] && IntegerQ[(p-1)/2] && IntegerQ[n] && (p<0 && NeQ[a^2-b^2] || 0<n<p-1 || p+1<-n<2*p+1)


Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  1/a*Int[Cos[e+f*x]^(p-2)*(d*Sin[e+f*x])^n,x] - 
  1/(b*d)*Int[Cos[e+f*x]^(p-2)*(d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,n,p},x] && IntegerQ[(p-1)/2] && EqQ[a^2-b^2] && IntegerQ[n] && (0<n<(p+1)/2 || p<=-n<2*p-3 || 0<n<=-p)


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/(b^p*f)*Subst[Int[(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2)*(c+d/b*x)^n,x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,e,f,c,d,m,n},x] && IntegerQ[(p-1)/2] && EqQ[a^2-b^2]


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/(b^p*f)*Subst[Int[(a+x)^m*(c+d/b*x)^n*(b^2-x^2)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IntegerQ[(p-1)/2] && NeQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_.*(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^n,x] + b/d*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,g,n,p},x]


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g^2/a*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n,x] - 
  g^2/(b*d)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && EqQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^m*c^m/g^(2*m)*Int[(g*Cos[e+f*x])^(2*m+p)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m] && Not[IntegerQ[n] && n^2<m^2]


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  1/(a^(p/2)*c^(p/2))*Int[(a+b*Sin[e+f*x])^(m+p/2)*(c+d*Sin[e+f*x])^(n+p/2),x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[p/2]


Int[(g_.*cos[e_.+f_.*x_])^p_/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  g*Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])*Int[(g*Cos[e+f*x])^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/
    (g^(2*IntPart[m])*(g*Cos[e+f*x])^(2*FracPart[m]))*Int[(g*Cos[e+f*x])^(2*m+p)/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && EqQ[2*m+p-1] && EqQ[m-n-1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(m-n-1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && EqQ[2*m+p-1] && NeQ[m-n-1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(2*n+p+1)) - 
  b*(2*m+p-1)/(d*(2*n+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[Simplify[m+p/2-1/2]] && RationalQ[n] && n<-1 && 
  NeQ[2*n+p+1] && Not[NegativeIntegerQ[Simplify[m+n+p]] && Simplify[2*m+n+3*p/2+1]>0]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(m+n+p)) + 
  a*(2*m+p-1)/(m+n+p)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && PositiveIntegerQ[Simplify[m+p/2-1/2]] && Not[RationalQ[n] && n<-1] && 
  Not[PositiveIntegerQ[Simplify[n+p/2-1/2]] && m-n>0] && Not[NegativeIntegerQ[Simplify[m+n+p]] && Simplify[2*m+n+3*p/2+1]>0]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/
    (g^(2*IntPart[m])*(g*Cos[e+f*x])^(2*FracPart[m]))*Int[(g*Cos[e+f*x])^(2*m+p),x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && EqQ[2*m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*g*(m-n)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && EqQ[m+n+p+1] && NeQ[m-n]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*g*(2*m+p+1)) + 
  (m+n+p+1)/(a*(2*m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && NegativeIntegerQ[Simplify[m+n+p+1]] && NeQ[2*m+p+1] && 
  (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -2*b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(2*n+p+1)) - 
  b*(2*m+p-1)/(d*(2*n+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && RationalQ[m,n] && m>0 && n<-1 && NeQ[2*n+p+1] && 
  IntegersQ[2*m,2*n,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n/(f*g*(m+n+p)) + 
  a*(2*m+p-1)/(m+n+p)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && RationalQ[m] && m>0 && NeQ[m+n+p] && 
  Not[RationalQ[n] && 0<n<m] && IntegersQ[2*m,2*n,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*g*(2*m+p+1)) + 
  (m+n+p+1)/(a*(2*m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && RationalQ[m] && m<-1 && NeQ[2*m+p+1] && 
  Not[RationalQ[n] && m<n<-1] && IntegersQ[2*m,2*n,2*p]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/
    (g^(2*IntPart[m])*(g*Cos[e+f*x])^(2*FracPart[m]))*
    Int[(g*Cos[e+f*x])^(2*m+p)*(c+d*Sin[e+f*x])^(n-m),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && (FractionQ[m] || Not[FractionQ[n]])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[a^2-b^2] && EqQ[a*d*m+b*c*(m+p+1)]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(b*c+a*d)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(p+1)) + 
  b*(a*d*m+b*c*(m+p+1))/(a*g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[a^2-b^2] && RationalQ[m,p] && m>-1 && p<-1


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) + 
  (a*d*m+b*c*(m+p+1))/(b*(m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[a^2-b^2] && PositiveIntegerQ[Simplify[(2*m+p+1)/2]] && NeQ[m+p+1]


Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  2*(b*c-a*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*(2*m+3)) + 
  1/(b^3*(2*m+3))*Int[(a+b*Sin[e+f*x])^(m+2)*(b*c+2*a*d*(m+1)-b*d*(2*m+3)*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-3/2


Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  d*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+2)/(b^2*f*(m+3)) - 
  1/(b^2*(m+3))*Int[(a+b*Sin[e+f*x])^(m+1)*(b*d*(m+2)-a*c*(m+3)+(b*c*(m+3)-a*d*(m+4))*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[a^2-b^2] && RationalQ[m] && -3/2<=m<0


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (b*c-a*d)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(2*m+p+1)) + 
  (a*d*m+b*c*(m+p+1))/(a*b*(2*m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[a^2-b^2] && (RationalQ[m] && m<-1 || NegativeIntegerQ[Simplify[m+p]]) && NeQ[2*m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) + 
  (a*d*m+b*c*(m+p+1))/(b*(m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[a^2-b^2] && NeQ[m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])/(f*g*(p+1)) + 
  1/(g^2*(p+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1)*Simp[a*c*(p+2)+b*d*m+b*c*(m+p+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[a^2-b^2] && RationalQ[m,p] && m>0 && p<-1 && IntegerQ[2*m] && 
  Not[m==1 && NeQ[c^2-d^2] && SimplerQ[c+d*x,a+b*x]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(f*g*(m+p+1)) + 
  1/(m+p+1)*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1)*Simp[a*c*(m+p+1)+b*d*m+(a*d*m+b*c*(m+p+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[a^2-b^2] && RationalQ[m] && m>0 && Not[RationalQ[p] && p<-1] && IntegerQ[2*m] && 
  Not[m==1 && NeQ[c^2-d^2] && SimplerQ[c+d*x,a+b*x]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)*(b*c*(m+p+1)-a*d*p+b*d*(m+1)*Sin[e+f*x])/(b^2*f*(m+1)*(m+p+1)) + 
  g^2*(p-1)/(b^2*(m+1)*(m+p+1))*
    Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1)*Simp[b*d*(m+1)+(b*c*(m+p+1)-a*d*p)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[a^2-b^2] && RationalQ[m,p] && m<-1 && p>1 && NeQ[m+p+1] && IntegerQ[2*m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a^2-b^2)*(m+1)) + 
  1/((a^2-b^2)*(m+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*Simp[(a*c-b*d)*(m+1)-(b*c-a*d)*(m+p+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && IntegerQ[2*m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)*(b*c*(m+p+1)-a*d*p+b*d*(m+p)*Sin[e+f*x])/(b^2*f*(m+p)*(m+p+1)) + 
  g^2*(p-1)/(b^2*(m+p)*(m+p+1))*
    Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^m*Simp[b*(a*d*m+b*c*(m+p+1))+(a*b*c*(m+p+1)-d*(a^2*p-b^2*(m+p)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[a^2-b^2] && RationalQ[p] && p>1 && NeQ[m+p] && NeQ[m+p+1] && IntegerQ[2*m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)*(b*c-a*d-(a*c-b*d)*Sin[e+f*x])/(f*g*(a^2-b^2)*(p+1)) + 
  1/(g^2*(a^2-b^2)*(p+1))*
    Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m*Simp[c*(a^2*(p+2)-b^2*(m+p+2))+a*b*d*m+b*(a*c-b*d)*(m+p+3)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[a^2-b^2] && RationalQ[p] && p<-1 && IntegerQ[2*m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(c_.+d_.*sin[e_.+f_.*x_])/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[(g*Cos[e+f*x])^p,x] + (b*c-a*d)/b*Int[(g*Cos[e+f*x])^p/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  c*g*(g*Cos[e+f*x])^(p-1)/(f*(1+Sin[e+f*x])^((p-1)/2)*(1-Sin[e+f*x])^((p-1)/2))*
    Subst[Int[(1+d/c*x)^((p+1)/2)*(1-d/c*x)^((p-1)/2)*(a+b*x)^m,x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && NeQ[a^2-b^2] && EqQ[c^2-d^2]


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^(2*m)*Int[(d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2] && IntegersQ[m,p] && 2*m+p==0


Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(2*b*f*g*(m+1)) + 
  a/(2*g^2)*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && EqQ[m-p]


Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*m) - 
  1/g^2*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && EqQ[m+p+1]


Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  1/a^p*Int[ExpandTrig[(d*sin[e+f*x])^n*(a-b*sin[e+f*x])^(p/2)*(a+b*sin[e+f*x])^(m+p/2),x],x] /;
FreeQ[{a,b,d,e,f},x] && EqQ[a^2-b^2] && IntegersQ[m,n,p/2] && (m>0 && p>0 && -m-p<n<-1 || m>2 && p<0 && m+p/2>0)


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Int[ExpandTrig[(g*cos[e+f*x])^p,(d*sin[e+f*x])^n*(a+b*sin[e+f*x])^m,x],x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && EqQ[a^2-b^2] && PositiveIntegerQ[m]


Int[cos[e_.+f_.*x_]^2*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  1/b^2*Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^(m+1)*(a-b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && (NegativeIntegerQ[m] || Not[PositiveIntegerQ[n]])


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (a/g)^(2*m)*Int[(g*Cos[e+f*x])^(2*m+p)*(d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && EqQ[a^2-b^2] && NegativeIntegerQ[m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (a/g)^(2*m)*Int[(g*Cos[e+f*x])^(2*m+p)*(d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,d,e,f,g,n},x] && EqQ[a^2-b^2] && IntegerQ[m] && RationalQ[p] && (2*m+p==0 || 2*m+p>0 && p<-1)


Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(2*m+p+1)) - 
  1/(a^2*(2*m+p+1))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(a*m-b*(2*m+p+1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2] && RationalQ[m] && m<=-1/2 && NeQ[2*m+p+1]


Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*g*(m+p+2)) + 
  1/(b*(m+p+2))*Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m*(b*(m+1)-a*(p+1)*Sin[e+f*x]),x] /;
FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2] && NeQ[m+p+2]


Int[cos[e_.+f_.*x_]^2*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  1/b^2*Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^(m+1)*(a-b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && IntegersQ[2*m,2*n]


Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  -2/(a*b*d)*Int[(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+2),x] + 
  1/a^2*Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^(m+2)*(1+Sin[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2] && RationalQ[m] && m<-1


Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  1/d^4*Int[(d*Sin[e+f*x])^(n+4)*(a+b*Sin[e+f*x])^m,x] + 
  Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^m*(1-2*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && Not[PositiveIntegerQ[m]]


Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  a^m*Cos[e+f*x]/(f*Sqrt[1+Sin[e+f*x]]*Sqrt[1-Sin[e+f*x]])*
    Subst[Int[(d*x)^n*(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
FreeQ[{a,b,d,e,f,n},x] && EqQ[a^2-b^2] && IntegerQ[p/2] && IntegerQ[m]


Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Cos[e+f*x]/(a^(p-2)*f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]])*
    Subst[Int[(d*x)^n(a+b*x)^(m+p/2-1/2)*(a-b*x)^(p/2-1/2),x],x,Sin[e+f*x]] /;
FreeQ[{a,b,d,e,f,m,n},x] && EqQ[a^2-b^2] && IntegerQ[p/2] && Not[IntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Int[ExpandTrig[(g*cos[e+f*x])^p,(d*sin[e+f*x])^n*(a+b*sin[e+f*x])^m,x],x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && EqQ[a^2-b^2] && PositiveIntegerQ[m] && (IntegerQ[p] || PositiveIntegerQ[n])


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  a^m*g*(g*Cos[e+f*x])^(p-1)/(f*(1+Sin[e+f*x])^((p-1)/2)*(1-Sin[e+f*x])^((p-1)/2))*
    Subst[Int[(d*x)^n*(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
FreeQ[{a,b,d,e,f,n,p},x] && EqQ[a^2-b^2] && IntegerQ[m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)/(f*(a+b*Sin[e+f*x])^((p-1)/2)*(a-b*Sin[e+f*x])^((p-1)/2))*
    Subst[Int[(d*x)^n*(a+b*x)^(m+(p-1)/2)*(a-b*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
FreeQ[{a,b,d,e,f,m,n,p},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -g*(g*Cos[e+f*x])^(p-1)*Sqrt[d*Sin[e+f*x]]*(a+b*Sin[e+f*x])^(m+1)/(a*d*f*(m+1)) + 
  g^2*(2*m+3)/(2*a*(m+1))*Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1)/Sqrt[d*Sin[e+f*x]],x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && RationalQ[m] && m<-1 && EqQ[m+p+1/2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_/Sqrt[d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  2*(g*Cos[e+f*x])^(p+1)*Sqrt[d*Sin[e+f*x]]*(a+b*Sin[e+f*x])^m/(d*f*g*(2*m+1)) + 
  2*a*m/(g^2*(2*m+1))*Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1)/Sqrt[d*Sin[e+f*x]],x] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2] && RationalQ[m] && m>0 && EqQ[m+p+3/2]


Int[cos[e_.+f_.*x_]^2*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^m*(1-Sin[e+f*x]^2),x] /;
FreeQ[{a,b,d,e,f,m,n},x] && NeQ[a^2-b^2] && (PositiveIntegerQ[m] || IntegersQ[2*m,2*n])


(* Int[cos[e_.+f_.*x_]^4*sin[e_.+f_.*x_]^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (a^2-b^2)*Cos[e+f*x]*Sin[e+f*x]^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(a*b^2*d*(m+1)) - 
  (a^2*(n+1)-b^2*(m+n+2))*Cos[e+f*x]*Sin[e+f*x]^(n+1)*(a+b*Sin[e+f*x])^(m+2)/(a^2*b^2*d*(n+1)*(m+1)) + 
  1/(a^2*b*(n+1)*(m+1))*Int[Sin[e+f*x]^(n+1)*(a+b*Sin[e+f*x])^(m+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*(m+1)*Sin[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && IntegersQ[2*m,2*n] && m<-1 && n<-1 *)


Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Cos[e+f*x]*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(a*d*f*(n+1)) - 
  (a^2*(n+1)-b^2*(m+n+2))*Cos[e+f*x]*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^(m+1)/(a^2*b*d^2*f*(n+1)*(m+1)) + 
  1/(a^2*b*d*(n+1)*(m+1))*Int[(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*(m+1)*Sin[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && IntegersQ[2*m,2*n] && m<-1 && n<-1


Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (a^2-b^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*b^2*d*f*(m+1)) + 
  (a^2*(n-m+1)-b^2*(m+n+2))*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^(n+1)/(a^2*b^2*d*f*(m+1)*(m+2)) - 
  1/(a^2*b^2*(m+1)*(m+2))*Int[(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^n*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+3)+a*b*(m+2)*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2] && IntegersQ[2*m,2*n] && m<-1 && Not[n<-1] && (m<-2 || EqQ[m+n+4])


Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  (a^2-b^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*b^2*d*f*(m+1)) - 
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+2)*(d*Sin[e+f*x])^(n+1)/(b^2*d*f*(m+n+4)) - 
  1/(a*b^2*(m+1)*(m+n+4))*Int[(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^n*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+2)*(m+n+4)+a*b*(m+1)*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+3)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && NeQ[a^2-b^2] && IntegersQ[2*m,2*n] && m<-1 && Not[n<-1] && NeQ[m+n+4]


Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*d*f*(n+1)) - 
  b*(m+n+2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+2)/(a^2*d^2*f*(n+1)*(n+2)) - 
  1/(a^2*d^2*(n+1)*(n+2))*Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n+2)*
    Simp[a^2*n*(n+2)-b^2*(m+n+2)*(m+n+3)+a*b*m*Sin[e+f*x]-(a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NeQ[a^2-b^2] && (PositiveIntegerQ[m] || IntegersQ[2*m,2*n]) && Not[m<-1] && RationalQ[n] && n<-1 && 
  (n<-2 || EqQ[m+n+4])


Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+1)/(a*d*f*(n+1)) - 
  Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(d*Sin[e+f*x])^(n+2)/(b*d^2*f*(m+n+4)) + 
  1/(a*b*d*(n+1)*(m+n+4))*Int[(a+b*Sin[e+f*x])^m*(d*Sin[e+f*x])^(n+1)*
    Simp[a^2*(n+1)*(n+2)-b^2*(m+n+2)*(m+n+4)+a*b*(m+3)*Sin[e+f*x]-(a^2*(n+1)*(n+3)-b^2*(m+n+3)*(m+n+4))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m},x] && NeQ[a^2-b^2] && (PositiveIntegerQ[m] || IntegersQ[2*m,2*n]) && Not[m<-1] && RationalQ[n] && n<-1 && 
  NeQ[m+n+4]


Int[cos[e_.+f_.*x_]^4*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  a*(n+3)*Cos[e+f*x]*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(b^2*d*f*(m+n+3)*(m+n+4)) - 
  Cos[e+f*x]*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^(m+1)/(b*d^2*f*(m+n+4)) - 
  1/(b^2*(m+n+3)*(m+n+4))*Int[(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^m*
    Simp[a^2*(n+1)*(n+3)-b^2*(m+n+3)*(m+n+4)+a*b*m*Sin[e+f*x]-(a^2*(n+2)*(n+3)-b^2*(m+n+3)*(m+n+5))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m,n},x] && NeQ[a^2-b^2] && (PositiveIntegerQ[m] || IntegersQ[2*m,2*n]) && Not[m<-1] && Not[RationalQ[n] && n<-1] && 
  NeQ[m+n+3] && NeQ[m+n+4]


Int[cos[e_.+f_.*x_]^6*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Cos[e+f*x]*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1)/(a*d*f*(n+1)) - 
  b*(m+n+2)*Cos[e+f*x]*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^(m+1)/(a^2*d^2*f*(n+1)*(n+2)) - 
  a*(n+5)*Cos[e+f*x]*(d*Sin[e+f*x])^(n+3)*(a+b*Sin[e+f*x])^(m+1)/(b^2*d^3*f*(m+n+5)*(m+n+6)) + 
  Cos[e+f*x]*(d*Sin[e+f*x])^(n+4)*(a+b*Sin[e+f*x])^(m+1)/(b*d^4*f*(m+n+6)) + 
  1/(a^2*b^2*d^2*(n+1)*(n+2)*(m+n+5)*(m+n+6))*
    Int[(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^m*
      Simp[a^4*(n+1)*(n+2)*(n+3)*(n+5)-a^2*b^2*(n+2)*(2*n+1)*(m+n+5)*(m+n+6)+b^4*(m+n+2)*(m+n+3)*(m+n+5)*(m+n+6) + 
        a*b*m*(a^2*(n+1)*(n+2)-b^2*(m+n+5)*(m+n+6))*Sin[e+f*x] - 
        (a^4*(n+1)*(n+2)*(4+n)*(n+5)+b^4*(m+n+2)*(m+n+4)*(m+n+5)*(m+n+6)-a^2*b^2*(n+1)*(n+2)*(m+n+5)*(2*n+2*m+13))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,d,e,f,m,n},x] && NeQ[a^2-b^2] && IntegersQ[2*m,2*n] && NeQ[n+1] && NeQ[n+2] && NeQ[m+n+5] && 
  NeQ[m+n+6] && Not[PositiveIntegerQ[m]]


Int[cos[e_.+f_.*x_]^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Int[ExpandTrig[(d*sin[e+f*x])^n*(a+b*sin[e+f*x])^m*(1-sin[e+f*x]^2)^(p/2),x],x] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2] && IntegersQ[m,2*n,p/2] && (m<-1 || m==-1 && p>0)


Int[(g_.*cos[e_.+f_.*x_])^p_*sin[e_.+f_.*x_]^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  Int[ExpandTrig[(g*cos[e+f*x])^p,sin[e+f*x]^n/(a+b*sin[e+f*x]),x],x] /;
FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2] && IntegerQ[n] && (n<0 || PositiveIntegerQ[p+1/2])


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g^2/a*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n,x] - 
  b*g^2/(a^2*d)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1),x] - 
  g^2*(a^2-b^2)/(a^2*d^2)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+2)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && p>1 && (n<=-2 || n==-3/2 && p==3/2)


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g^2/(a*b)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n*(b-a*Sin[e+f*x]),x] + 
  g^2*(a^2-b^2)/(a*b*d)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && p>1 && (n<-1 || p==3/2 && n==-1/2)


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g^2/b^2*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n*(a-b*Sin[e+f*x]),x] - 
  g^2*(a^2-b^2)/b^2*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && p>1


(* Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g^2*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n/(a+b*Sin[e+f*x]),x] - 
  g^2/d^2*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+2)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && p>1 *)


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a*d^2/(a^2-b^2)*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-2),x] - 
  b*d/(a^2-b^2)*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1),x] - 
  a^2*d^2/(g^2*(a^2-b^2))*Int[(g*Cos[e+f*x])^(p+2)*(d*Sin[e+f*x])^(n-2)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && p<-1 && n>1


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -d/(a^2-b^2)*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1)*(b-a*Sin[e+f*x]),x] + 
  a*b*d/(g^2*(a^2-b^2))*Int[(g*Cos[e+f*x])^(p+2)*(d*Sin[e+f*x])^(n-1)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && p<-1 && n>0


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  1/(a^2-b^2)*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^n*(a-b*Sin[e+f*x]),x] - 
  b^2/(g^2*(a^2-b^2))*Int[(g*Cos[e+f*x])^(p+2)*(d*Sin[e+f*x])^n/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && p<-1


Int[Sqrt[g_.*cos[e_.+f_.*x_]]/(Sqrt[sin[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -4*Sqrt[2]*g/f*Subst[Int[x^2/(((a+b)*g^2+(a-b)*x^4)*Sqrt[1-x^4/g^2]),x],x,Sqrt[g*Cos[e+f*x]]/Sqrt[1+Sin[e+f*x]]] /;
FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2]


Int[Sqrt[g_.*cos[e_.+f_.*x_]]/(Sqrt[d_*sin[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
  Sqrt[Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]*Int[Sqrt[g*Cos[e+f*x]]/(Sqrt[Sin[e+f*x]]*(a+b*Sin[e+f*x])),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2]


Int[Sqrt[d_.*sin[e_.+f_.*x_]]/(Sqrt[cos[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
  With[{q=Rt[-a^2+b^2,2]},
  2*Sqrt[2]*d*(b+q)/(f*q)*Subst[Int[1/((d*(b+q)+a*x^2)*Sqrt[1-x^4/d^2]),x],x,Sqrt[d*Sin[e+f*x]]/Sqrt[1+Cos[e+f*x]]] - 
  2*Sqrt[2]*d*(b-q)/(f*q)*Subst[Int[1/((d*(b-q)+a*x^2)*Sqrt[1-x^4/d^2]),x],x,Sqrt[d*Sin[e+f*x]]/Sqrt[1+Cos[e+f*x]]]] /;
FreeQ[{a,b,d,e,f},x] && NeQ[a^2-b^2]


Int[Sqrt[d_.*sin[e_.+f_.*x_]]/(Sqrt[g_.*cos[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
  Sqrt[Cos[e+f*x]]/Sqrt[g*Cos[e+f*x]]*Int[Sqrt[d*Sin[e+f*x]]/(Sqrt[Cos[e+f*x]]*(a+b*Sin[e+f*x])),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2]


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  d/b*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1),x] - 
  a*d/b*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n-1)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && -1<p<1 && n>0


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  1/a*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^n,x] - 
  b/(a*d)*Int[(g*Cos[e+f*x])^p*(d*Sin[e+f*x])^(n+1)/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[2*n,2*p] && -1<p<1 && n<0


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  Int[ExpandTrig[(g*cos[e+f*x])^p,(d*sin[e+f*x])^n*(a+b*sin[e+f*x])^m,x],x] /;
FreeQ[{a,b,d,e,f,g,n,p},x] && NeQ[a^2-b^2] && IntegerQ[m] && (m>0 || IntegerQ[n])


Int[(g_.*cos[e_.+f_.*x_])^p_*(d_.*sin[e_.+f_.*x_])^n_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
  g^2/a*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^n*(a+b*Sin[e+f*x])^(m+1),x] - 
  b*g^2/(a^2*d)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+1)*(a+b*Sin[e+f*x])^(m+1),x] - 
  g^2*(a^2-b^2)/(a^2*d^2)*Int[(g*Cos[e+f*x])^(p-2)*(d*Sin[e+f*x])^(n+2)*(a+b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,d,e,f,g},x] && NeQ[a^2-b^2] && IntegersQ[m,2*n,2*p] && m<0 && p>1 && (n<=-2 || m==-1 && n==-3/2 && p==3/2)


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^(2*m)*Int[(c+d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[a^2-b^2] && IntegersQ[m,p] && 2*m+p==0


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (a/g)^(2*m)*Int[(g*Cos[e+f*x])^(2*m+p)*(c+d*Sin[e+f*x])^n/(a-b*Sin[e+f*x])^m,x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[a^2-b^2] && IntegerQ[m] && RationalQ[p] && (2*m+p==0 || 2*m+p>0 && p<-1)


Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  1/b^2*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*(a-b*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[a^2-b^2] && IntegersQ[2*m,2*n]


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^m*Cos[e+f*x]/(f*Sqrt[1+Sin[e+f*x]]*Sqrt[1-Sin[e+f*x]])*
    Subst[Int[(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2)*(c+d*x)^n,x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && EqQ[a^2-b^2] && IntegerQ[p/2] && IntegerQ[m]


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Cos[e+f*x]/(a^(p-2)*f*Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]])*
    Subst[Int[(a+b*x)^(m+p/2-1/2)*(a-b*x)^(p/2-1/2)*(c+d*x)^n,x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[a^2-b^2] && IntegerQ[p/2] && Not[IntegerQ[m]]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(g*cos[e+f*x])^p,(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[a^2-b^2] && PositiveIntegerQ[m] && (IntegerQ[p] || PositiveIntegerQ[n])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  a^m*g*(g*Cos[e+f*x])^(p-1)/(f*(1+Sin[e+f*x])^((p-1)/2)*(1-Sin[e+f*x])^((p-1)/2))*
    Subst[Int[(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2)*(c+d*x)^n,x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[a^2-b^2] && IntegerQ[m]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  g*(g*Cos[e+f*x])^(p-1)/(f*(a+b*Sin[e+f*x])^((p-1)/2)*(a-b*Sin[e+f*x])^((p-1)/2))*
    Subst[Int[(a+b*x)^(m+(p-1)/2)*(a-b*x)^((p-1)/2)*(c+d*x)^n,x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[a^2-b^2] && Not[IntegerQ[m]]


Int[cos[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(1-Sin[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[a^2-b^2] && (PositiveIntegerQ[m] || IntegersQ[2*m,2*n])


Int[cos[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n*(1-sin[e+f*x]^2)^(p/2),x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NeQ[a^2-b^2] && PositiveIntegerQ[p/2] && (PositiveIntegerQ[m] || IntegersQ[2*m,2*n])


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(g*cos[e+f*x])^p*(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[a^2-b^2] && IntegersQ[2*m,2*n]


Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[a^2-b^2]


Int[(g_.*sec[e_.+f_.*x_])^p_*(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  g^(2*IntPart[p])*(g*Cos[e+f*x])^FracPart[p]*(g*Sec[e+f*x])^FracPart[p]*
    Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(g*Cos[e+f*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IntegerQ[p]]


Int[(g_.*csc[e_.+f_.*x_])^p_*(a_.+b_.*cos[e_.+f_.*x_])^m_.*(c_.+d_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
  g^(2*IntPart[p])*(g*Sin[e+f*x])^FracPart[p]*(g*Csc[e+f*x])^FracPart[p]*
    Int[(a+b*Cos[e+f*x])^m*(c+d*Cos[e+f*x])^n/(g*Sin[e+f*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IntegerQ[p]]





(* ::Subsection::Closed:: *)
(*4.1.2.3 (g sin)^p (a+b sin)^m (c+d sin)^n*)


Int[Sqrt[g_.*sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  g/d*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[g*Sin[e+f*x]],x] - 
  c*g/d*Int[Sqrt[a+b*Sin[e+f*x]]/(Sqrt[g*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && (EqQ[a^2-b^2] || EqQ[c^2-d^2])


Int[Sqrt[g_.*sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b/d*Int[Sqrt[g*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] - 
  (b*c-a*d)/d*Int[Sqrt[g*Sin[e+f*x]]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[g_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -2*b/f*Subst[Int[1/(b*c+a*d+c*g*x^2),x],x,b*Cos[e+f*x]/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -Sqrt[a+b]/(c*f)*EllipticE[ArcSin[Cos[e+f*x]/(1+Sin[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[d-c] && PositiveQ[b^2-a^2] && PositiveQ[b]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[g_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]/(c+d*Sin[e+f*x])]/
    (d*f*Sqrt[g*Sin[e+f*x]]*Sqrt[c^2*(a+b*Sin[e+f*x])/((a*c+b*d)*(c+d*Sin[e+f*x]))])*
    EllipticE[ArcSin[c*Cos[e+f*x]/(c+d*Sin[e+f*x])],(b*c-a*d)/(b*c+a*d)] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && EqQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[g_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  a/c*Int[1/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] + 
  (b*c-a*d)/(c*g)*Int[Sqrt[g*Sin[e+f*x]]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  1/c*Int[Sqrt[a+b*Sin[e+f*x]]/Sin[e+f*x],x] - 
  d/c*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  a/c*Int[1/(Sin[e+f*x]*Sqrt[a+b*Sin[e+f*x]]),x] + 
  (b*c-a*d)/c*Int[1/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[Sqrt[g_.*sin[e_.+f_.*x_]]/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  -a*g/(b*c-a*d)*Int[1/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] + 
  c*g/(b*c-a*d)*Int[Sqrt[a+b*Sin[e+f*x]]/(Sqrt[g*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && (EqQ[a^2-b^2] || EqQ[c^2-d^2])


Int[Sqrt[g_.*sin[e_.+f_.*x_]]/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  2*Sqrt[-Cot[e+f*x]^2]*Sqrt[g*Sin[e+f*x]]/(f*(c+d)*Cot[e+f*x]*Sqrt[a+b*Sin[e+f*x]])*Sqrt[(b+a*Csc[e+f*x])/(a+b)]*
    EllipticPi[2*c/(c+d),ArcSin[Sqrt[1-Csc[e+f*x]]/Sqrt[2]],2*a/(a+b)] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[1/(Sqrt[g_.*sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] - 
  d/(b*c-a*d)*Int[Sqrt[a+b*Sin[e+f*x]]/(Sqrt[g*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && (EqQ[a^2-b^2] || EqQ[c^2-d^2])


Int[1/(Sqrt[g_.*sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  1/c*Int[1/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] - 
  d/(c*g)*Int[Sqrt[g*Sin[e+f*x]]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[1/(sin[e_.+f_.*x_]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  d^2/(c*(b*c-a*d))*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] + 
  1/(c*(b*c-a*d))*Int[(b*c-a*d-b*d*Sin[e+f*x])/(Sin[e+f*x]*Sqrt[a+b*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2]


Int[1/(sin[e_.+f_.*x_]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  1/c*Int[1/(Sin[e+f*x]*Sqrt[a+b*Sin[e+f*x]]),x] - d/c*Int[1/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -d/c*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  1/c*Int[Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]/Sin[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && EqQ[b*c+a*d]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*a/f*Subst[Int[1/(1-a*c*x^2),x],x,Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[b*c+a*d]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  (b*c-a*d)/c*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] + 
  a/c*Int[Sqrt[c+d*Sin[e+f*x]]/(Sin[e+f*x]*Sqrt[a+b*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && EqQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*(a+b*Sin[e+f*x])/(c*f*Rt[(a+b)/(c+d),2]*Cos[e+f*x])*
    Sqrt[-(b*c-a*d)*(1-Sin[e+f*x])/((c+d)*(a+b*Sin[e+f*x]))]*Sqrt[(b*c-a*d)*(1+Sin[e+f*x])/((c-d)*(a+b*Sin[e+f*x]))]*
    EllipticPi[a*(c+d)/(c*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[1/(sin[e_.+f_.*x_]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])*Int[1/(Cos[e+f*x]*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && EqQ[c^2-d^2]


Int[1/(sin[e_.+f_.*x_]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -b/a*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] + 
  1/a*Int[Sqrt[a+b*Sin[e+f*x]]/(Sin[e+f*x]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && (NeQ[a^2-b^2] || NeQ[c^2-d^2])


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]/sin[e_.+f_.*x_],x_Symbol] :=
  Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]/Cos[e+f*x]*Int[Cot[e+f*x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && EqQ[c^2-d^2]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]/sin[e_.+f_.*x_],x_Symbol] :=
  d*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  c*Int[Sqrt[a+b*Sin[e+f*x]]/(Sin[e+f*x]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d] && (NeQ[a^2-b^2] || NeQ[c^2-d^2])


Int[sin[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  a^n*c^n*Int[Tan[e+f*x]^p*(a+b*Sin[e+f*x])^(m-n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && EqQ[p+2*n] && IntegerQ[n]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Sqrt[a-b*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(f*Cos[e+f*x])*
    Subst[Int[(g*x)^p*(a+b*x)^(m-1/2)*(c+d*x)^n/Sqrt[a-b*x],x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && IntegerQ[m-1/2]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[ExpandTrig[(g*sin[e+f*x])^p*(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[b*c-a*d] && (IntegersQ[m,n] || IntegersQ[m,p] || IntegersQ[n,p]) && NeQ[p-2]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  Defer[Int][(g*Sin[e+f*x])^p*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[p-2]


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_.+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  g^(m+n)*Int[(g*Sin[e+f*x])^(p-m-n)*(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b*c-a*d] && Not[IntegerQ[p]] && IntegerQ[m] && IntegerQ[n]


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_.+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  (g*Csc[e+f*x])^p*(g*Sin[e+f*x])^p*Int[(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/(g*Csc[e+f*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d] && Not[IntegerQ[p]] && Not[IntegerQ[m] && IntegerQ[n]]


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  g^n*Int[(g*Sin[e+f*x])^(p-n)*(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && IntegerQ[n]


Int[sin[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Int[(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/Csc[e+f*x]^(m+p),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m] && IntegerQ[p]


Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  Csc[e+f*x]^p*(g*Sin[e+f*x])^p*Int[(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/Csc[e+f*x]^(m+p),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && Not[IntegerQ[n]] && IntegerQ[m] && Not[IntegerQ[p]]


Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  (g*Sin[e+f*x])^n*(c+d*Csc[e+f*x])^n/(d+c*Sin[e+f*x])^n*Int[(g*Sin[e+f*x])^(p-n)*(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IntegerQ[n]] && Not[IntegerQ[m]]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  g^(m+n)*Int[(g*Csc[e+f*x])^(p-m-n)*(b+a*Csc[e+f*x])^m*(d+c*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b*c-a*d] && Not[IntegerQ[p]] && IntegerQ[m] && IntegerQ[n]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  (g*Csc[e+f*x])^p*(g*Sin[e+f*x])^p*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(g*Sin[e+f*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d] && Not[IntegerQ[p]] && Not[IntegerQ[m] && IntegerQ[n]]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  g^m*Int[(g*Csc[e+f*x])^(p-m)*(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && IntegerQ[m]


Int[csc[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^(n+p),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && Not[IntegerQ[m]] && IntegerQ[n] && IntegerQ[p]


Int[(g_.*csc[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
  Sin[e+f*x]^p*(g*Csc[e+f*x])^p*Int[(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^(n+p),x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && Not[IntegerQ[m]] && IntegerQ[n] && Not[IntegerQ[p]]


Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
  (a+b*Sin[e+f*x])^m*(g*Csc[e+f*x])^m/(b+a*Csc[e+f*x])^m*
    Int[(g*Csc[e+f*x])^(p-m)*(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]





(* ::Subsection::Closed:: *)
(*4.1.3.1 (a+b sin)^m (c+d sin)^n (A+B sin)*)


Int[sin[e_.+f_.*x_]^n_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  Int[ExpandTrig[sin[e+f*x]^n*(a+b*sin[e+f*x])^m*(A+B*sin[e+f*x]),x],x] /;
FreeQ[{a,b,e,f,A,B},x] && EqQ[A*b+a*B] && EqQ[a^2-b^2] && IntegerQ[m] && IntegerQ[n]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  a^m*c^m*Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m)*(A+B*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m] && Not[IntegerQ[n] && (m<0 && n>0 || 0<n<m || m<n<0)]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  Int[(a+b*Sin[e+f*x])^m*(A*c+(B*c+A*d)*Sin[e+f*x]+B*d*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d]


Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  (A*b+a*B)/(2*a*b)*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  (B*c+A*d)/(2*c*d)*Int[Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && EqQ[A*b*(m+n+1)+a*B*(m-n)] && 
  NeQ[m+1/2]


Int[Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] - 
  (B*c-A*d)/d*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) + 
  (a*B*(m-n)+A*b*(m+n+1))/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && 
  (RationalQ[m] && m<-1/2 || NegativeIntegerQ[m+n] && Not[SumSimplerQ[n,1]]) && NeQ[2*m+1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) - 
  (B*c*(m-n)-A*d*(m+n+1))/(d*(m+n+1))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && 
  NeQ[m+n+1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)) /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && EqQ[m+n+2] && 
  EqQ[A*(a*d*m+b*c*(n+1))-B*(a*c*m+b*d*(n+1))]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b^2*(B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)) - 
  b/(d*(n+1)*(b*c+a*d))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[a*A*d*(m-n-2)-B*(a*c*(m-1)+b*d*(n+1))-(A*b*d*(m+n+1)-B*(b*c*m-a*d*(n+1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m>1/2 && n<-1 && 
  IntegerQ[2*m] && (IntegerQ[2*n] || EqQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
    Simp[a*A*d*(m+n+1)+B*(a*c*(m-1)+b*d*(n+1))+(A*b*d*(m+n+1)-B*(b*c*m-a*d*(2*m+n)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m>1/2 && 
  Not[RationalQ[n] && n<-1] && IntegerQ[2*m] && (IntegerQ[2*n] || EqQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(a*f*(2*m+1)) - 
  1/(a*b*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[A*(a*d*n-b*c*(m+1))-B*(a*c*m+b*d*n)-d*(a*B*(m-n)+A*b*(m+n+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m<-1/2 && n>0 && 
  IntegerQ[2*m] && (IntegerQ[2*n] || EqQ[c])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  b*(A*b-a*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(a*f*(2*m+1)*(b*c-a*d)) + 
  1/(a*(2*m+1)*(b*c-a*d))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[B*(a*c*m+b*d*(n+1))+A*(b*c*(m+1)-a*d*(2*m+n+2))+d*(A*b-a*B)*(m+n+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m<-1/2 && 
  Not[RationalQ[n] && n>0] && IntegerQ[2*m] && (IntegerQ[2*n] || EqQ[c])


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*b*B*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(2*n+3)*Sqrt[a+b*Sin[e+f*x]]) /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && EqQ[A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1))]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b^2*(B*c-A*d)*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(b*c+a*d)*Sqrt[a+b*Sin[e+f*x]]) + 
  (A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)))/(2*d*(n+1)*(b*c+a*d))*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n<-1


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*b*B*Cos[e+f*x]*(c+d*Sin[e+f*x])^(n+1)/(d*f*(2*n+3)*Sqrt[a+b*Sin[e+f*x]]) + 
  (A*b*d*(2*n+3)-B*(b*c-2*a*d*(n+1)))/(b*d*(2*n+3))*Int[Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && Not[RationalQ[n] && n<-1]


Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  (A*b-a*B)/b*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] + 
  B/b*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -B*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(f*(m+n+1)) + 
  1/(b*(m+n+1))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n-1)*
    Simp[A*b*c*(m+n+1)+B*(a*c*m+b*d*n)+(A*b*d*(m+n+1)+B*(a*d*m+b*c*n))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n>0 && 
  (IntegerQ[n] || EqQ[m+1/2])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(n+1)*(c^2-d^2)) + 
  1/(b*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*(a*d*m+b*c*(n+1))-B*(a*c*m+b*d*(n+1))+b*(B*c-A*d)*(m+n+2)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n<-1 && 
  (IntegerQ[n] || EqQ[m+1/2])


Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  (A*b-a*B)/(b*c-a*d)*Int[1/Sqrt[a+b*Sin[e+f*x]],x] + 
  (B*c-A*d)/(b*c-a*d)*Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[(a+b*Sin[e+f*x])^m,x] - (B*c-A*d)/d*Int[(a+b*Sin[e+f*x])^m/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && NeQ[m+1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (A*b-a*B)/b*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] + 
  B/b*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && NeQ[A*b+a*B]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(b*c-a*d)*(B*c-A*d)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[b*(b*c-a*d)*(B*c-A*d)*(m-1)+a*d*(a*A*c+b*B*c-(A*b+a*B)*d)*(n+1)+
      (b*(b*d*(B*c-A*d)+a*(A*c*d+B*(c^2-2*d^2)))*(n+1)-a*(b*c-a*d)*(B*c-A*d)*(n+2))*Sin[e+f*x]+
      b*(d*(A*b*c+a*B*c-a*A*d)*(m+n+1)-b*B*(c^2*m+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m>1 && n<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -b*B*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+1)) + 
  1/(d*(m+n+1))*Int[(a+b*Sin[e+f*x])^(m-2)*(c+d*Sin[e+f*x])^n*
    Simp[a^2*A*d*(m+n+1)+b*B*(b*c*(m-1)+a*d*(n+1))+
      (a*d*(2*A*b+a*B)*(m+n+1)-b*B*(a*c-b*d*(m+n)))*Sin[e+f*x]+
      b*(A*b*d*(m+n+1)-B*(b*c*m-a*d*(2*m+n)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m>1 && 
  Not[IntegerQ[n] && n>1 && (Not[IntegerQ[m]] || EqQ[a] && NeQ[c])]


Int[Sqrt[c_+d_.*sin[e_.+f_.*x_]]*(A_.+B_.*sin[e_.+f_.*x_])/(b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  B*d/b^2*Int[Sqrt[b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  Int[(A*c+(B*c+A*d)*Sin[e+f*x])/((b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{b,c,d,e,f,A,B},x] && NeQ[c^2-d^2]


Int[Sqrt[c_.+d_.*sin[e_.+f_.*x_]]*(A_.+B_.*sin[e_.+f_.*x_])/(a_+b_.*sin[e_.+f_.*x_])^(3/2),x_Symbol] :=
  B/b*Int[Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] + 
  (A*b-a*B)/b*Int[Sqrt[c+d*Sin[e+f*x]]/(a+b*Sin[e+f*x])^(3/2),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  2*(A*b-a*B)*Cos[e+f*x]/(f*(a^2-b^2)*Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]]) + 
  d/(a^2-b^2)*Int[(A*b-a*B+(a*A-b*B)*Sin[e+f*x])/(Sqrt[a+b*Sin[e+f*x]]*(d*Sin[e+f*x])^(3/2)),x] /;
FreeQ[{a,b,d,e,f,A,B},x] && NeQ[a^2-b^2]


Int[(A_+B_.*sin[e_.+f_.*x_])/((b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*A*(c-d)*Tan[e+f*x]/(f*b*c^2)*Rt[(c+d)/b,2]*Sqrt[c*(1+Csc[e+f*x])/(c-d)]*Sqrt[c*(1-Csc[e+f*x])/(c+d)]*
    EllipticE[ArcSin[Sqrt[c+d*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]/Rt[(c+d)/b,2]],-(c+d)/(c-d)] /;
FreeQ[{b,c,d,e,f,A,B},x] && NeQ[c^2-d^2] && EqQ[A-B] && PosQ[(c+d)/b]


Int[(A_+B_.*sin[e_.+f_.*x_])/((b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -Sqrt[-b*Sin[e+f*x]]/Sqrt[b*Sin[e+f*x]]*Int[(A+B*Sin[e+f*x])/((-b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{b,c,d,e,f,A,B},x] && NeQ[c^2-d^2] && EqQ[A-B] && NegQ[(c+d)/b]


Int[(A_+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -2*A*(c-d)*(a+b*Sin[e+f*x])/(f*(b*c-a*d)^2*Rt[(a+b)/(c+d),2]*Cos[e+f*x])*
    Sqrt[(b*c-a*d)*(1+Sin[e+f*x])/((c-d)*(a+b*Sin[e+f*x]))]*
    Sqrt[-(b*c-a*d)*(1-Sin[e+f*x])/((c+d)*(a+b*Sin[e+f*x]))]*
    EllipticE[ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && EqQ[A-B] && PosQ[(a+b)/(c+d)]


Int[(A_+B_.*sin[e_.+f_.*x_])/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[-c-d*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]]*Int[(A+B*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[-c-d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && EqQ[A-B] && NegQ[(a+b)/(c+d)]


Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  (A-B)/(a-b)*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] - 
  (A*b-a*B)/(a-b)*Int[(1+Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && NeQ[A-B]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  (B*a-A*b)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n/(f*(m+1)*(a^2-b^2)) + 
  1/((m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n-1)*
    Simp[c*(a*A-b*B)*(m+1)+d*n*(A*b-a*B)+(d*(a*A-b*B)*(m+1)-c*(A*b-a*B)*(m+2))*Sin[e+f*x]-d*(A*b-a*B)*(m+n+2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m<-1 && n>0


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -(A*b^2-a*b*B)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(1+n)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[(a*A-b*B)*(b*c-a*d)*(m+1)+b*d*(A*b-a*B)*(m+n+2)+
      (A*b-a*B)*(a*d*(m+1)-b*c*(m+2))*Sin[e+f*x]-
      b*d*(A*b-a*B)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  (EqQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || EqQ[a])])


Int[(A_.+B_.*sin[e_.+f_.*x_])/((a_.+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  (A*b-a*B)/(b*c-a*d)*Int[1/(a+b*Sin[e+f*x]),x] + (B*c-A*d)/(b*c-a*d)*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_])/(c_.+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
  B/d*Int[(a+b*Sin[e+f*x])^m,x] - (B*c-A*d)/d*Int[(a+b*Sin[e+f*x])^m/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*B*Cos[e+f*x]*Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])^n/(f*(2*n+3)) + 
  1/(2*n+3)*Int[(c+d*Sin[e+f*x])^(n-1)/Sqrt[a+b*Sin[e+f*x]]*
    Simp[a*A*c*(2*n+3)+B*(b*c+2*a*d*n)+
      (B*(a*c+b*d)*(2*n+1)+A*(b*c+a*d)*(2*n+3))*Sin[e+f*x]+
      (A*b*d*(2*n+3)+B*(a*d+2*b*c*n))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[n] && n^2==1/4


Int[(A_+B_.*sin[e_.+f_.*x_])/(Sqrt[sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  4*A/(f*Sqrt[a+b])*EllipticPi[-1,-ArcSin[Cos[e+f*x]/(1+Sin[e+f*x])],-(a-b)/(a+b)] /;
FreeQ[{a,b,e,f,A,B},x] && PositiveQ[b] && PositiveQ[b^2-a^2] && EqQ[A-B]


Int[(A_+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[d_*sin[e_.+f_.*x_]]),x_Symbol] :=
  Sqrt[Sin[e+f*x]]/Sqrt[d*Sin[e+f*x]]*Int[(A+B*Sin[e+f*x])/(Sqrt[Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] /;
FreeQ[{a,b,e,f,d,A,B},x] && PositiveQ[b] && PositiveQ[b^2-a^2] && EqQ[A-B]


Int[(A_.+B_.*sin[e_.+f_.*x_])/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  B/d*Int[Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] - 
  (B*c-A*d)/d*Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]),x_Symbol] :=
  Defer[Int][(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+B*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


(* Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_])^p_,x_Symbol] :=
  a^m*c^m*Int[Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m)*(A+B*Sin[e+f*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m] && 
  Not[IntegerQ[n] && (m<0 && n>0 || 0<n<m || m<n<0)] *)


(* Int[(a_+b_.*cos[e_.+f_.*x_])^m_*(c_+d_.*cos[e_.+f_.*x_])^n_*(A_.+B_.*cos[e_.+f_.*x_])^p_,x_Symbol] :=
  a^m*c^m*Int[Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m)*(A+B*Cos[e+f*x])^p,x] /;
FreeQ[{a,b,c,d,e,f,A,B,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && IntegerQ[m] && 
  Not[IntegerQ[n] && (m<0 && n>0 || 0<n<m || m<n<0)] *)


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_])^p_,x_Symbol] :=
  Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]/(f*Cos[e+f*x])*
    Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^(n-1/2)*(A+B*x)^p,x],x,Sin[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]


Int[(a_+b_.*cos[e_.+f_.*x_])^m_.*(c_+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_])^p_,x_Symbol] :=
  -Sqrt[a+b*Cos[e+f*x]]*Sqrt[c+d*Cos[e+f*x]]/(f*Sin[e+f*x])*
    Subst[Int[(a+b*x)^(m-1/2)*(c+d*x)^(n-1/2)*(A+B*x)^p,x],x,Cos[e+f*x]] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2]





(* ::Subsection::Closed:: *)
(*4.1.4.1 (a+b sin)^m (A+B sin+C sin^2)*)


Int[(b_.*sin[e_.+f_.*x_])^m_.*(B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  1/b*Int[(b*Sin[e+f*x])^(m+1)*(B+C*Sin[e+f*x]),x] /;
FreeQ[{b,e,f,B,C,m},x]


Int[(b_.*sin[e_.+f_.*x_])^m_.*(A_+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cos[e+f*x]*(b*Sin[e+f*x])^(m+1)/(b*f*(m+1)) /;
FreeQ[{b,e,f,A,C,m},x] && EqQ[A*(m+2)+C*(m+1)]


Int[(b_.*sin[e_.+f_.*x_])^m_*(A_+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  A*Cos[e+f*x]*(b*Sin[e+f*x])^(m+1)/(b*f*(m+1)) + (A*(m+2)+C*(m+1))/(b^2*(m+1))*Int[(b*Sin[e+f*x])^(m+2),x] /;
FreeQ[{b,e,f,A,C},x] && RationalQ[m] && m<-1


Int[sin[e_.+f_.*x_]^m_.*(A_+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -1/f*Subst[Int[(1-x^2)^((m-1)/2)*(A+C-C*x^2),x],x,Cos[e+f*x]] /;
FreeQ[{e,f,A,C},x] && PositiveIntegerQ[(m+1)/2]


Int[(b_.*sin[e_.+f_.*x_])^m_.*(A_+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + (A*(m+2)+C*(m+1))/(m+2)*Int[(b*Sin[e+f*x])^m,x] /;
FreeQ[{b,e,f,A,C,m},x] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  1/b^2*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[b*B-a*C+b*C*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && EqQ[A*b^2-a*b*B+a^2*C]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  C/b^2*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[-a+b*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && EqQ[A*b^2+a^2*C]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (A-C)*Int[(a+b*Sin[e+f*x])^m*(1+Sin[e+f*x]),x] + C*Int[(a+b*Sin[e+f*x])^m*(1+Sin[e+f*x])^2,x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && EqQ[A-B+C] && Not[IntegerQ[2*m]]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (A-C)*Int[(a+b*Sin[e+f*x])^m*(1+Sin[e+f*x]),x] + C*Int[(a+b*Sin[e+f*x])^m*(1+Sin[e+f*x])^2,x] /;
FreeQ[{a,b,e,f,A,C,m},x] && EqQ[A+C] && Not[IntegerQ[2*m]]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (A*b-a*B+b*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*A*(m+1)+m*(b*B-a*C)+b*C*(2*m+1)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && RationalQ[m] && m<-1 && EqQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  b*(A+C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m/(a*f*(2*m+1)) + 
  1/(a^2*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*A*(m+1)-a*C*m+b*C*(2*m+1)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && RationalQ[m] && m<-1 && EqQ[a^2-b^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*
    Int[(a+b*Sin[e+f*x])^(m+1)*Simp[b*(a*A-b*B+a*C)*(m+1)-(A*b^2-a*b*B+a^2*C+b*(A*b-a*B+b*C)*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C},x] && RationalQ[m] && m<-1 && NeQ[a^2-b^2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)*(a^2-b^2)) + 
  1/(b*(m+1)*(a^2-b^2))*
    Int[(a+b*Sin[e+f*x])^(m+1)*Simp[a*b*(A+C)*(m+1)-(A*b^2+a^2*C+b^2*(A+C)*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C},x] && RationalQ[m] && m<-1 && NeQ[a^2-b^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[A*b*(m+2)+b*C*(m+1)+(b*B*(m+2)-a*C)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,B,C,m},x] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+2)) + 
  1/(b*(m+2))*Int[(a+b*Sin[e+f*x])^m*Simp[A*b*(m+2)+b*C*(m+1)-a*C*Sin[e+f*x],x],x] /;
FreeQ[{a,b,e,f,A,C,m},x] && Not[RationalQ[m] && m<-1]


Int[(b_.*sin[e_.+f_.*x_]^p_)^m_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (b*Sin[e+f*x]^p)^m/(b*Sin[e+f*x])^(m*p)*Int[(b*Sin[e+f*x])^(m*p)*(A+B*Sin[e+f*x]+C*Sin[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,B,C,m,p},x] && Not[IntegerQ[m]]


Int[(b_.*cos[e_.+f_.*x_]^p_)^m_*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (b*Cos[e+f*x]^p)^m/(b*Cos[e+f*x])^(m*p)*Int[(b*Cos[e+f*x])^(m*p)*(A+B*Cos[e+f*x]+C*Cos[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,B,C,m,p},x] && Not[IntegerQ[m]]


Int[(b_.*sin[e_.+f_.*x_]^p_)^m_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (b*Sin[e+f*x]^p)^m/(b*Sin[e+f*x])^(m*p)*Int[(b*Sin[e+f*x])^(m*p)*(A+C*Sin[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,C,m,p},x] && Not[IntegerQ[m]]


Int[(b_.*cos[e_.+f_.*x_]^p_)^m_*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (b*Cos[e+f*x]^p)^m/(b*Cos[e+f*x])^(m*p)*Int[(b*Cos[e+f*x])^(m*p)*(A+C*Cos[e+f*x]^2),x] /;
FreeQ[{b,e,f,A,C,m,p},x] && Not[IntegerQ[m]]





(* ::Subsection::Closed:: *)
(*4.1.4.2 (a+b sin)^m (c+d sin)^n (A+B sin+C sin^2)*)


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(b*c-a*d)*(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) - 
  1/(b^2*(m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*
    Simp[b*(m+1)*((b*B-a*C)*(b*c-a*d)-A*b*(a*c-b*d))+
      (b*B*(a^2*d+b^2*d*(m+1)-a*b*c*(m+2))+(b*c-a*d)*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Sin[e+f*x]-
      b*C*d*(m+1)*(a^2-b^2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(b*c-a*d)*(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*(m+1)*(a^2-b^2)) + 
  1/(b^2*(m+1)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*
    Simp[b*(m+1)*(a*C*(b*c-a*d)+A*b*(a*c-b*d))-
      ((b*c-a*d)*(A*b^2*(m+2)+C*(a^2+b^2*(m+1))))*Sin[e+f*x]+
      b*C*d*(m+1)*(a^2-b^2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && RationalQ[m] && m<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*d*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[(a+b*Sin[e+f*x])^m*
    Simp[a*C*d+A*b*c*(m+3)+b*(B*c*(m+3)+d*(C*(m+2)+A*(m+3)))*Sin[e+f*x]-(2*a*C*d-b*(c*C+B*d)*(m+3))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*d*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+3)) + 
  1/(b*(m+3))*Int[(a+b*Sin[e+f*x])^m*
    Simp[a*C*d+A*b*c*(m+3)+b*d*(C*(m+2)+A*(m+3))*Sin[e+f*x]-(2*a*C*d-b*c*C*(m+3))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && Not[RationalQ[m] && m<-1]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A-b*B+a*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(2*b*c*f*(2*m+1)) - 
  1/(2*b*c*d*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[A*(c^2*(m+1)+d^2*(2*m+n+2))-B*c*d*(m-n-1)-C*(c^2*m-d^2*(n+1))+d*((A*c+B*d)*(m+n+2)-c*C*(3*m-n))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && (RationalQ[m] && m<-1/2 || EqQ[m+n+2] && NeQ[2*m+1])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A+a*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(2*b*c*f*(2*m+1)) - 
  1/(2*b*c*d*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[A*(c^2*(m+1)+d^2*(2*m+n+2))-C*(c^2*m-d^2*(n+1))+d*(A*c*(m+n+2)-c*C*(3*m-n))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && (RationalQ[m] && m<-1/2 || EqQ[m+n+2] && NeQ[2*m+1])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+3)*Sqrt[c+d*Sin[e+f*x]]) + 
  Int[(a+b*Sin[e+f*x])^m*Simp[A+C+B*Sin[e+f*x],x]/Sqrt[c+d*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(A_.+C_.*sin[e_.+f_.*x_]^2)/Sqrt[c_.+d_.*sin[e_.+f_.*x_]],x_Symbol] :=
  -2*C*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+3)*Sqrt[c+d*Sin[e+f*x]]) + 
  (A+C)*Int[(a+b*Sin[e+f*x])^m/Sqrt[c+d*Sin[e+f*x]],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+(b*B*d*(m+n+2)-b*c*C*(2*m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && NeQ[m+n+2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))-b*c*C*(2*m+1)*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && EqQ[b*c+a*d] && EqQ[a^2-b^2] && Not[RationalQ[m] && m<-1/2] && NeQ[m+n+2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (a*A-b*B+a*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))+B*(b*c*m+a*d*(n+1))-C*(a*c*m+b*d*(n+1))+
      (d*(a*A-b*B)*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  a*(A+C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(f*(b*c-a*d)*(2*m+1)) + 
  1/(b*(b*c-a*d)*(2*m+1))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[A*(a*c*(m+1)-b*d*(2*m+n+2))-C*(a*c*m+b*d*(n+1))+
      (a*A*d*(m+n+2)+C*(b*c*(2*m+1)-a*d*(m-n-1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m<-1/2


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C-B*c*d+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(b*d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*d*(a*d*m+b*c*(n+1))+(c*C-B*d)*(a*c*m+b*d*(n+1))+b*(d*(B*c-A*d)*(m+n+2)-C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  (RationalQ[n] && n<-1 || EqQ[m+n+2])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(b*d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*d*(a*d*m+b*c*(n+1))+c*C*(a*c*m+b*d*(n+1))-b*(A*d^2*(m+n+2)+C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  (RationalQ[n] && n<-1 || EqQ[m+n+2])


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+(C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NeQ[m+n+2]


Int[(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(b*d*(m+n+2))*Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*
    Simp[A*b*d*(m+n+2)+C*(a*c*m+b*d*(n+1))+C*(a*d*m-b*c*(m+1))*Sin[e+f*x],x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NeQ[b*c-a*d] && EqQ[a^2-b^2] && NeQ[c^2-d^2] && Not[RationalQ[m] && m<-1/2] && 
  NeQ[m+n+2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C-B*c*d+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m+a*c*(n+1))+(c*C-B*d)*(b*c*m+a*d*(n+1)) - 
      (d*(A*(a*d*(n+2)-b*c*(n+1))+B*(b*d*(n+1)-a*c*(n+2)))-C*(b*c*d*(n+1)-a*(c^2+d^2*(n+1))))*Sin[e+f*x] + 
      b*(d*(B*c-A*d)*(m+n+2)-C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(c^2*C+A*d^2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(n+1)*(c^2-d^2)) + 
  1/(d*(n+1)*(c^2-d^2))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^(n+1)*
    Simp[A*d*(b*d*m+a*c*(n+1))+c*C*(b*c*m+a*d*(n+1)) - 
      (A*d*(a*d*(n+2)-b*c*(n+1))-C*(b*c*d*(n+1)-a*(c^2+d^2*(n+1))))*Sin[e+f*x] - 
      b*(A*d^2*(m+n+2)+C*(c^2*(m+1)+d^2*(n+1)))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m,n] && m>0 && n<-1


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(d*(m+n+2))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
    Simp[a*A*d*(m+n+2)+C*(b*c*m+a*d*(n+1))+
      (d*(A*b+a*B)*(m+n+2)-C*(a*c-b*d*(m+n+1)))*Sin[e+f*x]+
      (C*(a*d*m-b*c*(m+1))+b*B*d*(m+n+2))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || EqQ[a] && NeQ[c])]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -C*Cos[e+f*x]*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^(n+1)/(d*f*(m+n+2)) + 
  1/(d*(m+n+2))*Int[(a+b*Sin[e+f*x])^(m-1)*(c+d*Sin[e+f*x])^n*
    Simp[a*A*d*(m+n+2)+C*(b*c*m+a*d*(n+1))+(A*b*d*(m+n+2)-C*(a*c-b*d*(m+n+1)))*Sin[e+f*x]+C*(a*d*m-b*c*(m+1))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m>0 && 
  Not[IntegerQ[n] && n>0 && (Not[IntegerQ[m]] || EqQ[a] && NeQ[c])]


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  C/(b*d)*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] + 
  1/b*Int[(A*b+(b*B-a*C)*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,B,C},x] && NeQ[a^2-b^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  C/(b*d)*Int[Sqrt[d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] + 
  1/b*Int[(A*b-a*C*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,d,e,f,A,C},x] && NeQ[a^2-b^2]


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  C/b^2*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  1/b^2*Int[(A*b^2-a^2*C+b*(b*B-2*a*C)*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_.+b_.*sin[e_.+f_.*x_])^(3/2)*Sqrt[c_.+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  C/b^2*Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] + 
  1/b^2*Int[(A*b^2-a^2*C-2*a*b*C*Sin[e+f*x])/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2-a*b*B+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[(m+1)*(b*c-a*d)*(a*A-b*B+a*C)+d*(A*b^2-a*b*B+a^2*C)*(m+n+2) - 
      (c*(A*b^2-a*b*B+a^2*C)+(m+1)*(b*c-a*d)*(A*b-a*B+b*C))*Sin[e+f*x] - 
      d*(A*b^2-a*b*B+a^2*C)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m<-1 &&
  (EqQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || EqQ[a])])


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b^2+a^2*C)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^(n+1)/(f*(m+1)*(b*c-a*d)*(a^2-b^2)) + 
  1/((m+1)*(b*c-a*d)*(a^2-b^2))*Int[(a+b*Sin[e+f*x])^(m+1)*(c+d*Sin[e+f*x])^n*
    Simp[a*(m+1)*(b*c-a*d)*(A+C)+d*(A*b^2+a^2*C)*(m+n+2) - 
      (c*(A*b^2+a^2*C)+b*(m+1)*(b*c-a*d)*(A+C))*Sin[e+f*x] - 
      d*(A*b^2+a^2*C)*(m+n+3)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2] && RationalQ[m] && m<-1 && 
  (EqQ[a] && IntegerQ[m] && Not[IntegerQ[n]] || Not[IntegerQ[2*n] && n<-1 && (IntegerQ[n] && Not[IntegerQ[m]] || EqQ[a])])


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  C*x/(b*d) + 
  (A*b^2-a*b*B+a^2*C)/(b*(b*c-a*d))*Int[1/(a+b*Sin[e+f*x]),x] - 
  (c^2*C-B*c*d+A*d^2)/(d*(b*c-a*d))*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/((a_+b_.*sin[e_.+f_.*x_])*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  C*x/(b*d) + 
  (A*b^2+a^2*C)/(b*(b*c-a*d))*Int[1/(a+b*Sin[e+f*x]),x] - 
  (c^2*C+A*d^2)/(d*(b*c-a*d))*Int[1/(c+d*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  C/(b*d)*Int[Sqrt[a+b*Sin[e+f*x]],x] - 
  1/(b*d)*Int[Simp[a*c*C-A*b*d+(b*c*C-b*B*d+a*C*d)*Sin[e+f*x],x]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*(c_.+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
  C/(b*d)*Int[Sqrt[a+b*Sin[e+f*x]],x] - 
  1/(b*d)*Int[Simp[a*c*C-A*b*d+(b*c*C+a*C*d)*Sin[e+f*x],x]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -C*Cos[e+f*x]*Sqrt[c+d*Sin[e+f*x]]/(d*f*Sqrt[a+b*Sin[e+f*x]]) + 
  1/(2*d)*Int[1/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]])*
    Simp[2*a*A*d-C*(b*c-a*d)-2*(a*c*C-d*(A*b+a*B))*Sin[e+f*x]+(2*b*B*d-C*(b*c+a*d))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(A_.+C_.*sin[e_.+f_.*x_]^2)/(Sqrt[a_.+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
  -C*Cos[e+f*x]*Sqrt[c+d*Sin[e+f*x]]/(d*f*Sqrt[a+b*Sin[e+f*x]]) + 
  1/(2*d)*Int[1/((a+b*Sin[e+f*x])^(3/2)*Sqrt[c+d*Sin[e+f*x]])*
    Simp[2*a*A*d-C*(b*c-a*d)-2*(a*c*C-A*b*d)*Sin[e+f*x]-C*(b*c+a*d)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+B*Sin[e+f*x]+C*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,m,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(a_.+b_.*sin[e_.+f_.*x_])^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  Defer[Int][(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n*(A+C*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,c,d,e,f,A,C,m,n},x] && NeQ[b*c-a*d] && NeQ[a^2-b^2] && NeQ[c^2-d^2]


Int[(b_.*sin[e_.+f_.*x_]^p_)^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+B_.*sin[e_.+f_.*x_]+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (b*Sin[e+f*x]^p)^m/(b*Sin[e+f*x])^(m*p)*Int[(b*Sin[e+f*x])^(m*p)*(c+d*Sin[e+f*x])^n*(A+B*Sin[e+f*x]+C*Sin[e+f*x]^2),x] /;
FreeQ[{b,c,d,e,f,A,B,C,m,n,p},x] && Not[IntegerQ[m]]


Int[(b_.*cos[e_.+f_.*x_]^p_)^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+B_.*cos[e_.+f_.*x_]+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (b*Cos[e+f*x]^p)^m/(b*Cos[e+f*x])^(m*p)*Int[(b*Cos[e+f*x])^(m*p)*(c+d*Cos[e+f*x])^n*(A+B*Cos[e+f*x]+C*Cos[e+f*x]^2),x] /;
FreeQ[{b,c,d,e,f,A,B,C,m,n,p},x] && Not[IntegerQ[m]]


Int[(b_.*sin[e_.+f_.*x_]^p_)^m_*(c_.+d_.*sin[e_.+f_.*x_])^n_.*(A_.+C_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (b*Sin[e+f*x]^p)^m/(b*Sin[e+f*x])^(m*p)*Int[(b*Sin[e+f*x])^(m*p)*(c+d*Sin[e+f*x])^n*(A+C*Sin[e+f*x]^2),x] /;
FreeQ[{b,c,d,e,f,A,C,m,n,p},x] && Not[IntegerQ[m]]


Int[(b_.*cos[e_.+f_.*x_]^p_)^m_*(c_.+d_.*cos[e_.+f_.*x_])^n_.*(A_.+C_.*cos[e_.+f_.*x_]^2),x_Symbol] :=
  (b*Cos[e+f*x]^p)^m/(b*Cos[e+f*x])^(m*p)*Int[(b*Cos[e+f*x])^(m*p)*(c+d*Cos[e+f*x])^n*(A+C*Cos[e+f*x]^2),x] /;
FreeQ[{b,c,d,e,f,A,C,m,n,p},x] && Not[IntegerQ[m]]





(* ::Subsection::Closed:: *)
(*4.1.5 trig^m (a cos+b sin)^n*)


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(b*d*n) /;
FreeQ[{a,b,c,d,n},x] && EqQ[a^2+b^2,0]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -1/d*Subst[Int[(a^2+b^2-x^2)^((n-1)/2),x],x,b*Cos[c+d*x]-a*Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && PositiveIntegerQ[(n-1)/2]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(b*Cos[c+d*x]-a*Sin[c+d*x])*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*n) +
  (n-1)*(a^2+b^2)/n*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && Not[OddQ[n]] && GtQ[n,1]


Int[1/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -1/d*Subst[Int[1/(a^2+b^2-x^2),x],x,b*Cos[c+d*x]-a*Sin[c+d*x]] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]


Int[1/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^2,x_Symbol] :=
  Sin[c+d*x]/(a*d*(a*Cos[c+d*x]+b*Sin[c+d*x])) /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cos[c+d*x]-a*Sin[c+d*x])*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) +
  (n+2)/((n+1)*(a^2+b^2))*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1] && NeQ[n,-2]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a^2+b^2)^(n/2)*Int[(Cos[c+d*x-ArcTan[a,b]])^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[GeQ[n,1] || LeQ[n,-1]] && PositiveQ[a^2+b^2]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a*Cos[c+d*x]+b*Sin[c+d*x])^n/((a*Cos[c+d*x]+b*Sin[c+d*x])/Sqrt[a^2+b^2])^n*Int[Cos[c+d*x-ArcTan[a,b]]^n,x] /;
FreeQ[{a,b,c,d,n},x] && Not[GeQ[n,1] || LeQ[n,-1]] && Not[PositiveQ[a^2+b^2] || EqQ[a^2+b^2,0]]


Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -a*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)*Sin[c+d*x]^(n-1)) + 
  2*b*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/Sin[c+d*x]^(n-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && GtQ[n,1]


Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  b*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)*Cos[c+d*x]^(n-1)) + 
  2*a*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/Cos[c+d*x]^(n-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && GtQ[n,1]


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*b*d*n*Sin[c+d*x]^n) + 
  1/(2*b)*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/Sin[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && LtQ[n,0]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*a*d*n*Cos[c+d*x]^n) + 
  1/(2*a)*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/Cos[c+d*x]^(n+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && LtQ[n,0]


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*b*d*n*Sin[c+d*x]^n)*Hypergeometric2F1[1,n,n+1,(b+a*Cot[c+d*x])/(2*b)] /;
FreeQ[{a,b,c,d,n},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && Not[IntegerQ[n]]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -b*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*a*d*n*Cos[c+d*x]^n)*Hypergeometric2F1[1,n,n+1,(a+b*Tan[c+d*x])/(2*a)] /;
FreeQ[{a,b,c,d,n},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && Not[IntegerQ[n]]


Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(b+a*Cot[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && IntegerQ[n] && NeQ[a^2+b^2,0]


Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[(a+b*Tan[c+d*x])^n,x] /;
FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && IntegerQ[n] && NeQ[a^2+b^2,0]


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  1/d*Subst[Int[x^m*(a+b*x)^n/(1+x^2)^((m+n+2)/2),x],x,Tan[c+d*x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && IntegerQ[(m+n)/2] && n!=-1 && Not[n>0 && m>1]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -1/d*Subst[Int[x^m*(b+a*x)^n/(1+x^2)^((m+n+2)/2),x],x,Cot[c+d*x]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && IntegerQ[(m+n)/2] && n!=-1 && Not[n>0 && m>1]


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[sin[c+d*x]^m*(a*cos[c+d*x]+b*sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && PositiveIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*(a*cos[c+d*x]+b*sin[c+d*x])^n,x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && PositiveIntegerQ[n]


Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a^n*b^n*Int[Sin[c+d*x]^m*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-n),x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[a^2+b^2,0] && NegativeIntegerQ[n]


Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a^n*b^n*Int[Cos[c+d*x]^m*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-n),x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[a^2+b^2,0] && NegativeIntegerQ[n]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/sin[c_.+d_.*x_],x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)) + 
  b*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] + 
  a^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2)/Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/cos[c_.+d_.*x_],x_Symbol] :=
  -b*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)) + 
  a*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] + 
  b^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2)/Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1]


Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a^2+b^2)*Int[Sin[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] + 
  2*b*Int[Sin[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] + 
  a^2*Int[Sin[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && GtQ[n,1] && LtQ[m,-1]


Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(a^2+b^2)*Int[Cos[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] + 
  2*a*Int[Cos[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] + 
  b^2*Int[Cos[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && GtQ[n,1] && LtQ[m,-1]


Int[sin[c_.+d_.*x_]/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  b*x/(a^2+b^2) - 
  a/(a^2+b^2)*Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]


Int[cos[c_.+d_.*x_]/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  a*x/(a^2+b^2) + 
  b/(a^2+b^2)*Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]


Int[sin[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -a*Sin[c+d*x]^(m-1)/(d*(a^2+b^2)*(m-1)) + 
  b/(a^2+b^2)*Int[Sin[c+d*x]^(m-1),x] + 
  a^2/(a^2+b^2)*Int[Sin[c+d*x]^(m-2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && GtQ[m,1]


Int[cos[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  b*Cos[c+d*x]^(m-1)/(d*(a^2+b^2)*(m-1)) + 
  a/(a^2+b^2)*Int[Cos[c+d*x]^(m-1),x] + 
  b^2/(a^2+b^2)*Int[Cos[c+d*x]^(m-2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && GtQ[m,1]


Int[1/(sin[c_.+d_.*x_]*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  1/a*Int[Cot[c+d*x],x] - 
  1/a*Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]


Int[1/(cos[c_.+d_.*x_]*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
  1/b*Int[Tan[c+d*x],x] + 
  1/b*Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]


Int[sin[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Sin[c+d*x]^(m+1)/(a*d*(m+1)) - 
  b/a^2*Int[Sin[c+d*x]^(m+1),x] + 
  (a^2+b^2)/a^2*Int[Sin[c+d*x]^(m+2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[m,-1]


Int[cos[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  -Cos[c+d*x]^(m+1)/(b*d*(m+1)) - 
  a/b^2*Int[Cos[c+d*x]^(m+1),x] + 
  (a^2+b^2)/b^2*Int[Cos[c+d*x]^(m+2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[m,-1]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/sin[c_.+d_.*x_],x_Symbol] :=
  -(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(a*d*(n+1)) - 
  b/a^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] + 
  1/a^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2)/Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1]


Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/cos[c_.+d_.*x_],x_Symbol] :=
  (a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) - 
  a/b^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] + 
  1/b^2*Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2)/Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1]


Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a^2+b^2)/a^2*Int[Sin[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] - 
  2*b/a^2*Int[Sin[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] + 
  1/a^2*Int[Sin[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1] && LtQ[m,-1]


Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (a^2+b^2)/b^2*Int[Cos[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] - 
  2*a/b^2*Int[Cos[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] + 
  1/b^2*Int[Cos[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1] && LtQ[m,-1]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_.,x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n*(a*cos[c+d*x]+b*sin[c+d*x])^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && PositiveIntegerQ[p]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  a^p*b^p*Int[Cos[c+d*x]^m*Sin[c+d*x]^n*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-p),x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[a^2+b^2,0] && NegativeIntegerQ[p]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_./(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  b/(a^2+b^2)*Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1),x] +
  a/(a^2+b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n,x] -
  a*b/(a^2+b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^(n-1)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && IntegersQ[m,n] && m>0 && n>0


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_./(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
  Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n/(a*cos[c+d*x]+b*sin[c+d*x]),x],x] /;
FreeQ[{a,b,c,d,m,n},x] && IntegersQ[m,n]


Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
  b/(a^2+b^2)*Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(p+1),x] +
  a/(a^2+b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n*(a*Cos[c+d*x]+b*Sin[c+d*x])^(p+1),x] -
  a*b/(a^2+b^2)*Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^(n-1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^p,x] /;
FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && IntegersQ[m,n,p] && m>0 && n>0 && p<0





(* ::Subsection::Closed:: *)
(*4.1.6 (a+b cos+c sin)^n*)


Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  -2*(c*Cos[d+e*x]-b*Sin[d+e*x])/(e*Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]) /;
FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2]


Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)/(e*n) +
  a*(2*n-1)/n*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2] && RationalQ[n] && n>0


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  -(c-a*Sin[d+e*x])/(c*e*(c*Cos[d+e*x]-b*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2]


Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Int[1/Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2]


Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(2*n+1)) +
  (n+1)/(a*(2*n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2] && RationalQ[n] && n<-1


Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  b/(c*e)*Subst[Int[Sqrt[a+x]/x,x],x,b*Cos[d+e*x]+c*Sin[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[b^2+c^2]


Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Int[Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2+c^2] && PositiveQ[a+Sqrt[b^2+c^2]]


Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/Sqrt[(a+b*Cos[d+e*x]+c*Sin[d+e*x])/(a+Sqrt[b^2+c^2])]*
    Int[Sqrt[a/(a+Sqrt[b^2+c^2])+Sqrt[b^2+c^2]/(a+Sqrt[b^2+c^2])*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2] && NeQ[b^2+c^2] && Not[PositiveQ[a+Sqrt[b^2+c^2]]]


Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)/(e*n) +
  1/n*Int[Simp[n*a^2+(n-1)*(b^2+c^2)+a*b*(2*n-1)*Cos[d+e*x]+a*c*(2*n-1)*Sin[d+e*x],x]*
    (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2] && RationalQ[n] && n>1


(* Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  x/Sqrt[a^2-b^2-c^2] + 
  2/(e*Sqrt[a^2-b^2-c^2])*ArcTan[(c*Cos[d+e*x]-b*Sin[d+e*x])/(a+Sqrt[a^2-b^2-c^2]+b*Cos[d+e*x]+c*Sin[d+e*x])] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[a^2-b^2-c^2] *)


(* Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Log[RemoveContent[b^2+c^2+(a*b-c*Rt[-a^2+b^2+c^2,2])*Cos[d+e*x]+(a*c+b*Sqrt[-a^2+b^2+c^2])*Sin[d+e*x],x]]/
    (2*e*Rt[-a^2+b^2+c^2,2]) - 
  Log[RemoveContent[b^2+c^2+(a*b+c*Rt[-a^2+b^2+c^2,2])*Cos[d+e*x]+(a*c-b*Sqrt[-a^2+b^2+c^2])*Sin[d+e*x],x]]/
    (2*e*Rt[-a^2+b^2+c^2,2]) /;
FreeQ[{a,b,c,d,e},x] && NegativeQ[a^2-b^2-c^2] *)


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Module[{f=FreeFactors[Cot[(d+e*x)/2],x]},
  -f/e*Subst[Int[1/(a+c*f*x),x],x,Cot[(d+e*x)/2]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[a+b]


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Module[{f=FreeFactors[Tan[(d+e*x)/2+Pi/4],x]},
  f/e*Subst[Int[1/(a+b*f*x),x],x,Tan[(d+e*x)/2+Pi/4]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[a+c]


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Module[{f=FreeFactors[Cot[(d+e*x)/2+Pi/4],x]},
  -f/e*Subst[Int[1/(a+b*f*x),x],x,Cot[(d+e*x)/2+Pi/4]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[a-c] && NeQ[a-b]


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  Module[{f=FreeFactors[Tan[(d+e*x)/2],x]},
  2*f/e*Subst[Int[1/(a+b+2*c*f*x+(a-b)*f^2*x^2),x],x,Tan[(d+e*x)/2]/f]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2]


Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  b/(c*e)*Subst[Int[1/(x*Sqrt[a+x]),x],x,b*Cos[d+e*x]+c*Sin[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[b^2+c^2]


Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Int[1/Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2+c^2] && PositiveQ[a+Sqrt[b^2+c^2]]


Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  Sqrt[(a+b*Cos[d+e*x]+c*Sin[d+e*x])/(a+Sqrt[b^2+c^2])]/Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]*
    Int[1/Sqrt[a/(a+Sqrt[b^2+c^2])+Sqrt[b^2+c^2]/(a+Sqrt[b^2+c^2])*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2] && NeQ[b^2+c^2] && Not[PositiveQ[a+Sqrt[b^2+c^2]]]


Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^(3/2),x_Symbol] :=
  2*(c*Cos[d+e*x]-b*Sin[d+e*x])/(e*(a^2-b^2-c^2)*Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]) +
  1/(a^2-b^2-c^2)*Int[Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2]


Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (-c*Cos[d+e*x]+b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/(e*(n+1)*(a^2-b^2-c^2)) +
  1/((n+1)*(a^2-b^2-c^2))*
    Int[(a*(n+1)-b*(n+2)*Cos[d+e*x]-c*(n+2)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2] && RationalQ[n] && n<-1 && n!=-3/2


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-b*B-c*C)*x/(2*a^2) - (b*B+c*C)*(b*Cos[d+e*x]-c*Sin[d+e*x])/(2*a*b*c*e) + 
  (a^2*(b*B-c*C)-2*a*A*b^2+b^2*(b*B+c*C))*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*b*c*e) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && EqQ[b^2+c^2]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-c*C)*x/(2*a^2) - C*Cos[d+e*x]/(2*a*e) + c*C*Sin[d+e*x]/(2*a*b*e) + 
  (-a^2*C+2*a*c*A+b^2*C)*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*b*e) /;
FreeQ[{a,b,c,d,e,A,C},x] && EqQ[b^2+c^2]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-b*B)*x/(2*a^2) - b*B*Cos[d+e*x]/(2*a*c*e) + B*Sin[d+e*x]/(2*a*e) + 
  (a^2*B-2*a*b*A+b^2*B)*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*c*e) /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2+c^2]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (b*B+c*C)*x/(b^2+c^2) + (c*B-b*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NeQ[b^2+c^2] && EqQ[A*(b^2+c^2)-a*(b*B+c*C)]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  c*C*x/(b^2+c^2) - b*C*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,C},x] && NeQ[b^2+c^2] && EqQ[A*(b^2+c^2)-a*c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  b*B*x/(b^2+c^2) + c*B*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2+c^2] && EqQ[A*(b^2+c^2)-a*b*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  (b*B+c*C)*x/(b^2+c^2) + (c*B-b*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  (A*(b^2+c^2)-a*(b*B+c*C))/(b^2+c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NeQ[b^2+c^2] && NeQ[A*(b^2+c^2)-a*(b*B+c*C)]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  c*C*(d+e*x)/(e*(b^2+c^2)) - b*C*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  (A*(b^2+c^2)-a*c*C)/(b^2+c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,C},x] && NeQ[b^2+c^2] && NeQ[A*(b^2+c^2)-a*c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
  b*B*(d+e*x)/(e*(b^2+c^2)) +
  c*B*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  (A*(b^2+c^2)-a*b*B)/(b^2+c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2+c^2] && NeQ[A*(b^2+c^2)-a*b*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
FreeQ[{a,b,c,d,e,A,B,C,n},x] && NeQ[n+1] && EqQ[a^2-b^2-c^2] && EqQ[(b*B+c*C)*n+a*A*(n+1)]


Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
FreeQ[{a,b,c,d,e,A,C,n},x] && NeQ[n+1] && EqQ[a^2-b^2-c^2] && EqQ[c*C*n+a*A*(n+1)]


Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
FreeQ[{a,b,c,d,e,A,B,n},x] && NeQ[n+1] && EqQ[a^2-b^2-c^2] && EqQ[b*B*n+a*A*(n+1)]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  ((b*B+c*C)*n+a*A*(n+1))/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,C,n},x] && NeQ[n+1] && EqQ[a^2-b^2-c^2] && NeQ[(b*B+c*C)*n+a*A*(n+1)]


Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  (c*C*n+a*A*(n+1))/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,C,n},x] && NeQ[n+1] && EqQ[a^2-b^2-c^2] && NeQ[c*C*n+a*A*(n+1)]


Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  (b*B*n+a*A*(n+1))/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e,A,B,n},x] && NeQ[n+1] && EqQ[a^2-b^2-c^2] && NeQ[b*B*n+a*A*(n+1)]


Int[(B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (c*B-b*C)*(b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/(e*(n+1)*(b^2+c^2)) /;
FreeQ[{b,c,d,e,B,C},x] && NeQ[n+1] && NeQ[b^2+c^2] && EqQ[b*B+c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  1/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
	Simp[a*(b*B+c*C)*n+a^2*A*(n+1)+
      (n*(a^2*B-B*c^2+b*c*C)+a*b*A*(n+1))*Cos[d+e*x]+
      (n*(b*B*c+a^2*C-b^2*C)+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && RationalQ[n] && n>0 && NeQ[a^2-b^2-c^2]


Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  1/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
    Simp[a*c*C*n+a^2*A*(n+1)+(c*b*C*n+a*b*A*(n+1))*Cos[d+e*x]+(a^2*C*n-b^2*C*n+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,C},x] && RationalQ[n] && n>0 && NeQ[a^2-b^2-c^2]


Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
  (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  1/(a*(n+1))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
    Simp[a*b*B*n+a^2*A*(n+1)+(a^2*B*n-c^2*B*n+a*b*A*(n+1))*Cos[d+e*x]+(b*c*B*n+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && RationalQ[n] && n>0 && NeQ[a^2-b^2-c^2]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
  B/b*Int[Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] +
  (A*b-a*B)/b*Int[1/Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && EqQ[B*c-b*C] && NeQ[A*b-a*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/
    (e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NeQ[a^2-b^2-c^2] && EqQ[a*A-b*B-c*C]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  -(b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,C},x] && NeQ[a^2-b^2-c^2] && EqQ[a*A-c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[a^2-b^2-c^2] && EqQ[a*A-b*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/
    (e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  (a*A-b*B-c*C)/(a^2-b^2-c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NeQ[a^2-b^2-c^2] && NeQ[a*A-b*B-c*C]


Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  -(b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  (a*A-c*C)/(a^2-b^2-c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,C},x] && NeQ[a^2-b^2-c^2] && NeQ[a*A-c*C]


Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  (a*A-b*B)/(a^2-b^2-c^2)*Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[a^2-b^2-c^2] && NeQ[a*A-b*B]


Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  1/((n+1)*(a^2-b^2-c^2))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
    Simp[(n+1)*(a*A-b*B-c*C)+(n+2)*(a*B-b*A)*Cos[d+e*x]+(n+2)*(a*C-c*A)*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && RationalQ[n] && n<-1 && NeQ[a^2-b^2-c^2] && n!=-2


Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  1/((n+1)*(a^2-b^2-c^2))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
    Simp[(n+1)*(a*A-c*C)-(n+2)*b*A*Cos[d+e*x]+(n+2)*(a*C-c*A)*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,C},x] && RationalQ[n] && n<-1 && NeQ[a^2-b^2-c^2] && n!=-2


Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  1/((n+1)*(a^2-b^2-c^2))*Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
    Simp[(n+1)*(a*A-b*B)+(n+2)*(a*B-b*A)*Cos[d+e*x]-(n+2)*c*A*Sin[d+e*x],x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && RationalQ[n] && n<-1 && NeQ[a^2-b^2-c^2] && n!=-2


Int[1/(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]),x_Symbol] :=
  Int[Cos[d+e*x]/(b+a*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
FreeQ[{a,b,c,d,e},x]


Int[1/(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]),x_Symbol] :=
  Int[Sin[d+e*x]/(b+a*Sin[d+e*x]+c*Cos[d+e*x]),x] /;
FreeQ[{a,b,c,d,e},x]


Int[cos[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^n_.,x_Symbol] :=
  Int[(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[n]


Int[sin[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^n_.,x_Symbol] :=
  Int[(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[n]


Int[cos[d_.+e_.*x_]^n_*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^n_,x_Symbol] :=
  Cos[d+e*x]^n*(a+b*Sec[d+e*x]+c*Tan[d+e*x])^n/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n*Int[(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[sin[d_.+e_.*x_]^n_*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^n_,x_Symbol] :=
  Sin[d+e*x]^n*(a+b*Csc[d+e*x]+c*Cot[d+e*x])^n/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n*Int[(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && Not[IntegerQ[n]]


Int[sec[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^m_,x_Symbol] :=
  Int[1/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[m+n] && IntegerQ[n]


Int[csc[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^m_,x_Symbol] :=
  Int[1/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[m+n] && IntegerQ[n]


Int[sec[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^m_,x_Symbol] :=
  Sec[d+e*x]^n*(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n/(a+b*Sec[d+e*x]+c*Tan[d+e*x])^n*Int[1/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[m+n] && Not[IntegerQ[n]]


Int[csc[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^m_,x_Symbol] :=
  Csc[d+e*x]^n*(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n/(a+b*Csc[d+e*x]+c*Cot[d+e*x])^n*Int[1/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[m+n] && Not[IntegerQ[n]]





(* ::Subsection::Closed:: *)
(*4.1.7 (d trig)^m (a+b (c sin)^n)^p*)


Int[(a_+b_.*sin[e_.+f_.*x_]^2)*(A_.+B_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  (4*A*(2*a+b)+B*(4*a+3*b))*x/8 - 
  (4*A*b+B*(4*a+3*b))*Cos[e+f*x]*Sin[e+f*x]/(8*f) - 
  b*B*Cos[e+f*x]*Sin[e+f*x]^3/(4*f) /;
FreeQ[{a,b,e,f,A,B},x]


Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_*(A_.+B_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -B*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x]^2)^p/(2*f*(p+1)) + 
  1/(2*(p+1))*Int[(a+b*Sin[e+f*x]^2)^(p-1)*
    Simp[a*B+2*a*A*(p+1)+(2*A*b*(p+1)+B*(b+2*a*p+2*b*p))*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B},x] && GtQ[p,0]


Int[(A_.+B_.*sin[e_.+f_.*x_]^2)/(a_+b_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  B*x/b + (A*b-a*B)/b*Int[1/(a+b*Sin[e+f*x]^2),x] /;
FreeQ[{a,b,e,f,A,B},x]


Int[(A_.+B_.*sin[e_.+f_.*x_]^2)/Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
  B/b*Int[Sqrt[a+b*Sin[e+f*x]^2],x] + (A*b-a*B)/b*Int[1/Sqrt[a+b*Sin[e+f*x]^2],x] /;
FreeQ[{a,b,e,f,A,B},x]


Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_*(A_.+B_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  -(A*b-a*B)*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x]^2)^(p+1)/(2*a*f*(a+b)*(p+1)) - 
  1/(2*a*(a+b)*(p+1))*Int[(a+b*Sin[e+f*x]^2)^(p+1)*
    Simp[a*B-A*(2*a*(p+1)+b*(2*p+3))+2*(A*b-a*B)*(p+2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f,A,B},x] && LtQ[p,-1] && NeQ[a+b,0]


Int[(a_.+b_.*sin[e_.+f_.*x_]^2)^p_*(A_.+B_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff*(a+b*Sin[e+f*x]^2)^p*(Sec[e+f*x]^2)^p/(f*(a+(a+b)*Tan[e+f*x]^2)^p)*
    Subst[Int[(a+(a+b)*ff^2*x^2)^p*(A+(A+B)*ff^2*x^2)/(1+ff^2*x^2)^(p+2),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,A,B},x] && Not[IntegerQ[p]]


Int[u_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  a^p*Int[ActivateTrig[u*cos[e+f*x]^(2*p)],x] /;
FreeQ[{a,b,e,f,p},x] && EqQ[a+b,0] && IntegerQ[p]


Int[u_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  Int[ActivateTrig[u*(a*cos[e+f*x]^2)^p],x] /;
FreeQ[{a,b,e,f,p},x] && EqQ[a+b,0]


Int[(b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  -Cot[e+f*x]*(b*Sin[e+f*x]^2)^p/(2*f*p) + 
  b*(2*p-1)/(2*p)*Int[(b*Sin[e+f*x]^2)^(p-1),x] /;
FreeQ[{b,e,f},x] && Not[IntegerQ[p]] && GtQ[p,1]


Int[(b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  Cot[e+f*x]*(b*Sin[e+f*x]^2)^(p+1)/(b*f*(2*p+1)) + 
  2*(p+1)/(b*(2*p+1))*Int[(b*Sin[e+f*x]^2)^(p+1),x] /;
FreeQ[{b,e,f},x] && Not[IntegerQ[p]] && LtQ[p,-1]


Int[tan[e_.+f_.*x_]^m_.*(b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x]^2,x]},
  ff^((m+1)/2)/(2*f)*Subst[Int[x^((m-1)/2)*(b*ff^(n/2)*x^(n/2))^p/(1-ff*x)^((m+1)/2),x],x,Sin[e+f*x]^2/ff]] /;
FreeQ[{b,e,f,p},x] && IntegerQ[(m-1)/2] && IntegerQ[n/2]


Int[tan[e_.+f_.*x_]^m_.*(b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x],x]},
  ff^(m+1)/f*Subst[Int[x^m*(b*(c*ff*x)^n)^p/(1-ff^2*x^2)^((m+1)/2),x],x,Sin[e+f*x]/ff]] /;
FreeQ[{b,c,e,f,n,p},x] && ILtQ[(m-1)/2,0]


Int[u_.*(b_.*sin[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x],x]},
  (b*ff^n)^IntPart[p]*(b*Sin[e+f*x]^n)^FracPart[p]/(Sin[e+f*x]/ff)^(n*FracPart[p])*
    Int[ActivateTrig[u]*(Sin[e+f*x]/ff)^(n*p),x]] /;
FreeQ[{b,e,f,n,p},x] && Not[IntegerQ[p]] && IntegerQ[n] && 
  (EqQ[u,1] || MatchQ[u,(d_.*trig_[e+f*x])^m_. /; FreeQ[{d,m},x] && MemberQ[{sin,cos,tan,cot,sec,csc},trig]])


Int[u_.*(b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  b^IntPart[p]*(b*(c*Sin[e+f*x])^n)^FracPart[p]/(c*Sin[e+f*x])^(n*FracPart[p])*
    Int[ActivateTrig[u]*(c*Sin[e+f*x])^(n*p),x] /;
FreeQ[{b,c,e,f,n,p},x] && Not[IntegerQ[p]] && Not[IntegerQ[n]] && 
  (EqQ[u,1] || MatchQ[u,(d_.*trig_[e+f*x])^m_. /; FreeQ[{d,m},x] && MemberQ[{sin,cos,tan,cot,sec,csc},trig]])


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
  Sqrt[a]/f*EllipticE[e+f*x,-b/a] /;
FreeQ[{a,b,e,f},x] && GtQ[a,0]


Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
  Sqrt[a+b*Sin[e+f*x]^2]/Sqrt[1+b*Sin[e+f*x]^2/a]*Int[Sqrt[1+(b*Sin[e+f*x]^2)/a],x] /;
FreeQ[{a,b,e,f},x] && Not[GtQ[a,0]]


Int[(a_+b_.*sin[e_.+f_.*x_]^2)^2,x_Symbol] :=
  (8*a^2+8*a*b+3*b^2)*x/8 - 
  b*(8*a+3*b)*Cos[e+f*x]*Sin[e+f*x]/(8*f) - 
  b^2*Cos[e+f*x]*Sin[e+f*x]^3/(4*f) /;
FreeQ[{a,b,e,f},x]


Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  -b*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x]^2)^(p-1)/(2*f*p) + 
  1/(2*p)*Int[(a+b*Sin[e+f*x]^2)^(p-2)*Simp[a*(b+2*a*p)+b*(2*a+b)*(2*p-1)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f},x] && NeQ[a+b,0] && GtQ[p,1]


Int[1/(a_+b_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[1/(a+(a+b)*ff^2*x^2),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x]


Int[1/Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
  1/(Sqrt[a]*f)*EllipticF[e+f*x,-b/a] /;
FreeQ[{a,b,e,f},x] && GtQ[a,0]


Int[1/Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
  Sqrt[1+b*Sin[e+f*x]^2/a]/Sqrt[a+b*Sin[e+f*x]^2]*Int[1/Sqrt[1+(b*Sin[e+f*x]^2)/a],x] /;
FreeQ[{a,b,e,f},x] && Not[GtQ[a,0]]


Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  -b*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x]^2)^(p+1)/(2*a*f*(p+1)*(a+b)) + 
  1/(2*a*(p+1)*(a+b))*Int[(a+b*Sin[e+f*x]^2)^(p+1)*Simp[2*a*(p+1)+b*(2*p+3)-2*b*(p+2)*Sin[e+f*x]^2,x],x] /;
FreeQ[{a,b,e,f},x] && NeQ[a+b,0] && LtQ[p,-1]


Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff*(a+b*Sin[e+f*x]^2)^p*(Sec[e+f*x]^2)^p/(f*(a+(a+b)*Tan[e+f*x]^2)^p)*
    Subst[Int[(a+(a+b)*ff^2*x^2)^p/(1+ff^2*x^2)^(p+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && Not[IntegerQ[p]]


(* Int[(a_+b_.*sin[e_.+f_.*x_]^4)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  -ff/f*Subst[Int[(a+b+2*a*ff^2*x^2+a*ff^4*x^4)^p/(1+ff^2*x^2)^(2*p+1),x],x,Cot[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[p] *)


Int[(a_+b_.*sin[e_.+f_.*x_]^4)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(a+2*a*ff^2*x^2+(a+b)*ff^4*x^4)^p/(1+ff^2*x^2)^(2*p+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[p]


Int[(a_+b_.*sin[e_.+f_.*x_]^4)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff*(a+b*Sin[e+f*x]^4)^p*(Sec[e+f*x]^2)^(2*p)/(f*(a+2*a*Tan[e+f*x]^2+(a+b)*Tan[e+f*x]^4)^p)*
    Subst[Int[(a+2*a*ff^2*x^2+(a+b)*ff^4*x^4)^p/(1+ff^2*x^2)^(2*p+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[p-1/2]


Int[1/(a_+b_.*sin[e_.+f_.*x_]^n_),x_Symbol] :=
  Module[{k},
  Dist[2/(a*n),Sum[Int[1/(1-Sin[e+f*x]^2/((-1)^(4*k/n)*Rt[-a/b,n/2])),x],{k,1,n/2}],x]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[n/2]


(* Int[(a_+b_.*sin[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  -ff/f*Subst[Int[(b+a*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2)^(n*p/2+1),x],x,Cot[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[n/2] && IGtQ[p,0] *)


Int[(a_+b_.*sin[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(b*ff^n*x^n+a*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2)^(n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[n/2] && IGtQ[p,0]


Int[(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[(a+b*(c*sin[e+f*x])^n)^p,x],x] /;
FreeQ[{a,b,c,e,f,n},x] && (IGtQ[p,0] || EqQ[p,-1] && IntegerQ[n])


Int[(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  Defer[Int][(a+b*(c*Sin[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,e,f,n,p},x]


Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Cos[e+f*x],x]},
  -ff/f*Subst[Int[(1-ff^2*x^2)^((m-1)/2)*ExpandToSum[a+b*(1-ff^2*x^2)^(n/2),x]^p,x],x,Cos[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2] && (EqQ[n,2] || EqQ[n,4])


Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Cos[e+f*x],x]},
  -ff/f*Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b*(1-ff^2*x^2)^(n/2))^p,x],x,Cos[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2] && IntegerQ[n/2]


Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff^(m+1)/f*Subst[Int[x^m*ExpandToSum[a*(1+ff^2*x^2)^(n/2)+b*ff^n*x^n,x]^p/(1+ff^2*x^2)^(m/2+n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && (EqQ[n,2] || EqQ[n,4]) && IntegerQ[p]


Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff^(m+1)/f*Subst[Int[x^m*(a*(1+ff^2*x^2)^(n/2)+b*ff^n*x^n)^p/(1+ff^2*x^2)^(m/2+n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[n/2] && IntegerQ[p]


Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff^(m+1)*(a+b*Sin[e+f*x]^n)^p*(Sec[e+f*x]^2)^(n*p/2)/(f*Apart[a*(1+Tan[e+f*x]^2)^(n/2)+b*Tan[e+f*x]^n]^p)*
    Subst[Int[x^m*ExpandToSum[a*(1+ff^2*x^2)^(n/2)+b*ff^n*x^n,x]^p/(1+ff^2*x^2)^(m/2+n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[m/2] && (EqQ[n,2] || EqQ[n,4] && IntegerQ[p-1/2])


Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  Int[ExpandTrig[sin[e+f*x]^m*(a+b*sin[e+f*x]^n)^p,x],x] /;
FreeQ[{a,b,e,f},x] && IntegersQ[m,p] && (EqQ[n,2] || EqQ[n,4] || p>0 || p==-1 && IntegerQ[n])


Int[(d_.*sin[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Int[ExpandTrig[(d*sin[e+f*x])^m*(a+b*(c*sin[e+f*x])^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0]


Int[(d_.*sin[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Defer[Int][(d*Sin[e+f*x])^m*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[cos[e_.+f_.*x_]^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x],x]},
  ff/f*Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b*(c*ff*x)^n)^p,x],x,Sin[e+f*x]/ff]] /;
FreeQ[{a,b,c,e,f,n,p},x] && IntegerQ[(m-1)/2] && (EqQ[n,2] || EqQ[n,4] || m>0 || IGtQ[p,0] || IntegersQ[m,p])


Int[cos[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[ExpandToSum[b*ff^n*x^n+a*(1+ff^2*x^2)^(n/2),x]^p/(1+ff^2*x^2)^(m/2+n*(p/2)+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && (EqQ[n,2] || EqQ[n,4]) && IntegerQ[p]


Int[cos[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(b*ff^n*x^n+a*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2)^(m/2+n*(p/2)+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[n/2] && IntegerQ[p]


Int[cos[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff*(a+b*Sin[e+f*x]^2)^p*(Sec[e+f*x]^2)^p/(f*(a+(a+b)*Tan[e+f*x]^2)^p)*
    Subst[Int[(a+(a+b)*ff^2*x^2)^p/(1+ff^2*x^2)^(m/2+p+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[m/2] && Not[IntegerQ[p]]


Int[cos[e_.+f_.*x_]^m_/(a_+b_.*sin[e_.+f_.*x_]^n_),x_Symbol] :=
  Int[Expand[(1-Sin[e+f*x]^2)^(m/2)/(a+b*Sin[e+f*x]^n),x],x] /;
FreeQ[{a,b,e,f},x] && IGtQ[m/2,0] && IntegerQ[(n-1)/2]


(* Int[cos[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  Int[ExpandTrig[(1-sin[e+f*x]^2)^(m/2)*(a+b*sin[e+f*x]^n)^p,x],x] /;
FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[(n-1)/2] && IntegerQ[p] && m<0 && p<-1 *)


Int[(d_.*cos[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Int[ExpandTrig[(d*cos[e+f*x])^m*(a+b*(c*sin[e+f*x])^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0]


Int[(d_.*cos[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Defer[Int][(d*Cos[e+f*x])^m*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[tan[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x]^2,x]},
  ff^((m+1)/2)/(2*f)*Subst[Int[x^((m-1)/2)*(a+b*ff^(n/2)*x^(n/2))^p/(1-ff*x)^((m+1)/2),x],x,Sin[e+f*x]^2/ff]] /;
FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2] && IntegerQ[n/2]


Int[tan[e_.+f_.*x_]^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Sin[e+f*x],x]},
  ff^(m+1)/f*Subst[Int[x^m*(a+b*(c*ff*x)^n)^p/(1-ff^2*x^2)^((m+1)/2),x],x,Sin[e+f*x]/ff]] /;
FreeQ[{a,b,c,e,f,n,p},x] && ILtQ[(m-1)/2,0]


Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff/f*Subst[Int[(d*ff*x)^m*ExpandToSum[a*(1+ff^2*x^2)^(n/2)+b*ff^n*x^n,x]^p/(1+ff^2*x^2)^(n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,d,e,f,m},x] && (EqQ[n,2] || EqQ[n,4]) && IntegerQ[p]


Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff*(a+b*Sin[e+f*x]^n)^p*(Sec[e+f*x]^2)^(n*p/2)/(f*Apart[a*(1+Tan[e+f*x]^2)^(n/2)+b*Tan[e+f*x]^n]^p)*
    Subst[Int[(d*ff*x)^m*ExpandToSum[a*(1+ff^2*x^2)^(n/2)+b*ff^n*x^n,x]^p/(1+ff^2*x^2)^(n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,d,e,f,m},x] && (EqQ[n,2] || EqQ[n,4] && IntegerQ[p-1/2]) && Not[IntegerQ[p]]


Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
  With[{ff=FreeFactors[Tan[e+f*x],x]},
  ff^(m+1)/f*Subst[Int[(d*x)^m*(b*ff^n*x^n+a*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2)^(n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
FreeQ[{a,b,d,e,f,m},x] && IntegerQ[n/2] && IGtQ[p,0]


Int[(d_.*tan[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Int[ExpandTrig[(d*tan[e+f*x])^m*(a+b*(c*sin[e+f*x])^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0]


Int[(d_.*tan[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
  Defer[Int][(d*Tan[e+f*x])^m*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[(d_.*cot[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  (d*Cot[e+f*x])^FracPart[m]*(Tan[e+f*x]/d)^FracPart[m]*Int[(Tan[e+f*x]/d)^(-m)*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]


Int[(d_.*sec[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  (d*Sec[e+f*x])^FracPart[m]*(Cos[e+f*x]/d)^FracPart[m]*Int[(Cos[e+f*x]/d)^(-m)*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]


Int[(d_.*csc[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^n_.)^p_.,x_Symbol] :=
  d^(n*p)*Int[(d*Csc[e+f*x])^(m-n*p)*(b+a*Csc[e+f*x]^n)^p,x] /;
FreeQ[{a,b,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && IntegersQ[n,p]


Int[(d_.*csc[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
  (d*Csc[e+f*x])^FracPart[m]*(Sin[e+f*x]/d)^FracPart[m]*Int[(Sin[e+f*x]/d)^(-m)*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]





(* ::Subsection::Closed:: *)
(*4.1.8 trig^m (a+b cos^p+c sin^q)^n*)


Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<p<=q


Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<p<=q


Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
    Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<q<p


Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
    Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<q<p


Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<p<=q


Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<p<=q


Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
    Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<q<p


Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
    Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EvenQ[m] && EvenQ[p] && EvenQ[q] && IntegerQ[n] && 0<q<p





(* ::Subsection::Closed:: *)
(*4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p*)


Int[(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[u*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[u*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[1/(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Sin[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Sin[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c]


Int[1/(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(b-q+2*c*Cos[d+e*x]^n),x] - 
  2*c/q*Int[1/(b+q+2*c*Cos[d+e*x]^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Sin[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  1/(4^p*c^p)*Int[Cos[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[Sin[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[Cos[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f/e*Subst[Int[ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f/e*Subst[Int[ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  Int[ExpandTrig[sin[d+e*x]^m*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && IntegersQ[m,n,p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  Int[ExpandTrig[cos[d+e*x]^m*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && IntegersQ[m,n,p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*sin[d_.+e_.*x_])^n_.+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p,x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[n2-2*n] && OddQ[m]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*(f_.*cos[d_.+e_.*x_])^n_.+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p,x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[n2-2*n] && OddQ[m]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Cos[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Sin[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[Cos[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[sin[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[Sin[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cos[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c+b*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(m/2+n*p+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[cos[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[(1-sin[d+e*x]^2)^(m/2)*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && IntegersQ[n,p]


Int[sin[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[(1-cos[d+e*x]^2)^(m/2)*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && IntegersQ[n,p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*sin[d_.+e_.*x_])^n_+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g^(m+1)/e*Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1-g^2*x^2)^((m+1)/2),x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n},x] && OddQ[m] && IntegerQ[2*p]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*cos[d_.+e_.*x_])^n_+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g^(m+1)/e*Subst[Int[x^m*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/(1-g^2*x^2)^((m+1)/2),x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n},x] && OddQ[m] && IntegerQ[2*p]


Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Tan[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Cot[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[Tan[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[Cot[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c*x^(2*n)+b*x^n*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[n2-2*n] && Not[OddQ[m]] && NeQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c*x^(2*n)+b*x^n*(1+x^2)^(n/2)+a*(1+x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[n2-2*n] && Not[OddQ[m]] && NeQ[b^2-4*a*c] && EvenQ[n] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[sin[d+e*x]^m*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p/(1-sin[d+e*x]^2)^(m/2),x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && IntegersQ[n,p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[cos[d+e*x]^m*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p/(1-cos[d+e*x]^2)^(m/2),x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && IntegersQ[n,p]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*sin[d_.+e_.*x_])^n_+c_.*(f_.*sin[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Sin[d+e*x],x]},
  g^(m+1)/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/x^m,x],x,Sin[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n},x] && OddQ[m] && IntegerQ[2*p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*(f_.*cos[d_.+e_.*x_])^n_+c_.*(f_.*cos[d_.+e_.*x_])^n2_.)^p_.,x_Symbol] :=
  Module[{g=FreeFactors[Cos[d+e*x],x]},
  -g^(m+1)/e*Subst[Int[(1-g^2*x^2)^((m-1)/2)*(a+b*(f*g*x)^n+c*(f*g*x)^(2*n))^p/x^m,x],x,Cos[d+e*x]/g]] /;
FreeQ[{a,b,c,d,e,f,n},x] && OddQ[m] && IntegerQ[2*p]


Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Cot[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  1/(4^p*c^p)*Int[Tan[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Sin[d+e*x]^n+c*Sin[d+e*x]^(2*n))^p/(b+2*c*Sin[d+e*x]^n)^(2*p)*Int[Cot[d+e*x]^m*(b+2*c*Sin[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[tan[d_.+e_.*x_]^m_*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_,x_Symbol] :=
  (a+b*Cos[d+e*x]^n+c*Cos[d+e*x]^(2*n))^p/(b+2*c*Cos[d+e*x]^n)^(2*p)*Int[Tan[d+e*x]^m*(b+2*c*Cos[d+e*x]^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && Not[OddQ[m]] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[cot[d_.+e_.*x_]^m_.*(a_+b_.*sin[d_.+e_.*x_]^n_+c_.*sin[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Cot[d+e*x],x]},
  -f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c+b*(1+f^2*x^2)^(n/2)+a*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Cot[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[n2-2*n] && EvenQ[n] && IntegerQ[p]


Int[tan[d_.+e_.*x_]^m_.*(a_+b_.*cos[d_.+e_.*x_]^n_+c_.*cos[d_.+e_.*x_]^n2_)^p_.,x_Symbol] :=
  Module[{f=FreeFactors[Tan[d+e*x],x]},
  f^(m+1)/e*Subst[Int[x^m*ExpandToSum[c+b*(1+f^2*x^2)^(n/2)+a*(1+f^2*x^2)^n,x]^p/(1+f^2*x^2)^(n*p+1),x],x,Tan[d+e*x]/f]] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[n2-2*n] && EvenQ[n] && IntegerQ[p]


Int[cot[d_.+e_.*x_]^m_.*(a_.+b_.*sin[d_.+e_.*x_]^n_.+c_.*sin[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[(1-sin[d+e*x]^2)^(m/2)*(a+b*sin[d+e*x]^n+c*sin[d+e*x]^(2*n))^p/sin[d+e*x]^m,x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && IntegersQ[n,p]


Int[tan[d_.+e_.*x_]^m_.*(a_.+b_.*cos[d_.+e_.*x_]^n_.+c_.*cos[d_.+e_.*x_]^n2_.)^p_.,x_Symbol] :=
  Int[ExpandTrig[(1-cos[d+e*x]^2)^(m/2)*(a+b*cos[d+e*x]^n+c*cos[d+e*x]^(2*n))^p/cos[d+e*x]^m,x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && EvenQ[m] && NeQ[b^2-4*a*c] && IntegersQ[n,p]


Int[(A_+B_.*sin[d_.+e_.*x_])*(a_+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Sin[d+e*x])*(b+2*c*Sin[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  1/(4^n*c^n)*Int[(A+B*Cos[d+e*x])*(b+2*c*Cos[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*sin[d_.+e_.*x_])*(a_+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Sin[d+e*x]+c*Sin[d+e*x]^2)^n/(b+2*c*Sin[d+e*x])^(2*n)*Int[(A+B*Sin[d+e*x])*(b+2*c*Sin[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  (a+b*Cos[d+e*x]+c*Cos[d+e*x]^2)^n/(b+2*c*Cos[d+e*x])^(2*n)*Int[(A+B*Cos[d+e*x])*(b+2*c*Cos[d+e*x])^(2*n),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2-4*a*c] && Not[IntegerQ[n]]


Int[(A_+B_.*sin[d_.+e_.*x_])/(a_.+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Sin[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c]


Int[(A_+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (B+(b*B-2*A*c)/q)*Int[1/(b+q+2*c*Cos[d+e*x]),x] + 
  (B-(b*B-2*A*c)/q)*Int[1/(b-q+2*c*Cos[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c]


Int[(A_+B_.*sin[d_.+e_.*x_])*(a_.+b_.*sin[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*sin[d+e*x])*(a+b*sin[d+e*x]+c*sin[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c] && IntegerQ[n]


Int[(A_+B_.*cos[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*cos[d_.+e_.*x_]^2)^n_,x_Symbol] :=
  Int[ExpandTrig[(A+B*cos[d+e*x])*(a+b*cos[d+e*x]+c*cos[d+e*x]^2)^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2-4*a*c] && IntegerQ[n]





(* ::Subsection::Closed:: *)
(*4.1.10 (c+d x)^m (a+b sin)^n*)


Int[(c_.+d_.*x_)^m_.*sin[e_.+f_.*x_],x_Symbol] :=
  -(c+d*x)^m*Cos[e+f*x]/f + 
  d*m/f*Int[(c+d*x)^(m-1)*Cos[e+f*x],x] /;
FreeQ[{c,d,e,f},x] && RationalQ[m] && m>0


Int[(c_.+d_.*x_)^m_*sin[e_.+f_.*x_],x_Symbol] :=
  (c+d*x)^(m+1)*Sin[e+f*x]/(d*(m+1)) -
  f/(d*(m+1))*Int[(c+d*x)^(m+1)*Cos[e+f*x],x] /;
FreeQ[{c,d,e,f},x] && RationalQ[m] && m<-1


Int[sin[e_.+f_.*Complex[0,fz_]*x_]/(c_.+d_.*x_),x_Symbol] :=
  I*SinhIntegral[c*f*fz/d+f*fz*x]/d /;
FreeQ[{c,d,e,f,fz},x] && EqQ[d*e-c*f*fz*I]


Int[sin[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  SinIntegral[e+f*x]/d /;
FreeQ[{c,d,e,f},x] && EqQ[d*e-c*f]


Int[sin[e_.+f_.*Complex[0,fz_]*x_]/(c_.+d_.*x_),x_Symbol] :=
  CoshIntegral[-c*f*fz/d-f*fz*x]/d /;
FreeQ[{c,d,e,f,fz},x] && EqQ[d*(e-Pi/2)-c*f*fz*I] && NegQ[c*f*fz/d]


Int[sin[e_.+f_.*Complex[0,fz_]*x_]/(c_.+d_.*x_),x_Symbol] :=
  CoshIntegral[c*f*fz/d+f*fz*x]/d /;
FreeQ[{c,d,e,f,fz},x] && EqQ[d*(e-Pi/2)-c*f*fz*I]


Int[sin[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  CosIntegral[e-Pi/2+f*x]/d /;
FreeQ[{c,d,e,f},x] && EqQ[d*(e-Pi/2)-c*f]


Int[sin[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
  Cos[(d*e-c*f)/d]*Int[Sin[c*f/d+f*x]/(c+d*x),x] + 
  Sin[(d*e-c*f)/d]*Int[Cos[c*f/d+f*x]/(c+d*x),x] /;
FreeQ[{c,d,e,f},x] && NeQ[d*e-c*f]


Int[sin[e_.+Pi/2+f_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  2/d*Subst[Int[Cos[f*x^2/d],x],x,Sqrt[c+d*x]] /;
FreeQ[{c,d,e,f},x] && ComplexFreeQ[f] && EqQ[d*e-c*f]


Int[sin[e_.+f_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  2/d*Subst[Int[Sin[f*x^2/d],x],x,Sqrt[c+d*x]] /;
FreeQ[{c,d,e,f},x] && ComplexFreeQ[f] && EqQ[d*e-c*f]


Int[sin[e_.+f_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  Cos[(d*e-c*f)/d]*Int[Sin[c*f/d+f*x]/Sqrt[c+d*x],x] + 
  Sin[(d*e-c*f)/d]*Int[Cos[c*f/d+f*x]/Sqrt[c+d*x],x] /;
FreeQ[{c,d,e,f},x] && ComplexFreeQ[f] && NeQ[d*e-c*f]


Int[(c_.+d_.*x_)^m_.*sin[e_.+k_.*Pi+f_.*x_],x_Symbol] :=
  I/2*Int[(c+d*x)^m*E^(-I*k*Pi)*E^(-I*(e+f*x)),x] - I/2*Int[(c+d*x)^m*E^(I*k*Pi)*E^(I*(e+f*x)),x] /;
FreeQ[{c,d,e,f,m},x] && IntegerQ[2*k]


Int[(c_.+d_.*x_)^m_.*sin[e_.+f_.*x_],x_Symbol] :=
  I/2*Int[(c+d*x)^m*E^(-I*(e+f*x)),x] - I/2*Int[(c+d*x)^m*E^(I*(e+f*x)),x] /;
FreeQ[{c,d,e,f,m},x]


Int[(c_.+d_.*x_)*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  d*(b*Sin[e+f*x])^n/(f^2*n^2) -
  b*(c+d*x)*Cos[e+f*x]*(b*Sin[e+f*x])^(n-1)/(f*n) +
  b^2*(n-1)/n*Int[(c+d*x)*(b*Sin[e+f*x])^(n-2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[n] && n>1


Int[(c_.+d_.*x_)^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  d*m*(c+d*x)^(m-1)*(b*Sin[e+f*x])^n/(f^2*n^2) -
  b*(c+d*x)^m*Cos[e+f*x]*(b*Sin[e+f*x])^(n-1)/(f*n) +
  b^2*(n-1)/n*Int[(c+d*x)^m*(b*Sin[e+f*x])^(n-2),x] -
  d^2*m*(m-1)/(f^2*n^2)*Int[(c+d*x)^(m-2)*(b*Sin[e+f*x])^n,x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n>1 && m>1


Int[(c_.+d_.*x_)^m_*sin[e_.+f_.*x_]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(c+d*x)^m,Sin[e+f*x]^n,x],x] /;
FreeQ[{c,d,e,f,m},x] && IntegerQ[n] && n>1 && (Not[RationalQ[m]] || -1<=m<1)


Int[(c_.+d_.*x_)^m_*sin[e_.+f_.*x_]^n_,x_Symbol] :=
  (c+d*x)^(m+1)*Sin[e+f*x]^n/(d*(m+1)) - 
  f*n/(d*(m+1))*Int[ExpandTrigReduce[(c+d*x)^(m+1),Cos[e+f*x]*Sin[e+f*x]^(n-1),x],x] /;
FreeQ[{c,d,e,f,m},x] && IntegerQ[n] && n>1 && RationalQ[m] && -2<=m<-1


Int[(c_.+d_.*x_)^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (c+d*x)^(m+1)*(b*Sin[e+f*x])^n/(d*(m+1)) - 
  b*f*n*(c+d*x)^(m+2)*Cos[e+f*x]*(b*Sin[e+f*x])^(n-1)/(d^2*(m+1)*(m+2)) - 
  f^2*n^2/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*(b*Sin[e+f*x])^n,x] + 
  b^2*f^2*n*(n-1)/(d^2*(m+1)*(m+2))*Int[(c+d*x)^(m+2)*(b*Sin[e+f*x])^(n-2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n>1 && m<-2


Int[(c_.+d_.*x_)*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (c+d*x)*Cos[e+f*x]*(b*Sin[e+f*x])^(n+1)/(b*f*(n+1)) -
  d*(b*Sin[e+f*x])^(n+2)/(b^2*f^2*(n+1)*(n+2)) +
  (n+2)/(b^2*(n+1))*Int[(c+d*x)*(b*Sin[e+f*x])^(n+2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[n] && n<-1 && n!=-2


Int[(c_.+d_.*x_)^m_.*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (c+d*x)^m*Cos[e+f*x]*(b*Sin[e+f*x])^(n+1)/(b*f*(n+1)) -
  d*m*(c+d*x)^(m-1)*(b*Sin[e+f*x])^(n+2)/(b^2*f^2*(n+1)*(n+2)) +
  (n+2)/(b^2*(n+1))*Int[(c+d*x)^m*(b*Sin[e+f*x])^(n+2),x] +
  d^2*m*(m-1)/(b^2*f^2*(n+1)*(n+2))*Int[(c+d*x)^(m-2)*(b*Sin[e+f*x])^(n+2),x] /;
FreeQ[{b,c,d,e,f},x] && RationalQ[m,n] && n<-1 && n!=-2 && m>1


Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^m,(a+b*Sin[e+f*x])^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && PositiveIntegerQ[n] && (n==1 || PositiveIntegerQ[m] || NeQ[a^2-b^2])


Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  (2*a)^n*Int[(c+d*x)^m*Sin[1/2*(e+Pi*a/(2*b))+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[a^2-b^2] && IntegerQ[n] && (n>0 || PositiveIntegerQ[m])


Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (2*a)^IntPart[n]*(a+b*Sin[e+f*x])^FracPart[n]/Sin[e/2+a*Pi/(4*b)+f*x/2]^(2*FracPart[n])*
    Int[(c+d*x)^m*Sin[e/2+a*Pi/(4*b)+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[a^2-b^2] && IntegerQ[n+1/2] && (n>0 || PositiveIntegerQ[m])


(* Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  (2*a)^n*Int[(c+d*x)^m*Cos[1/2*(e-Pi*a/(2*b))+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[a^2-b^2] && IntegerQ[n] && (n>0 || PositiveIntegerQ[m]) *)


(* Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  (2*a)^IntPart[n]*(a+b*Sin[e+f*x])^FracPart[n]/Cos[1/2*(e-Pi*a/(2*b))+f*x/2]^(2*FracPart[n])*
    Int[(c+d*x)^m*Cos[1/2*(e-Pi*a/(2*b))+f*x/2]^(2*n),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[a^2-b^2] && IntegerQ[n+1/2] && (n>0 || PositiveIntegerQ[m]) *)


Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+k_.*Pi+f_.*Complex[0,fz_]*x_]),x_Symbol] :=
  2*Int[(c+d*x)^m*E^(-I*Pi*(k-1/2))*E^(-I*e+f*fz*x)/(b+2*a*E^(-I*Pi*(k-1/2))*E^(-I*e+f*fz*x)-b*E^(-2*I*k*Pi)*E^(2*(-I*e+f*fz*x))),x] /;
FreeQ[{a,b,c,d,e,f,fz},x] && IntegerQ[2*k] && NeQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+k_.*Pi+f_.*x_]),x_Symbol] :=
  2*Int[(c+d*x)^m*E^(I*Pi*(k-1/2))*E^(I*(e+f*x))/(b+2*a*E^(I*Pi*(k-1/2))*E^(I*(e+f*x))-b*E^(2*I*k*Pi)*E^(2*I*(e+f*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && IntegerQ[2*k] && NeQ[a^2-b^2] && PositiveIntegerQ[m]


(* Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+f_.*Complex[0,fz_]*x_]),x_Symbol] :=
  2*I*Int[(c+d*x)^m*E^(-I*e+f*fz*x)/(b+2*I*a*E^(-I*e+f*fz*x)-b*E^(2*(-I*e+f*fz*x))),x] /;
FreeQ[{a,b,c,d,e,f,fz},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m] *)


(* Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  -2*I*Int[(c+d*x)^m*E^(I*(e+f*x))/(b-2*I*a*E^(I*(e+f*x))-b*E^(2*I*(e+f*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m] *)


Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+f_.*Complex[0,fz_]*x_]),x_Symbol] :=
  2*Int[(c+d*x)^m*E^(-I*e+f*fz*x)/(-I*b+2*a*E^(-I*e+f*fz*x)+I*b*E^(2*(-I*e+f*fz*x))),x] /;
FreeQ[{a,b,c,d,e,f,fz},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
  2*Int[(c+d*x)^m*E^(I*(e+f*x))/(I*b+2*a*E^(I*(e+f*x))-I*b*E^(2*I*(e+f*x))),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
  b*(c+d*x)^m*Cos[e+f*x]/(f*(a^2-b^2)*(a+b*Sin[e+f*x])) + 
  a/(a^2-b^2)*Int[(c+d*x)^m/(a+b*Sin[e+f*x]),x] - 
  b*d*m/(f*(a^2-b^2))*Int[(c+d*x)^(m-1)*Cos[e+f*x]/(a+b*Sin[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[a^2-b^2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
  -b*(c+d*x)^m*Cos[e+f*x]*(a+b*Sin[e+f*x])^(n+1)/(f*(n+1)*(a^2-b^2)) + 
  a/(a^2-b^2)*Int[(c+d*x)^m*(a+b*Sin[e+f*x])^(n+1),x] + 
  b*d*m/(f*(n+1)*(a^2-b^2))*Int[(c+d*x)^(m-1)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(n+1),x] - 
  b*(n+2)/((n+1)*(a^2-b^2))*Int[(c+d*x)^m*Sin[e+f*x]*(a+b*Sin[e+f*x])^(n+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[a^2-b^2] && NegativeIntegerQ[n+2] && PositiveIntegerQ[m]


Int[(c_.+d_.*x_)^m_.*(a_.+b_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
  Defer[Int][(c+d*x)^m*(a+b*Sin[e+f*x])^n,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[u_^m_.*(a_.+b_.*Sin[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Sin[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*(a_.+b_.*Cos[v_])^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*(a+b*Cos[ExpandToSum[v,x]])^n,x] /;
FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]





(* ::Subsection::Closed:: *)
(*4.1.11 (e x)^m (a+b x^n)^p sin*)


Int[(a_+b_.*x_^n_)^p_.*Sin[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sin[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[p]


Int[(a_+b_.*x_^n_)^p_.*Cos[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cos[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[p]


Int[(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
  x^(-n+1)*(a+b*x^n)^(p+1)*Sin[c+d*x]/(b*n*(p+1)) - 
  (-n+1)/(b*n*(p+1))*Int[x^(-n)*(a+b*x^n)^(p+1)*Sin[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(-n+1)*(a+b*x^n)^(p+1)*Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && PositiveIntegerQ[n] && p<-1 && n>2


Int[(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
  x^(-n+1)*(a+b*x^n)^(p+1)*Cos[c+d*x]/(b*n*(p+1)) - 
  (-n+1)/(b*n*(p+1))*Int[x^(-n)*(a+b*x^n)^(p+1)*Cos[c+d*x],x] + 
  d/(b*n*(p+1))*Int[x^(-n+1)*(a+b*x^n)^(p+1)*Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && PositiveIntegerQ[n] && p<-1 && n>2


Int[(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sin[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && PositiveIntegerQ[n] && (n==2 || p==-1)


Int[(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cos[c+d*x],(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && PositiveIntegerQ[n] && (n==2 || p==-1)


Int[(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
  Int[x^(n*p)*(b+a*x^(-n))^p*Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
  Int[x^(n*p)*(b+a*x^(-n))^p*Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
  Defer[Int][(a+b*x^n)^p*Sin[c+d*x],x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
  Defer[Int][(a+b*x^n)^p*Cos[c+d*x],x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sin[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sin[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cos[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cos[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
  e^m*(a+b*x^n)^(p+1)*Sin[c+d*x]/(b*n*(p+1)) - 
  d*e^m/(b*n*(p+1))*Int[(a+b*x^n)^(p+1)*Cos[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && EqQ[m-n+1] && RationalQ[p] && p<-1 && (IntegerQ[n] || PositiveQ[e])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
  e^m*(a+b*x^n)^(p+1)*Cos[c+d*x]/(b*n*(p+1)) + 
  d*e^m/(b*n*(p+1))*Int[(a+b*x^n)^(p+1)*Sin[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && EqQ[m-n+1] && RationalQ[p] && p<-1 && (IntegerQ[n] || PositiveQ[e])


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
  x^(m-n+1)*(a+b*x^n)^(p+1)*Sin[c+d*x]/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*(a+b*x^n)^(p+1)*Sin[c+d*x],x] - 
  d/(b*n*(p+1))*Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Cos[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && PositiveIntegerQ[n] && RationalQ[m] && p<-1 && (m-n+1>0 || n>2)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
  x^(m-n+1)*(a+b*x^n)^(p+1)*Cos[c+d*x]/(b*n*(p+1)) - 
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*(a+b*x^n)^(p+1)*Cos[c+d*x],x] + 
  d/(b*n*(p+1))*Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Sin[c+d*x],x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && PositiveIntegerQ[n] && RationalQ[m] && p<-1 && (m-n+1>0 || n>2)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Sin[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && IntegerQ[m] && PositiveIntegerQ[n] && (n==2 || p==-1)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
  Int[ExpandIntegrand[Cos[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NegativeIntegerQ[p] && IntegerQ[m] && PositiveIntegerQ[n] && (n==2 || p==-1)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
  Int[x^(m+n*p)*(b+a*x^(-n))^p*Sin[c+d*x],x] /;
FreeQ[{a,b,c,d,m},x] && NegativeIntegerQ[p] && NegativeIntegerQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
  Int[x^(m+n*p)*(b+a*x^(-n))^p*Cos[c+d*x],x] /;
FreeQ[{a,b,c,d,m},x] && NegativeIntegerQ[p] && NegativeIntegerQ[n]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sin[c_.+d_.*x_],x_Symbol] :=
  Defer[Int][(e*x)^m*(a+b*x^n)^p*Sin[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cos[c_.+d_.*x_],x_Symbol] :=
  Defer[Int][(e*x)^m*(a+b*x^n)^p*Cos[c+d*x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x]





(* ::Subsection::Closed:: *)
(*4.1.12 (e x)^m (a+b sin(c+d x^n))^p*)


Int[Sin[d_.*x_^2],x_Symbol] :=
  Sqrt[Pi/2]/Rt[d,2]*FresnelS[Sqrt[2/Pi]*Rt[d,2]*x] /;
FreeQ[d,x]


Int[Cos[d_.*x_^2],x_Symbol] :=
  Sqrt[Pi/2]/Rt[d,2]*FresnelC[Sqrt[2/Pi]*Rt[d,2]*x] /;
FreeQ[d,x]


Int[Sin[c_+d_.*x_^2],x_Symbol] :=
  Sin[c]*Int[Cos[d*x^2],x] + Cos[c]*Int[Sin[d*x^2],x] /;
FreeQ[{c,d},x]


Int[Cos[c_+d_.*x_^2],x_Symbol] :=
  Cos[c]*Int[Cos[d*x^2],x] - Sin[c]*Int[Sin[d*x^2],x] /;
FreeQ[{c,d},x]


Int[Sin[c_.+d_.*x_^n_],x_Symbol] :=
  I/2*Int[E^(-c*I-d*I*x^n),x] - I/2*Int[E^(c*I+d*I*x^n),x] /;
FreeQ[{c,d},x] && IntegerQ[n] && n>2


Int[Cos[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(-c*I-d*I*x^n),x] + 1/2*Int[E^(c*I+d*I*x^n),x] /;
FreeQ[{c,d},x] && IntegerQ[n] && n>2


Int[(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Sin[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && n>1 && p>1


Int[(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Cos[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && n>1 && p>1


Int[(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Sin[c+d*x^(-n)])^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NegativeIntegerQ[n]


Int[(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Cos[c+d*x^(-n)])^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NegativeIntegerQ[n]


Int[(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*Sin[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && FractionQ[n]


Int[(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*Cos[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && FractionQ[n]


Int[Sin[c_.+d_.*x_^n_],x_Symbol] :=
  I/2*Int[E^(-c*I-d*I*x^n),x] - I/2*Int[E^(c*I+d*I*x^n),x] /;
FreeQ[{c,d,n},x]


Int[Cos[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[E^(-c*I-d*I*x^n),x] + 1/2*Int[E^(c*I+d*I*x^n),x] /;
FreeQ[{c,d,n},x]


Int[(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Sin[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[p]


Int[(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(a+b*Cos[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && PositiveIntegerQ[p]


Int[(a_.+b_.*Sin[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Sin[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[p] && LinearQ[u,x] && NeQ[u-x]


Int[(a_.+b_.*Cos[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*Cos[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[p] && LinearQ[u,x] && NeQ[u-x]


Int[(a_.+b_.*Sin[c_.+d_.*u_^n_])^p_,x_Symbol] :=
  Defer[Int][(a+b*Sin[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x]


Int[(a_.+b_.*Cos[c_.+d_.*u_^n_])^p_,x_Symbol] :=
  Defer[Int][(a+b*Cos[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x]


Int[(a_.+b_.*Sin[u_])^p_.,x_Symbol] :=
  Int[(a+b*Sin[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*Cos[u_])^p_.,x_Symbol] :=
  Int[(a+b*Cos[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[Sin[d_.*x_^n_]/x_,x_Symbol] :=
  SinIntegral[d*x^n]/n /;
FreeQ[{d,n},x]


Int[Cos[d_.*x_^n_]/x_,x_Symbol] :=
  CosIntegral[d*x^n]/n /;
FreeQ[{d,n},x]


Int[Sin[c_+d_.*x_^n_]/x_,x_Symbol] :=
  Sin[c]*Int[Cos[d*x^n]/x,x] + Cos[c]*Int[Sin[d*x^n]/x,x] /;
FreeQ[{c,d,n},x]


Int[Cos[c_+d_.*x_^n_]/x_,x_Symbol] :=
  Cos[c]*Int[Cos[d*x^n]/x,x] - Sin[c]*Int[Sin[d*x^n]/x,x] /;
FreeQ[{c,d,n},x]


Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Sin[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]] && (EqQ[p,1] || EqQ[m,n-1] || IntegerQ[p] && Simplify[(m+1)/n]>0)


Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Cos[c+d*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]] && (EqQ[p,1] || EqQ[m,n-1] || IntegerQ[p] && Simplify[(m+1)/n]>0)


Int[(e_*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sin[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[(e_*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cos[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
  2/n*Subst[Int[Sin[a+b*x^2],x],x,x^(n/2)] /;
FreeQ[{a,b,m,n},x] && EqQ[m-(n/2-1)]


Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
  2/n*Subst[Int[Cos[a+b*x^2],x],x,x^(n/2)] /;
FreeQ[{a,b,m,n},x] && EqQ[m-(n/2-1)]


Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^n_],x_Symbol] :=
  -e^(n-1)*(e*x)^(m-n+1)*Cos[c+d*x^n]/(d*n) + 
  e^n*(m-n+1)/(d*n)*Int[(e*x)^(m-n)*Cos[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && PositiveIntegerQ[n] && RationalQ[m] && 0<n<m+1


Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^n_],x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*Sin[c+d*x^n]/(d*n) - 
  e^n*(m-n+1)/(d*n)*Int[(e*x)^(m-n)*Sin[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && PositiveIntegerQ[n] && RationalQ[m] && 0<n<m+1


Int[(e_.*x_)^m_*Sin[c_.+d_.*x_^n_],x_Symbol] :=
  (e*x)^(m+1)*Sin[c+d*x^n]/(e*(m+1)) - 
  d*n/(e^n*(m+1))*Int[(e*x)^(m+n)*Cos[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[(e_.*x_)^m_*Cos[c_.+d_.*x_^n_],x_Symbol] :=
  (e*x)^(m+1)*Cos[c+d*x^n]/(e*(m+1)) + 
  d*n/(e^n*(m+1))*Int[(e*x)^(m+n)*Sin[c+d*x^n],x] /;
FreeQ[{c,d,e},x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^n_],x_Symbol] :=
  I/2*Int[(e*x)^m*E^(-c*I-d*I*x^n),x] - I/2*Int[(e*x)^m*E^(c*I+d*I*x^n),x] /;
FreeQ[{c,d,e,m},x] && PositiveIntegerQ[n]


Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(-c*I-d*I*x^n),x] + 1/2*Int[(e*x)^m*E^(c*I+d*I*x^n),x] /;
FreeQ[{c,d,e,m},x] && PositiveIntegerQ[n]


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -Sin[a+b*x^n]^p/((n-1)*x^(n-1)) +
  b*n*p/(n-1)*Int[Sin[a+b*x^n]^(p-1)*Cos[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && EqQ[m+n] && p>1 && NeQ[n-1]


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -Cos[a+b*x^n]^p/((n-1)*x^(n-1)) -
  b*n*p/(n-1)*Int[Cos[a+b*x^n]^(p-1)*Sin[a+b*x^n],x] /;
FreeQ[{a,b},x] && IntegersQ[n,p] && EqQ[m+n] && p>1 && NeQ[n-1]


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  n*Sin[a+b*x^n]^p/(b^2*n^2*p^2) -
  x^n*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Sin[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1] && RationalQ[p] && p>1


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  n*Cos[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^n*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Cos[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1] && RationalQ[p] && p>1


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  (m-n+1)*x^(m-2*n+1)*Sin[a+b*x^n]^p/(b^2*n^2*p^2) -
  x^(m-n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Sin[a+b*x^n]^(p-2),x] -
  (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2)*Int[x^(m-2*n)*Sin[a+b*x^n]^p,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<m+1


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  (m-n+1)*x^(m-2*n+1)*Cos[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^(m-n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/(b*n*p) +
  (p-1)/p*Int[x^m*Cos[a+b*x^n]^(p-2),x] -
  (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2)*Int[x^(m-2*n)*Cos[a+b*x^n]^p,x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<m+1


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m+1)*Sin[a+b*x^n]^p/(m+1) - 
  b*n*p*x^(m+n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) - 
  b^2*n^2*p^2/((m+1)*(m+n+1))*Int[x^(m+2*n)*Sin[a+b*x^n]^p,x] + 
  b^2*n^2*p*(p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*Sin[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<1-m && NeQ[m+n+1]


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m+1)*Cos[a+b*x^n]^p/(m+1) + 
  b*n*p*x^(m+n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) - 
  b^2*n^2*p^2/((m+1)*(m+n+1))*Int[x^(m+2*n)*Cos[a+b*x^n]^p,x] + 
  b^2*n^2*p*(p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*Cos[a+b*x^n]^(p-2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<1-m && NeQ[m+n+1]


Int[(e_.*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  k/e*Subst[Int[x^(k*(m+1)-1)*(a+b*Sin[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  k/e*Subst[Int[x^(k*(m+1)-1)*(a+b*Cos[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && PositiveIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Sin[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && p>1


Int[(e_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Cos[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && PositiveIntegerQ[n] && p>1


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^n*Cos[a+b*x^n]*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  n*Sin[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) + 
  (p+2)/(p+1)*Int[x^m*Sin[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1] && RationalQ[p] && p<-1 && p!=-2


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^n*Sin[a+b*x^n]*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  n*Cos[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) + 
  (p+2)/(p+1)*Int[x^m*Cos[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1] && RationalQ[p] && p<-1 && p!=-2


Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  x^(m-n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)*x^(m-2*n+1)*Sin[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (p+2)/(p+1)*Int[x^m*Sin[a+b*x^n]^(p+2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2))*Int[x^(m-2*n)*Sin[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p<-1 && p!=-2 && 0<2*n<m+1 


Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
  -x^(m-n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)*x^(m-2*n+1)*Cos[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  (p+2)/(p+1)*Int[x^m*Cos[a+b*x^n]^(p+2),x] +
  (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2))*Int[x^(m-2*n)*Cos[a+b*x^n]^(p+2),x] /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p<-1 && p!=-2 && 0<2*n<m+1 


Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Sin[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NegativeIntegerQ[n] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -Subst[Int[(a+b*Cos[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d},x] && IntegerQ[p] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/e*Subst[Int[(a+b*Sin[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && NegativeIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/e*Subst[Int[(a+b*Cos[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && NegativeIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*Sin[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[(e_.*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*Cos[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*Sin[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]


Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  Module[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*Cos[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]


Int[(e_*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sin[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]


Int[(e_*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cos[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]


Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*Sin[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NeQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*Cos[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NeQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Sin[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NeQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*Cos[c+d*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NeQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^n_],x_Symbol] :=
  I/2*Int[(e*x)^m*E^(-c*I-d*I*x^n),x] - I/2*Int[(e*x)^m*E^(c*I+d*I*x^n),x] /;
FreeQ[{c,d,e,m,n},x]


Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^n_],x_Symbol] :=
  1/2*Int[(e*x)^m*E^(-c*I-d*I*x^n),x] + 1/2*Int[(e*x)^m*E^(c*I+d*I*x^n),x] /;
FreeQ[{c,d,e,m,n},x]


Int[(e_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Sin[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[(e_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_,x_Symbol] :=
  Int[ExpandTrigReduce[(e*x)^m,(a+b*Cos[c+d*x^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && PositiveIntegerQ[p]


Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*(a+b*Sin[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u-x] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]^(m+1)*Subst[Int[(x-Coefficient[u,x,0])^m*(a+b*Cos[c+d*x^n])^p,x],x,u] /;
FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u-x] && IntegerQ[m]


Int[(e_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  Defer[Int][(e*x)^m*(a+b*Sin[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && LinearQ[u,x]


Int[(e_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
  Defer[Int][(e*x)^m*(a+b*Cos[c+d*u^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && LinearQ[u,x]


Int[(e_*x_)^m_.*(a_.+b_.*Sin[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Sin[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(e_*x_)^m_.*(a_.+b_.*Cos[u_])^p_.,x_Symbol] :=
  Int[(e*x)^m*(a+b*Cos[ExpandToSum[u,x]])^p,x] /;
FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*Sin[a_.+b_.*x_^n_.]^p_.*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
  Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && EqQ[m-n+1] && NeQ[p+1]


Int[x_^m_.*Cos[a_.+b_.*x_^n_.]^p_.*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
  -Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && EqQ[m-n+1] && NeQ[p+1]


Int[x_^m_.*Sin[a_.+b_.*x_^n_.]^p_.*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
  x^(m-n+1)*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Sin[a+b*x^n]^(p+1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m,n] && 0<n<m+1 && NeQ[p+1]


Int[x_^m_.*Cos[a_.+b_.*x_^n_.]^p_.*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
  -x^(m-n+1)*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) +
  (m-n+1)/(b*n*(p+1))*Int[x^(m-n)*Cos[a+b*x^n]^(p+1),x] /;
FreeQ[{a,b,p},x] && RationalQ[m,n] && 0<n<m+1 && NeQ[p+1]





(* ::Subsection::Closed:: *)
(*4.1.13 (d+e x)^m sin(a+b x+c x^2)^n*)


Int[Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Int[Sin[(b+2*c*x)^2/(4*c)],x] /;
FreeQ[{a,b,c},x] && EqQ[b^2-4*a*c,0]


Int[Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Int[Cos[(b+2*c*x)^2/(4*c)],x] /;
FreeQ[{a,b,c},x] && EqQ[b^2-4*a*c,0]


Int[Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Cos[(b^2-4*a*c)/(4*c)]*Int[Sin[(b+2*c*x)^2/(4*c)],x] - 
  Sin[(b^2-4*a*c)/(4*c)]*Int[Cos[(b+2*c*x)^2/(4*c)],x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]


Int[Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Cos[(b^2-4*a*c)/(4*c)]*Int[Cos[(b+2*c*x)^2/(4*c)],x] + 
  Sin[(b^2-4*a*c)/(4*c)]*Int[Sin[(b+2*c*x)^2/(4*c)],x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]


Int[Sin[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[Sin[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[Cos[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[Cos[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n>1


Int[Sin[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][Sin[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,n},x]


Int[Cos[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][Cos[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,n},x]


Int[Sin[v_]^n_.,x_Symbol] :=
  Int[Sin[ExpandToSum[v,x]]^n,x] /;
PositiveIntegerQ[n] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[Cos[v_]^n_.,x_Symbol] :=
  Int[Cos[ExpandToSum[v,x]]^n,x] /;
PositiveIntegerQ[n] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]


Int[(d_+e_.*x_)*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*Cos[a+b*x+c*x^2]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0]


Int[(d_+e_.*x_)*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Sin[a+b*x+c*x^2]/(2*c) /;
FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0]


Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*(d+e*x)^(m-1)*Cos[a+b*x+c*x^2]/(2*c) + 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && GtQ[m,1]


Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Sin[a+b*x+c*x^2]/(2*c) - 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && GtQ[m,1]


Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sin[a+b*x+c*x^2]/(e*(m+1)) -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Cos[a+b*x+c*x^2]/(e*(m+1)) + 
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*Cos[a+b*x+c*x^2]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0]


Int[(d_.+e_.*x_)*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*Sin[a+b*x+c*x^2]/(2*c) + 
  (2*c*d-b*e)/(2*c)*Int[Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0]


Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  -e*(d+e*x)^(m-1)*Cos[a+b*x+c*x^2]/(2*c) - 
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*Sin[a+b*x+c*x^2],x] + 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && GtQ[m,1]


Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m-1)*Sin[a+b*x+c*x^2]/(2*c) - 
  (b*e-2*c*d)/(2*c)*Int[(d+e*x)^(m-1)*Cos[a+b*x+c*x^2],x] - 
  e^2*(m-1)/(2*c)*Int[(d+e*x)^(m-2)*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && GtQ[m,1]


Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sin[a+b*x+c*x^2]/(e*(m+1)) -
  (b*e-2*c*d)/(e^2*(m+1))*Int[(d+e*x)^(m+1)*Cos[a+b*x+c*x^2],x] -
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Cos[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Cos[a+b*x+c*x^2]/(e*(m+1)) + 
  (b*e-2*c*d)/(e^2*(m+1))*Int[(d+e*x)^(m+1)*Sin[a+b*x+c*x^2],x] +
  2*c/(e^2*(m+1))*Int[(d+e*x)^(m+2)*Sin[a+b*x+c*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_.*Sin[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(d+e*x)^m,Sin[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1]


Int[(d_.+e_.*x_)^m_.*Cos[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
  Int[ExpandTrigReduce[(d+e*x)^m,Cos[a+b*x+c*x^2]^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1]


Int[(d_.+e_.*x_)^m_.*Sin[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*Sin[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[(d_.+e_.*x_)^m_.*Cos[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*Cos[a+b*x+c*x^2]^n,x] /;
FreeQ[{a,b,c,d,e,m,n},x]


Int[u_^m_.*Sin[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Sin[ExpandToSum[v,x]]^n,x] /;
FreeQ[m,x] && PositiveIntegerQ[n] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[u_^m_.*Cos[v_]^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Cos[ExpandToSum[v,x]]^n,x] /;
FreeQ[m,x] && PositiveIntegerQ[n] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]



