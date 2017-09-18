(* ::Package:: *)

(* ::Section:: *)
(*1.2.3 General Trinomial Product Integration Rules*)


(* ::Subsection::Closed:: *)
(*1.2.3.1 (a+b x^n+c x^(2 n))^p*)


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(2*n*p)*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c},x] && EqQ[n2,2*n] && LtQ[n,0] && IntegerQ[p]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*x^(k*n)+c*x^(2*k*n))^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && FractionQ[n]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && ILtQ[n,0]


Int[(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^p/(b+2*c*x^n)^(2*p)*Int[(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[p,0]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  x*(a+b*x^n+c*x^(2*n))^p/(2*n*p+1) + 
  n*p/(2*n*p+1)*Int[(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[2*n*p+1,0] && IntegerQ[p]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -x*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) +
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[(b^2-2*a*c+n*(p+1)*(b^2-4*a*c)+b*c*(n*(2*p+3)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IntegerQ[p]


Int[1/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a/c,2]},
  With[{r=Rt[2*q-b/c,2]},
  1/(2*c*q*r)*Int[(r-x^(n/2))/(q-r*x^(n/2)+x^n),x] + 
  1/(2*c*q*r)*Int[(r+x^(n/2))/(q+r*x^(n/2)+x^n),x]]] /;
FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n/2,0] && NegQ[b^2-4*a*c]


Int[1/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[1/(b/2-q/2+c*x^n),x] - c/q*Int[1/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^n+c*x^(2*n))^FracPart[p]/
    ((1+2*c*x^n/(b+Rt[b^2-4*a*c,2]))^FracPart[p]*(1+2*c*x^n/(b-Rt[b^2-4*a*c,2]))^FracPart[p])*
    Int[(1+2*c*x^n/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^n/(b-Sqrt[b^2-4*a*c]))^p,x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n]


Int[(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[(b+a*x^n+c*x^(2*n))^p/x^(n*p),x] /;
FreeQ[{a,b,c,n},x] && EqQ[mn,-n] && IntegerQ[p] && PosQ[n]


Int[(a_+b_.*x_^mn_+c_.*x_^n_.)^p_,x_Symbol] :=
  x^(n*FracPart[p])*(a+b*x^(-n)+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p]*Int[(b+a*x^n+c*x^(2*n))^p/x^(n*p),x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[mn,-n] && Not[IntegerQ[p]] && PosQ[n]


Int[(a_+b_.*u_^n_+c_.*u_^n2_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && LinearQ[u,x] && NeQ[u,x]





(* ::Subsection::Closed:: *)
(*1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p*)


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && EqQ[Simplify[m-n+1]]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && PositiveIntegerQ[p] && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[x^(m+2*n*p)*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,m,n},x] && EqQ[n2,2*n] && NegativeIntegerQ[p] && NegQ[n]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[(d_*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k)+c*x^(2*n/k))^p,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/d*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/d^n+c*x^(2*k*n)/d^(2*n))^p,x],x,(d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && FractionQ[m] && IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(n-1)*(d*x)^(m-n+1)*(b*n*p+c*(m+n*(2*p-1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/(c*(m+2*n*p+1)*(m+n*(2*p-1)+1)) - 
  n*p*d^n/(c*(m+2*n*p+1)*(m+n*(2*p-1)+1))*
    Int[(d*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p-1)*Simp[a*b*(m-n+1)-(2*a*c*(m+n*(2*p-1)+1)-b^2*(m+n*(p-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m>n-1 && 
  m+2*n*p+1!=0 && m+n*(2*p-1)+1!=0 && IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+1)) - 
  n*p/(d^n*(m+1))*Int[(d*x)^(m+n)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-1 && IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+2*n*p+1)) + 
  n*p/(m+2*n*p+1)*Int[(d*x)^m*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p>0 && NeQ[m+2*n*p+1] && 
  IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(n-1)*(d*x)^(m-n+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) - 
  d^n/(n*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^(m-n)*(b*(m-n+1)+2*c*(m+2*n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && n-1<m<=2*n-1 && 
  IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -d^(2*n-1)*(d*x)^(m-2*n+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) + 
  d^(2*n)/(n*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^(m-2*n)*(2*a*(m-2*n+1)+b*(m+n*(2*p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>2*n-1 && 
  IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -(d*x)^(m+1)*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*Simp[b^2*(n*(p+1)+m+1)-2*a*c*(m+2*n*(p+1)+1)+b*c*(2*n*p+3*n+m+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(2*n-1)*(d*x)^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+2*n*p+1)) - 
  d^(2*n)/(c*(m+2*n*p+1))*
    Int[(d*x)^(m-2*n)*Simp[a*(m-2*n+1)+b*(m+n*(p-1)+1)*x^n,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>2*n-1 && 
  NeQ[m+2*n*p+1] && IntegerQ[p]


Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*(m+1)) - 
  1/(a*d^n*(m+1))*Int[(d*x)^(m+n)*(b*(m+n*(p+1)+1)+c*(m+2*n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && IntegerQ[p]


Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  (d*x)^(m+1)/(a*d*(m+1)) -
  1/(a*d^n)*Int[(d*x)^(m+n)*(b+c*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[PolynomialDivide[x^m,(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m] && m>3*n-1


Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  d^(2*n-1)*(d*x)^(m-2*n+1)/(c*(m-2*n+1)) -
  d^(2*n)/c*Int[(d*x)^(m-2*n)*(a+b*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>2*n-1


Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[a/c,2]},
  With[{r=Rt[2*q-b/c,2]},
  1/(2*c*r)*Int[x^(m-3*(n/2))*(q+r*x^(n/2))/(q+r*x^(n/2)+x^n),x] - 
  1/(2*c*r)*Int[x^(m-3*(n/2))*(q-r*x^(n/2))/(q-r*x^(n/2)+x^n),x]]] /;
FreeQ[{a,b,c},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n/2,m] && 3*n/2<=m<2*n && NegQ[b^2-4*a*c]


Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[a/c,2]},
  With[{r=Rt[2*q-b/c,2]},
  1/(2*c*r)*Int[x^(m-n/2)/(q-r*x^(n/2)+x^n),x] - 
  1/(2*c*r)*Int[x^(m-n/2)/(q+r*x^(n/2)+x^n),x]]] /;
FreeQ[{a,b,c},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n/2,m] && n/2<=m<3*n/2 && NegQ[b^2-4*a*c]


Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  d^n/2*(b/q+1)*Int[(d*x)^(m-n)/(b/2+q/2+c*x^n),x] - 
  d^n/2*(b/q-1)*Int[(d*x)^(m-n)/(b/2-q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>=n


Int[(d_.*x_)^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[(d*x)^m/(b/2-q/2+c*x^n),x] - c/q*Int[(d*x)^m/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/d*Subst[Int[(a+b*d^(-n)*x^(-k*n)+c*d^(-2*n)*x^(-2*k*n))^p/x^(k*(m+1)+1),x],x,1/(d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && FractionQ[m]


Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -d^IntPart[m]*(d*x)^FracPart[m]*(x^(-1))^FracPart[m]*Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)+c*x^(2*k*n))^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,m,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && FractionQ[n]


Int[(d_*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && FractionQ[n]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(d_*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(d_.*x_)^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[(d*x)^m/(b-q+2*c*x^n),x] -
  2*c/q*Int[(d*x)^m/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -(d*x)^(m+1)*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*Simp[b^2*(n*(p+1)+m+1)-2*a*c*(m+2*n*(p+1)+1)+b*c*(2*n*p+3*n+m+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^n+c*x^(2*n))^FracPart[p]/
    ((1+2*c*x^n/(b+Rt[b^2-4*a*c,2]))^FracPart[p]*(1+2*c*x^n/(b-Rt[b^2-4*a*c,2]))^FracPart[p])*
    Int[(d*x)^m*(1+2*c*x^n/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^n/(b-Sqrt[b^2-4*a*c]))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n]


Int[x_^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^(m-n*p)*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,m,n},x] && EqQ[mn,-n] && IntegerQ[p] && PosQ[n]


Int[x_^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p]*Int[x^(m-n*p)*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[mn,-n] && Not[IntegerQ[p]] && PosQ[n]


Int[(d_*x_)^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^(-n)+c*x^n)^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[mn,-n]


Int[x_^m_.*(a_.+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  1/Coefficient[v,x,1]^(m+1)*Subst[Int[SimplifyIntegrand[(x-Coefficient[v,x,0])^m*(a+b*x^n+c*x^(2*n))^p,x],x],x,v] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && LinearQ[v,x] && IntegerQ[m] && NeQ[v-x]


Int[u_^m_.*(a_.+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && LinearPairQ[u,v,x]





(* ::Subsection::Closed:: *)
(*1.2.3.3 (d+e x^n)^q (a+b x^n+c x^(2 n))^p*)


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(n*(2*p+q))*(e+d*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && IntegersQ[p,q] && NegQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(n*(2*p+q))*(e+d*x^(-n))^q*(c+a*x^(-2*n))^p,x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && IntegersQ[p,q] && NegQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2-2*n] && NegativeIntegerQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^2,x],x,1/x] /;
FreeQ[{a,c,d,e,p,q},x] && EqQ[n2-2*n] && NegativeIntegerQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*(d+e*x^(g*n))^q*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2-2*n] && FractionQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*(d+e*x^(g*n))^q*(a+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,c,d,e,p,q},x] && EqQ[n2-2*n] && FractionQ[n]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (b*e-d*c)*(b*x^n+c*x^(2*n))^(p+1)/(b*c*n*(p+1)*x^(2*n*(p+1))) + 
  e/c*Int[x^(-n)*(b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{b,c,d,e,n,p},x] && EqQ[n2-2*n] && Not[IntegerQ[p]] && EqQ[n*(2*p+1)+1]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  e*x^(-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(n*(2*p+1)+1)) /;
FreeQ[{b,c,d,e,n,p},x] && EqQ[n2-2*n] && Not[IntegerQ[p]] && NeQ[n*(2*p+1)+1] && EqQ[b*e*(n*p+1)-c*d*(n*(2*p+1)+1)]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  e*x^(-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(n*(2*p+1)+1)) - 
  (b*e*(n*p+1)-c*d*(n*(2*p+1)+1))/(c*(n*(2*p+1)+1))*Int[(b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{b,c,d,e,n,p},x] && EqQ[n2-2*n] && Not[IntegerQ[p]] && NeQ[n*(2*p+1)+1] && NeQ[b*e*(n*p+1)-c*d*(n*(2*p+1)+1)]


Int[(d_+e_.*x_^n_)^q_.*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (b*x^n+c*x^(2*n))^FracPart[p]/(x^(n*FracPart[p])*(b+c*x^n)^FracPart[p])*Int[x^(n*p)*(d+e*x^n)^q*(b+c*x^n)^p,x] /;
FreeQ[{b,c,d,e,n,p,q},x] && EqQ[n2-2*n] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,n,q},x] && EqQ[n2-2*n] && EqQ[c*d^2+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*Int[(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*Int[(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2-2*n] && EqQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[q]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q*(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && PositiveIntegerQ[q]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  -(c*d^2-b*d*e+a*e^2)*x*(d+e*x^n)^(q+1)/(d*e^2*n*(q+1)) + 
  1/(n*(q+1)*d*e^2)*Int[(d+e*x^n)^(q+1)*Simp[c*d^2-b*d*e+a*e^2*(n*(q+1)+1)+c*d*e*n*(q+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && RationalQ[q] && q<-1


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_),x_Symbol] :=
  -(c*d^2+a*e^2)*x*(d+e*x^n)^(q+1)/(d*e^2*n*(q+1)) + 
  1/(n*(q+1)*d*e^2)*Int[(d+e*x^n)^(q+1)*Simp[c*d^2+a*e^2*(n*(q+1)+1)+c*d*e*n*(q+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && RationalQ[q] && q<-1


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  c*x^(n+1)*(d+e*x^n)^(q+1)/(e*(n*(q+2)+1)) + 
  1/(e*(n*(q+2)+1))*Int[(d+e*x^n)^q*(a*e*(n*(q+2)+1)-(c*d*(n+1)-b*e*(n*(q+2)+1))*x^n),x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2]


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_),x_Symbol] :=
  c*x^(n+1)*(d+e*x^n)^(q+1)/(e*(n*(q+2)+1)) + 
  1/(e*(n*(q+2)+1))*Int[(d+e*x^n)^q*(a*e*(n*(q+2)+1)-c*d*(n+1)*x^n),x] /;
FreeQ[{a,c,d,e,n,q},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2]


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[2*d*e,2]},
  e^2/(2*c)*Int[1/(d+q*x^(n/2)+e*x^n),x] + e^2/(2*c)*Int[1/(d-q*x^(n/2)+e*x^n),x]] /;
FreeQ[{a,c,d,e},x] && EqQ[n2-2*n] && EqQ[c*d^2-a*e^2] && PositiveIntegerQ[n/2] && PosQ[d*e]


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[-2*d*e,2]},
  d/(2*a)*Int[(d-q*x^(n/2))/(d-q*x^(n/2)-e*x^n),x] + 
  d/(2*a)*Int[(d+q*x^(n/2))/(d+q*x^(n/2)-e*x^n),x]] /;
FreeQ[{a,c,d,e},x] && EqQ[n2-2*n] && EqQ[c*d^2-a*e^2] && PositiveIntegerQ[n/2] && NegQ[d*e]


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a/c,4]},
  1/(2*Sqrt[2]*c*q^3)*Int[(Sqrt[2]*d*q-(d-e*q^2)*x^(n/2))/(q^2-Sqrt[2]*q*x^(n/2)+x^n),x] + 
  1/(2*Sqrt[2]*c*q^3)*Int[(Sqrt[2]*d*q+(d-e*q^2)*x^(n/2))/(q^2+Sqrt[2]*q*x^(n/2)+x^n),x]] /;
FreeQ[{a,c,d,e},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && NeQ[c*d^2-a*e^2] && PositiveIntegerQ[n/2] && PosQ[a*c]


Int[(d_+e_.*x_^3)/(a_+c_.*x_^6),x_Symbol] :=
  With[{q=Rt[c/a,6]},
  1/(3*a*q^2)*Int[(q^2*d-e*x)/(1+q^2*x^2),x] + 
  1/(6*a*q^2)*Int[(2*q^2*d-(Sqrt[3]*q^3*d-e)*x)/(1-Sqrt[3]*q*x+q^2*x^2),x] + 
  1/(6*a*q^2)*Int[(2*q^2*d+(Sqrt[3]*q^3*d+e)*x)/(1+Sqrt[3]*q*x+q^2*x^2),x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2] && PosQ[c/a]


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[-a/c,2]},
  (d+e*q)/2*Int[1/(a+c*q*x^n),x] + (d-e*q)/2*Int[1/(a-c*q*x^n),x]] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && NegQ[a*c] && IntegerQ[n]


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  d*Int[1/(a+c*x^(2*n)),x] + e*Int[x^n/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && (PosQ[a*c] || Not[IntegerQ[n]])


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[2*d/e-b/c,2]},
  e/(2*c)*Int[1/Simp[d/e+q*x^(n/2)+x^n,x],x] + 
  e/(2*c)*Int[1/Simp[d/e-q*x^(n/2)+x^n,x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-a*e^2] && PositiveIntegerQ[n/2] && 
  (PositiveQ[2*d/e-b/c] || Not[NegativeQ[2*d/e-b/c]] && EqQ[d-e*Rt[a/c,2]])


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (e/2+(2*c*d-b*e)/(2*q))*Int[1/(b/2-q/2+c*x^n),x] + (e/2-(2*c*d-b*e)/(2*q))*Int[1/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-a*e^2] && PositiveIntegerQ[n/2] && 
  PositiveQ[b^2-4*a*c]


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[-2*d/e-b/c,2]},
  e/(2*c*q)*Int[(q-2*x^(n/2))/Simp[d/e+q*x^(n/2)-x^n,x],x] + 
  e/(2*c*q)*Int[(q+2*x^(n/2))/Simp[d/e-q*x^(n/2)-x^n,x],x]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-a*e^2] && PositiveIntegerQ[n/2] && 
  Not[PositiveQ[b^2-4*a*c]]


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (e/2+(2*c*d-b*e)/(2*q))*Int[1/(b/2-q/2+c*x^n),x] + (e/2-(2*c*d-b*e)/(2*q))*Int[1/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && 
  (PosQ[b^2-4*a*c] || Not[PositiveIntegerQ[n/2]])


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a/c,2]},
  With[{r=Rt[2*q-b/c,2]},
  1/(2*c*q*r)*Int[(d*r-(d-e*q)*x^(n/2))/(q-r*x^(n/2)+x^n),x] + 
  1/(2*c*q*r)*Int[(d*r+(d-e*q)*x^(n/2))/(q+r*x^(n/2)+x^n),x]]] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[n/2] && 
  NegQ[b^2-4*a*c]


Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && IntegerQ[q]


Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && IntegerQ[q]


Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  e^2/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x^n)^q,x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x^n)^(q+1)*(c*d-b*e-c*e*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[q]] && 
  RationalQ[q] && q<-1


Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
  e^2/(c*d^2+a*e^2)*Int[(d+e*x^n)^q,x] + 
  c/(c*d^2+a*e^2)*Int[(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && Not[IntegerQ[q]] && RationalQ[q] && q<-1


Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  2*c/r*Int[(d+e*x^n)^q/(b-r+2*c*x^n),x] - 2*c/r*Int[(d+e*x^n)^q/(b+r+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[q]]


Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{r=Rt[-a*c,2]},
  -c/(2*r)*Int[(d+e*x^n)^q/(r-c*x^n),x] - c/(2*r)*Int[(d+e*x^n)^q/(r+c*x^n),x]] /;
FreeQ[{a,c,d,e,n,q},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && Not[IntegerQ[q]]


Int[(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  x*(b*e*n*p+c*d*(2*n*p+n+1)+c*e*(2*n*p+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/(c*(2*n*p+1)*(2*n*p+n+1)) + 
  n*p/(c*(2*n*p+1)*(2*n*p+n+1))*
    Int[Simp[2*a*c*d*(2*n*p+n+1)-a*b*e+(2*a*c*e*(2*n*p+1)+b*d*c*(2*n*p+n+1)-b^2*e*(n*p+1))*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && FractionQ[p] && p>0 && NeQ[2*n*p+1] && NeQ[2*n*p+n+1] && 
  IntegerQ[p]


Int[(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  x*(d*(2*n*p+n+1)+e*(2*n*p+1)*x^n)*(a+c*x^(2*n))^p/((2*n*p+1)*(2*n*p+n+1)) + 
  2*a*n*p/((2*n*p+1)*(2*n*p+n+1))*Int[(d*(2*n*p+n+1)+e*(2*n*p+1)*x^n)*(a+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && FractionQ[p] && p>0 && NeQ[2*n*p+1] && NeQ[2*n*p+n+1] && 
  IntegerQ[p]


Int[(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(d*b^2-a*b*e-2*a*c*d+(b*d-2*a*e)*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[Simp[(n*p+n+1)*d*b^2-a*b*e-2*a*c*d*(2*n*p+2*n+1)+(2*n*p+3*n+1)*(d*b-2*a*e)*c*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && RationalQ[p] && p<-1 && IntegerQ[p]


Int[(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(d+e*x^n)*(a+c*x^(2*n))^(p+1)/(2*a*n*(p+1)) + 
  1/(2*a*n*(p+1))*Int[(d*(2*n*p+2*n+1)+e*(2*n*p+3*n+1)*x^n)*(a+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n] && RationalQ[p] && p<-1 && IntegerQ[p]


Int[(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c]


Int[(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,n},x] && EqQ[n2-2*n]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  c^p*x^(2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*(2*n*p+n*q+1)) + 
  Int[(d+e*x^n)^q*ExpandToSum[(a+b*x^n+c*x^(2*n))^p-c^p*x^(2*n*p)-d*c^p*(2*n*p-n+1)*x^(2*n*p-n)/(e*(2*n*p+n*q+1)),x],x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[p] && 
  NeQ[2*n*p+n*q+1] && PositiveIntegerQ[n] && Not[PositiveIntegerQ[q]]


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  c^p*x^(2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*(2*n*p+n*q+1)) + 
  Int[(d+e*x^n)^q*ExpandToSum[(a+c*x^(2*n))^p-c^p*x^(2*n*p)-d*c^p*(2*n*p-n+1)*x^(2*n*p-n)/(e*(2*n*p+n*q+1)),x],x] /;
FreeQ[{a,c,d,e,n,q},x] && EqQ[n2-2*n] && PositiveIntegerQ[p] && 
  NeQ[2*n*p+n*q+1] && PositiveIntegerQ[n] && Not[PositiveIntegerQ[q]]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && 
  (IntegersQ[p,q] && Not[IntegerQ[n]] || PositiveIntegerQ[p] || PositiveIntegerQ[q] && Not[IntegerQ[n]])


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && 
  (IntegersQ[p,q] && Not[IntegerQ[n]] || PositiveIntegerQ[p] || PositiveIntegerQ[q] && Not[IntegerQ[n]])


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^(2*n))^p,(d/(d^2-e^2*x^(2*n))-e*x^n/(d^2-e^2*x^(2*n)))^(-q),x],x] /;
FreeQ[{a,c,d,e,n,p},x] && EqQ[n2-2*n] && NeQ[c*d^2+a*e^2] && NegativeIntegerQ[q] && Not[IntegersQ[n,2*p]]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Defer[Int][(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2-2*n] && Not[IntegersQ[n,q]]


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  Defer[Int][(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2-2*n] && Not[IntegersQ[n,q]]


Int[(d_+e_.*u_^n_)^q_.*(a_+b_.*u_^n_+c_.*u_^n2_)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2-2*n] && LinearQ[u,x] && NeQ[u-x]


Int[(d_+e_.*u_^n_)^q_.*(a_+c_.*u_^n2_)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2-2*n] && LinearQ[u,x] && NeQ[u-x]


Int[(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2,2*n] && EqQ[mn,-n] && IntegerQ[q]


Int[(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
FreeQ[{a,c,d,e,mn,p},x] && EqQ[n2,-2*mn] && IntegerQ[q]


Int[(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(2*n*p)*(d+e*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && IntegerQ[p]


Int[(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(-2*mn*p)*(d+e*x^mn)^q*(c+a*x^(2*mn))^p,x] /;
FreeQ[{a,c,d,e,mn,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && IntegerQ[p]


Int[(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  x^(n*FracPart[q])*(d+e*x^(-n))^FracPart[q]/(e+d*x^n)^FracPart[q]*Int[x^(-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]] && PosQ[n]


Int[(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  x^(-mn*FracPart[q])*(d+e*x^mn)^FracPart[q]/(e+d*x^(-mn))^FracPart[q]*Int[x^(mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
FreeQ[{a,c,d,e,mn,p,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && Not[IntegerQ[p]] && PosQ[n2]


Int[(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/(x^(2*n*FracPart[p])*(c+b*x^(-n)+a*x^(-2*n))^FracPart[p])*
    Int[x^(2*n*p)*(d+e*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]] && NegQ[n]


Int[(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+c*x^n2)^FracPart[p]/(x^(n2*FracPart[p])*(c+a*x^(2*mn))^FracPart[p])*
    Int[x^(n2*p)*(d+e*x^mn)^q*(c+a*x^(2*mn))^p,x] /;
FreeQ[{a,c,d,e,mn,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && Not[IntegerQ[p]] && NegQ[n2]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^(-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[mn,-n] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p]*
    Int[x^(-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p]))*
    Int[(d+e*x^n)^q*(f+g*x^n)^r*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,q,r},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,f,g,n,q,r},x] && EqQ[n2-2*n] && EqQ[c*d^2+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*
    Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*
    Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,f,g,n,p,q,r},x] && EqQ[n2-2*n] && EqQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[(f_.+g_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*f-g*(b-q))/(2*c*d-e*(b-q))*Int[1/Sqrt[a+b*x^2+c*x^4],x] - 
  (e*f-d*g)/(2*c*d-e*(b-q))*Int[(b-q+2*c*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
 NeQ[2*c*f-g*(b-q)]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveQ[b^2-4*a*c] && NeQ[c*d^2-b*d*e+a*e^2] && Not[NegativeQ[c]]


Int[(f_+g_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (c*f+g*q)/(c*d+e*q)*Int[1/Sqrt[a+c*x^4],x] + (e*f-d*g)/(c*d+e*q)*Int[(q-c*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
 NeQ[c*f+g*q]] /;
FreeQ[{a,c,d,e,f,g},x] && PositiveQ[-a*c] && NeQ[c*d^2+a*e^2] && Not[NegativeQ[c]]


Int[(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n,p,q},x] && EqQ[n2-2*n] && EqQ[non2-n/2] && EqQ[d2*e1+d1*e2] && 
  (IntegerQ[q] || PositiveQ[d1] && PositiveQ[d2])


Int[(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (d1+e1*x^(n/2))^FracPart[q]*(d2+e2*x^(n/2))^FracPart[q]/(d1*d2+e1*e2*x^n)^FracPart[q]*
    Int[(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n,p,q},x] && EqQ[n2-2*n] && EqQ[non2-n/2] && EqQ[d2*e1+d1*e2]


Int[(A_+B_.*x_^m_.)*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  A*Int[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] + B*Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n,p,q},x] && EqQ[n2-2*n] && EqQ[m-n+1]


Int[(A_+B_.*x_^m_.)*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  A*Int[(d+e*x^n)^q*(a+c*x^(2*n))^p,x] + B*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,A,B,m,n,p,q},x] && EqQ[n2-2*n] && EqQ[m-n+1]





(* ::Subsection::Closed:: *)
(*1.2.3.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p*)


Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^m/(n*e^((m+1)/n-1))*Subst[Int[(e*x)^(q+(m+1)/n-1)*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,e,f,m,n,p,q},x] && EqQ[n2-2*n] && (IntegerQ[m] || PositiveQ[f]) && IntegerQ[Simplify[(m+1)/n]]


Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^m/(n*e^((m+1)/n-1))*Subst[Int[(e*x)^(q+(m+1)/n-1)*(a+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,c,e,f,m,n,p,q},x] && EqQ[n2-2*n] && (IntegerQ[m] || PositiveQ[f]) && IntegerQ[Simplify[(m+1)/n]]


Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^m*e^IntPart[q]*(e*x^n)^FracPart[q]/x^(n*FracPart[q])*Int[x^(m+n*q)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,e,f,m,n,p,q},x] && EqQ[n2-2*n] && (IntegerQ[m] || PositiveQ[f]) && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^m*e^IntPart[q]*(e*x^n)^FracPart[q]/x^(n*FracPart[q])*Int[x^(m+n*q)*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,e,f,m,n,p,q},x] && EqQ[n2-2*n] && (IntegerQ[m] || PositiveQ[f]) && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[(f_*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,e,f,m,n,p,q},x] && EqQ[n2-2*n] && Not[IntegerQ[m]]


Int[(f_*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,e,f,m,n,p,q},x] && EqQ[n2-2*n] && Not[IntegerQ[m]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2-2*n] && EqQ[Simplify[m-n+1]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[(d+e*x)^q*(a+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,c,d,e,m,n,p,q},x] && EqQ[n2-2*n] && EqQ[Simplify[m-n+1]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m+n*(2*p+q))*(e+d*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && EqQ[n2-2*n] && IntegersQ[p,q] && NegQ[n]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m+n*(2*p+q))*(e+d*x^(-n))^q*(c+a*x^(-2*n))^p,x] /;
FreeQ[{a,c,d,e,m,n},x] && EqQ[n2-2*n] && IntegersQ[p,q] && NegQ[n]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/n*Subst[Int[x^((m+1)/n-1)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]] && PositiveIntegerQ[m,n,(m+1)/n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/(c^IntPart[p]*(b/2+c*x^n)^(2*FracPart[p]))*
    Int[(f*x)^m*(d+e*x^n)^q*(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && EqQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x)^q*(a+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,c,d,e,m,n,p,q},x] && EqQ[n2-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(f*x)^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(f*x)^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,f,q,m,n,q},x] && EqQ[n2-2*n] && EqQ[c*d^2+a*e^2] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*
    Int[(f*x)^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && EqQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*Int[(f*x)^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && EqQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) + 
  1/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1))*Int[x^Mod[m,n]*(d+e*x^n)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^n)*(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)*x^(m-Mod[m,n])*(a+b*x^n+c*x^(2*n))^p-
      (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n,p] && IntegersQ[m,q] && q<-1 && m>0


Int[x_^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) + 
  1/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1))*Int[x^Mod[m,n]*(d+e*x^n)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^n)*(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)*x^(m-Mod[m,n])*(a+c*x^(2*n))^p-
      (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
FreeQ[{a,c,d,e},x] && EqQ[n2-2*n] && PositiveIntegerQ[n,p] && IntegersQ[m,q] && q<-1 && m>0


Int[x_^m_*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) + 
  (-d)^((m-Mod[m,n])/n-1)/(n*e^(2*p)*(q+1))*Int[x^m*(d+e*x^n)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^n)*(n*(-d)^(-(m-Mod[m,n])/n+1)*e^(2*p)*(q+1)*(a+b*x^n+c*x^(2*n))^p - 
  (e^(-(m-Mod[m,n])/n)*(c*d^2-b*d*e+a*e^2)^p*x^(-(m-Mod[m,n])))*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n,p] && IntegersQ[m,q] && q<-1 && m<0


Int[x_^m_*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) + 
  (-d)^((m-Mod[m,n])/n-1)/(n*e^(2*p)*(q+1))*Int[x^m*(d+e*x^n)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^n)*(n*(-d)^(-(m-Mod[m,n])/n+1)*e^(2*p)*(q+1)*(a+c*x^(2*n))^p - 
  (e^(-(m-Mod[m,n])/n)*(c*d^2+a*e^2)^p*x^(-(m-Mod[m,n])))*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
FreeQ[{a,c,d,e},x] && EqQ[n2-2*n] && PositiveIntegerQ[n,p] && IntegersQ[m,q] && q<-1 && m<0


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  c^p*(f*x)^(m+2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*f^(2*n*p-n+1)*(m+2*n*p+n*q+1)) + 
  1/(e*(m+2*n*p+n*q+1))*Int[(f*x)^m*(d+e*x^n)^q*
    ExpandToSum[e*(m+2*n*p+n*q+1)*((a+b*x^n+c*x^(2*n))^p-c^p*x^(2*n*p))-d*c^p*(m+2*n*p-n+1)*x^(2*n*p-n),x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n,p] && 2*n*p>n-1 && 
  Not[IntegerQ[q]] && NeQ[m+2*n*p+n*q+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  c^p*(f*x)^(m+2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*f^(2*n*p-n+1)*(m+2*n*p+n*q+1)) + 
  1/(e*(m+2*n*p+n*q+1))*Int[(f*x)^m*(d+e*x^n)^q*
    ExpandToSum[e*(m+2*n*p+n*q+1)*((a+c*x^(2*n))^p-c^p*x^(2*n*p))-d*c^p*(m+2*n*p-n+1)*x^(2*n*p-n),x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && EqQ[n2-2*n] && PositiveIntegerQ[n,p] && 2*n*p>n-1 && 
  Not[IntegerQ[q]] && NeQ[m+2*n*p+n*q+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[n2-2*n] && PositiveIntegerQ[n,p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && EqQ[n2-2*n] && EqQ[n2-2*n] && PositiveIntegerQ[n,p]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(d+e*x^(n/k))^q*(a+b*x^(n/k)+c*x^(2*n/k))^p,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(d+e*x^(n/k))^q*(a+c*x^(2*n/k))^p,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,c,d,e,p,q},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/f*Subst[Int[x^(k*(m+1)-1)*(d+e*x^(k*n)/f^n)^q*(a+b*x^(k*n)/f^n+c*x^(2*k*n)/f^(2*n))^p,x],x,(f*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && FractionQ[m] && IntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/f*Subst[Int[x^(k*(m+1)-1)*(d+e*x^(k*n)/f)^q*(a+c*x^(2*k*n)/f)^p,x],x,(f*x)^(1/k)]] /;
FreeQ[{a,c,d,e,f,p,q},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && FractionQ[m] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p*(d*(m+n*(2*p+1)+1)+e*(m+1)*x^n)/(f*(m+1)*(m+n*(2*p+1)+1)) + 
  n*p/(f^n*(m+1)*(m+n*(2*p+1)+1))*Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1)*
      Simp[2*a*e*(m+1)-b*d*(m+n*(2*p+1)+1)+(b*e*(m+1)-2*c*d*(m+n*(2*p+1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-1 && 
  m+n*(2*p+1)+1!=0 && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+c*x^(2*n))^p*(d*(m+n*(2*p+1)+1)+e*(m+1)*x^n)/(f*(m+1)*(m+n*(2*p+1)+1)) + 
  2*n*p/(f^n*(m+1)*(m+n*(2*p+1)+1))*Int[(f*x)^(m+n)*(a+c*x^(2*n))^(p-1)*(a*e*(m+1)-c*d*(m+n*(2*p+1)+1)*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-1 && 
  m+n*(2*p+1)+1!=0 && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p*(b*e*n*p+c*d*(m+n*(2*p+1)+1)+c*e*(2*n*p+m+1)*x^n)/
    (c*f*(2*n*p+m+1)*(m+n*(2*p+1)+1)) + 
  n*p/(c*(2*n*p+m+1)*(m+n*(2*p+1)+1))*Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p-1)*
    Simp[2*a*c*d*(m+n*(2*p+1)+1)-a*b*e*(m+1)+(2*a*c*e*(2*n*p+m+1)+b*c*d*(m+n*(2*p+1)+1)-b^2*e*(m+n*p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p>0 && 
  NeQ[2*n*p+m+1] && NeQ[m+n*(2*p+1)+1] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+c*x^(2*n))^p*(c*d*(m+n*(2*p+1)+1)+c*e*(2*n*p+m+1)*x^n)/(c*f*(2*n*p+m+1)*(m+n*(2*p+1)+1)) + 
  2*a*n*p/((2*n*p+m+1)*(m+n*(2*p+1)+1))*Int[(f*x)^m*(a+c*x^(2*n))^(p-1)*Simp[d*(m+n*(2*p+1)+1)+e*(2*n*p+m+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[p] && p>0 && 
  NeQ[2*n*p+m+1] && NeQ[m+n*(2*p+1)+1] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  f^(n-1)*(f*x)^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(b*d-2*a*e-(b*e-2*c*d)*x^n)/(n*(p+1)*(b^2-4*a*c)) + 
  f^n/(n*(p+1)*(b^2-4*a*c))*Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1)*
      Simp[(n-m-1)*(b*d-2*a*e)+(2*n*p+2*n+m+1)*(b*e-2*c*d)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m>n-1 && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  f^(n-1)*(f*x)^(m-n+1)*(a+c*x^(2*n))^(p+1)*(a*e-c*d*x^n)/(2*a*c*n*(p+1)) + 
  f^n/(2*a*c*n*(p+1))*Int[(f*x)^(m-n)*(a+c*x^(2*n))^(p+1)*(a*e*(n-m-1)+c*d*(2*n*p+2*n+m+1)*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>n-1 && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(d*(b^2-2*a*c)-a*b*e+(b*d-2*a*e)*c*x^n)/(a*f*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*
      Simp[d*(b^2*(m+n*(p+1)+1)-2*a*c*(m+2*n*(p+1)+1))-a*b*e*(m+1)+c*(m+n*(2*p+3)+1)*(b*d-2*a*e)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && 
  IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)*(d+e*x^n)/(2*a*f*n*(p+1)) + 
  1/(2*a*n*(p+1))*Int[(f*x)^m*(a+c*x^(2*n))^(p+1)*Simp[d*(m+2*n*(p+1)+1)+e*(m+n*(2*p+3)+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  e*f^(n-1)*(f*x)^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+n(2*p+1)+1)) - 
  f^n/(c*(m+n(2*p+1)+1))*
    Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^p*Simp[a*e*(m-n+1)+(b*e*(m+n*p+1)-c*d*(m+n(2*p+1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>n-1 && 
  NeQ[m+n(2*p+1)+1] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  e*f^(n-1)*(f*x)^(m-n+1)*(a+c*x^(2*n))^(p+1)/(c*(m+n(2*p+1)+1)) - 
  f^n/(c*(m+n(2*p+1)+1))*Int[(f*x)^(m-n)*(a+c*x^(2*n))^p*(a*e*(m-n+1)-c*d*(m+n(2*p+1)+1)*x^n),x] /;
FreeQ[{a,c,d,e,f,p},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m] && m>n-1 && NeQ[m+n(2*p+1)+1] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  d*(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*f*(m+1)) + 
  1/(a*f^n*(m+1))*Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^p*Simp[a*e*(m+1)-b*d*(m+n*(p+1)+1)-c*d*(m+2*n(p+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && 
  IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  d*(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)/(a*f*(m+1)) + 
  1/(a*f^n*(m+1))*Int[(f*x)^(m+n)*(a+c*x^(2*n))^p*(a*e*(m+1)-c*d*(m+2*n(p+1)+1)*x^n),x] /;
FreeQ[{a,c,d,e,f,p},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && IntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q-b*c,2]},
  c/(2*q*r)*Int[(f*x)^m*Simp[d*r-(c*d-e*q)*x^(n/2),x]/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(f*x)^m*Simp[d*r+(c*d-e*q)*x^(n/2),x]/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NegativeQ[b^2-4*a*c] && IntegersQ[m,n/2] && 0<m<n && PosQ[a*c]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q,2]},
  c/(2*q*r)*Int[(f*x)^m*Simp[d*r-(c*d-e*q)*x^(n/2),x]/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(f*x)^m*Simp[d*r+(c*d-e*q)*x^(n/2),x]/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveQ[a*c] && IntegersQ[m,n/2] && 0<m<n


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q-b*c,2]},
  c/(2*q*r)*Int[(f*x)^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(f*x)^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2-2*n] && NegativeQ[b^2-4*a*c] && IntegerQ[n/2] && n>2 && PosQ[a*c]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q,2]},
  c/(2*q*r)*Int[(f*x)^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(f*x)^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e,f,m},x] && EqQ[n2-2*n] && IntegerQ[n/2] && n>2 && PositiveQ[a*c]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (e/2+(2*c*d-b*e)/(2*q))*Int[(f*x)^m/(b/2-q/2+c*x^n),x] + (e/2-(2*c*d-b*e)/(2*q))*Int[(f*x)^m/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  -(e/2+c*d/(2*q))*Int[(f*x)^m/(q-c*x^n),x] + (e/2-c*d/(2*q))*Int[(f*x)^m/(q+c*x^n),x]] /;
FreeQ[{a,c,d,e,f,m},x] && EqQ[n2-2*n] && PositiveIntegerQ[n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[q] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,f,m},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && IntegerQ[q] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m,(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[q] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m,(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,f,m},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && IntegerQ[q] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  f^(2*n)/c^2*Int[(f*x)^(m-2*n)*(c*d-b*e+c*e*x^n)*(d+e*x^n)^(q-1),x] - 
  f^(2*n)/c^2*Int[(f*x)^(m-2*n)*(d+e*x^n)^(q-1)*Simp[a*(c*d-b*e)+(b*c*d-b^2*e+a*c*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q>0 && m>2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  f^(2*n)/c*Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] - 
  a*f^(2*n)/c*Int[(f*x)^(m-2*n)*(d+e*x^n)^q/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f,q},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m] && m>2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  e*f^n/c*Int[(f*x)^(m-n)*(d+e*x^n)^(q-1),x] - 
  f^n/c*Int[(f*x)^(m-n)*(d+e*x^n)^(q-1)*Simp[a*e-(c*d-b*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q>0 && n-1<m<=2n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  e*f^n/c*Int[(f*x)^(m-n)*(d+e*x^n)^(q-1),x] - 
  f^n/c*Int[(f*x)^(m-n)*(d+e*x^n)^(q-1)*Simp[a*e-c*d*x^n,x]/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m,q] && q>0 && n-1<m<=2n-1


Int[(f_.*x_)^m_*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  d/a*Int[(f*x)^m*(d+e*x^n)^(q-1),x] - 
  1/(a*f^n)*Int[(f*x)^(m+n)*(d+e*x^n)^(q-1)*Simp[b*d-a*e+c*d*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q>0 && m<0


Int[(f_.*x_)^m_*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  d/a*Int[(f*x)^m*(d+e*x^n)^(q-1),x] + 
  1/(a*f^n)*Int[(f*x)^(m+n)*(d+e*x^n)^(q-1)*Simp[a*e-c*d*x^n,x]/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m,q] && q>0 && m<0


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  d^2*f^(2*n)/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] - 
  f^(2*n)/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2*n)*(d+e*x^n)^(q+1)*Simp[a*d+(b*d-a*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q<-1 && m>2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  d^2*f^(2*n)/(c*d^2+a*e^2)*Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] - 
  a*f^(2*n)/(c*d^2+a*e^2)*Int[(f*x)^(m-2*n)*(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m,q] && q<-1 && m>2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  -d*e*f^n/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-n)*(d+e*x^n)^q,x] + 
  f^n/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-n)*(d+e*x^n)^(q+1)*Simp[a*e+c*d*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q<-1 && n-1<m<=2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  -d*e*f^n/(c*d^2+a*e^2)*Int[(f*x)^(m-n)*(d+e*x^n)^q,x] + 
  f^n/(c*d^2+a*e^2)*Int[(f*x)^(m-n)*(d+e*x^n)^(q+1)*Simp[a*e+c*d*x^n,x]/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m,q] && q<-1 && n-1<m<=2*n-1


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  e^2/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^m*(d+e*x^n)^q,x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^m*(d+e*x^n)^(q+1)*Simp[c*d-b*e-c*e*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[q] && q<-1


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
  e^2/(c*d^2+a*e^2)*Int[(f*x)^m*(d+e*x^n)^q,x] + 
  c/(c*d^2+a*e^2)*Int[(f*x)^m*(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f,m},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[q] && q<-1


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q,(f*x)^m/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,f,q,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q,(f*x)^m/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,f,q,n},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q,1/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,f,m,q,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q,1/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,f,m,q,n},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  1/d^2*Int[(f*x)^m*(a*d+(b*d-a*e)*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] + 
  (c*d^2-b*d*e+a*e^2)/(d^2*f^(2*n))*Int[(f*x)^(m+2*n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-n


Int[(f_.*x_)^m_*(a_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  a/d^2*Int[(f*x)^m*(d-e*x^n)*(a+c*x^(2*n))^(p-1),x] + 
  (c*d^2+a*e^2)/(d^2*f^(2*n))*Int[(f*x)^(m+2*n)*(a+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-n


Int[(f_.*x_)^m_*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  1/(d*e)*Int[(f*x)^m*(a*e+c*d*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] - 
  (c*d^2-b*d*e+a*e^2)/(d*e*f^n)*Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<0


Int[(f_.*x_)^m_*(a_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  1/(d*e)*Int[(f*x)^m*(a*e+c*d*x^n)*(a+c*x^(2*n))^(p-1),x] - 
  (c*d^2+a*e^2)/(d*e*f^n)*Int[(f*x)^(m+n)*(a+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<0


Int[(f_.*x_)^m_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  -f^(2*n)/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2*n)*(a*d+(b*d-a*e)*x^n)*(a+b*x^n+c*x^(2*n))^p,x] + 
  d^2*f^(2*n)/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2*n)*(a+b*x^n+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>n


Int[(f_.*x_)^m_.*(a_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  -a*f^(2*n)/(c*d^2+a*e^2)*Int[(f*x)^(m-2*n)*(d-e*x^n)*(a+c*x^(2*n))^p,x] + 
  d^2*f^(2*n)/(c*d^2+a*e^2)*Int[(f*x)^(m-2*n)*(a+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>n


Int[(f_.*x_)^m_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  f^n/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-n)*(a*e+c*d*x^n)*(a+b*x^n+c*x^(2*n))^p,x] - 
  d*e*f^n/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>0


Int[(f_.*x_)^m_.*(a_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  f^n/(c*d^2+a*e^2)*Int[(f*x)^(m-n)*(a*e+c*d*x^n)*(a+c*x^(2*n))^p,x] - 
  d*e*f^n/(c*d^2+a*e^2)*Int[(f*x)^(m-n)*(a+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>0


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n+c*x^(2*n))^p,(f*x)^m(d+e*x^n)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && (PositiveIntegerQ[q] || IntegersQ[m,q])


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^(2*n))^p,(f*x)^m(d+e*x^n)^q,x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && EqQ[n2-2*n] && PositiveIntegerQ[n] && (PositiveIntegerQ[q] || IntegersQ[m,q])


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && IntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,e,p,q},x] && EqQ[n2-2*n] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[m]},
  -g/f*Subst[Int[(d+e*f^(-n)*x^(-g*n))^q*(a+b*f^(-n)*x^(-g*n)+c*f^(-2*n)*x^(-2*g*n))^p/x^(g*(m+1)+1),x],x,1/(f*x)^(1/g)]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && FractionQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[m]},
  -g/f*Subst[Int[(d+e*f^(-n)*x^(-g*n))^q*(a+c*f^(-2*n)*x^(-2*g*n))^p/x^(g*(m+1)+1),x],x,1/(f*x)^(1/g)]] /;
FreeQ[{a,c,d,e,f,p,q},x] && EqQ[n2-2*n] && NegativeIntegerQ[n] && FractionQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -f^IntPart[m]*(f*x)^FracPart[m]*(x^(-1))^FracPart[m]*Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -f^IntPart[m]*(f*x)^FracPart[m]*(x^(-1))^FracPart[m]*Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && EqQ[n2-2*n] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*(d+e*x^(g*n))^q*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,d,e,m,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && FractionQ[n]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*(d+e*x^(g*n))^q*(a+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,c,d,e,m,p,q},x] && EqQ[n2-2*n] && FractionQ[n]


Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && FractionQ[n]


Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && EqQ[n2-2*n] && FractionQ[n]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(d+e*x^Simplify[n/(m+1)])^q*(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(d+e*x^Simplify[n/(m+1)])^q*(a+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,c,d,e,m,n,p,q},x] && EqQ[n2-2*n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && EqQ[n2-2*n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  2*c/r*Int[(f*x)^m*(d+e*x^n)^q/(b-r+2*c*x^n),x] - 2*c/r*Int[(f*x)^m*(d+e*x^n)^q/(b+r+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,e,f,m,n,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  With[{r=Rt[-a*c,2]},
  -c/(2*r)*Int[(f*x)^m*(d+e*x^n)^q/(r-c*x^n),x] - c/(2*r)*Int[(f*x)^m*(d+e*x^n)^q/(r+c*x^n),x]] /;
FreeQ[{a,c,d,e,f,m,n,q},x] && EqQ[n2-2*n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(d*(b^2-2*a*c)-a*b*e+(b*d-2*a*e)*c*x^n)/(a*f*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*
      Simp[d*(b^2*(m+n*(p+1)+1)-2*a*c*(m+2*n*(p+1)+1))-a*b*e*(m+1)+(m+n*(2*p+3)+1)*(b*d-2*a*e)*c*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)*(d+e*x^n)/(2*a*f*n*(p+1)) + 
  1/(2*a*n*(p+1))*Int[(f*x)^m*(a+c*x^(2*n))^(p+1)*Simp[d*(m+2*n*(p+1)+1)+e*(m+n*(2*p+3)+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,f,m,n},x] && EqQ[n2-2*n] && NegativeIntegerQ[p+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && NeQ[b^2-4*a*c] && (PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && (PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  f^m*Int[ExpandIntegrand[x^m*(a+c*x^(2*n))^p,(d/(d^2-e^2*x^(2*n))-e*x^n/(d^2-e^2*x^(2*n)))^(-q),x],x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && NegativeIntegerQ[q] && (IntegerQ[m] || PositiveQ[f])


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  (f*x)^m/x^m*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n] && NegativeIntegerQ[q] && Not[IntegerQ[m] || PositiveQ[f]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Defer[Int][(f*x)^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Defer[Int][(f*x)^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && EqQ[n2-2*n]


Int[u_^m_.*(d_+e_.*v_^n_)^q_.*(a_+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2-2*n] && LinearPairQ[u,v,x]


Int[u_^m_.*(d_+e_.*v_^n_)^q_.*(a_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,c,d,e,m,n,p},x] && EqQ[n2-2*n] && LinearPairQ[u,v,x]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && EqQ[mn,-n] && IntegerQ[q]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m+mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
FreeQ[{a,c,d,e,m,mn,p},x] && EqQ[n2,-2*mn] && IntegerQ[q]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m+2*n*p)*(d+e*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m-2*mn*p)*(d+e*x^mn)^q*(c+a*x^(2*mn))^p,x] /;
FreeQ[{a,c,d,e,m,mn,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  x^(n*FracPart[q])*(d+e*x^(-n))^FracPart[q]/(e+d*x^n)^FracPart[q]*Int[x^(m-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  x^(-mn*FracPart[q])*(d+e*x^mn)^FracPart[q]/(e+d*x^(-mn))^FracPart[q]*Int[x^(m+mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
FreeQ[{a,c,d,e,m,mn,p,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && Not[IntegerQ[p]]


Int[(f_*x_)^m_*(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^mn)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n]


Int[(f_*x_)^m_*(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^mn)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,mn,p,q},x] && EqQ[n2,-2*mn]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^(m-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && EqQ[mn,-n] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p]*
    Int[x^(m-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[p]]


Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+b*x^(-n)+c*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[mn,-n]


Int[(f_.*x_)^m_.*(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(f*x)^m*(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,n,p,q},x] && EqQ[n2-2*n] && EqQ[non2-n/2] && EqQ[d2*e1+d1*e2] && 
  (IntegerQ[q] || PositiveQ[d1] && PositiveQ[d2])


Int[(f_.*x_)^m_.*(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (d1+e1*x^(n/2))^FracPart[q]*(d2+e2*x^(n/2))^FracPart[q]/(d1*d2+e1*e2*x^n)^FracPart[q]*
    Int[(f*x)^m*(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,n,p,q},x] && EqQ[n2-2*n] && EqQ[non2-n/2] && EqQ[d2*e1+d1*e2]





(* ::Subsection::Closed:: *)
(*1.1.3.7 (c x)^m Pq(x) (a+b x^n)^p*)


Int[x_^m_.*(e_+f_.*x_^q_.+g_.*x_^r_.+h_.*x_^n_.)/(a_+c_.*x_^n_.)^(3/2),x_Symbol] :=
  -(2*a*g+4*a*h*x^(n/4)-2*c*f*x^(n/2))/(a*c*n*Sqrt[a+c*x^n]) /;
FreeQ[{a,c,e,f,g,h,m,n},x] && EqQ[q-n/4] && EqQ[r-3*n/4] && EqQ[4*m-n+4] && EqQ[c*e+a*h]


Int[(d_*x_)^m_.*(e_+f_.*x_^q_.+g_.*x_^r_.+h_.*x_^n_.)/(a_+c_.*x_^n_.)^(3/2),x_Symbol] :=
  (d*x)^m/x^m*Int[x^m*(e+f*x^(n/4)+g*x^((3*n)/4)+h*x^n)/(a+c*x^n)^(3/2),x] /;
FreeQ[{a,c,d,e,f,g,h,m,n},x] && EqQ[4*m-n+4] && EqQ[q-n/4] && EqQ[r-3*n/4] && EqQ[c*e+a*h]


Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_)^p_,x_Symbol] :=
  With[{n=Denominator[p]},
  n/b*Subst[Int[x^(n*p+n-1)*(-a*c/b+c*x^n/b)^m*ReplaceAll[Pq,x->-a/b+x^n/b],x],x,(a+b*x)^(1/n)]] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && FractionQ[p] && NegativeIntegerQ[m+1]


(* Int[Pq_*(a_+b_.*x_)^p_,x_Symbol] :=
  With[{n=Denominator[p]},
  n/b*Subst[Int[x^(n*p+n-1)*ReplaceAll[Pq,x->-a/b+x^n/b],x],x,(a+b*x)^(1/n)]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && FractionQ[p] *)


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  1/(m+1)*Subst[Int[SubstFor[x^(m+1),Pq,x]*(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && NeQ[m+1] && PositiveIntegerQ[Simplify[n/(m+1)]] && PolyQ[Pq,x^(m+1)]


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Coeff[Pq,x,n-1]*(a+b*x^n)^(p+1)/(b*n*(p+1)) + 
  Int[ExpandToSum[Pq-Coeff[Pq,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n,p] && NeQ[Coeff[Pq,x,n-1]]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PolyQ[Pq,x] && (PositiveIntegerQ[p] || EqQ[n-1])


Int[Pq_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,n},x] && PolyQ[Pq,x] && (PositiveIntegerQ[p] || EqQ[n-1])


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Pq,x]*(a+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[(m+1)/n]]


Int[(c_*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*Pq*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Pq*(a+b*x^n)^(p+1)/(b*n*(p+1)) - 
  1/(b*n*(p+1))*Int[D[Pq,x]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,m,n},x] && PolyQ[Pq,x] && EqQ[m-n+1] && RationalQ[p] && p<-1


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  1/d*Int[(d*x)^(m+1)*ExpandToSum[Pq/x,x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b,d,m,n,p},x] && PolyQ[Pq,x] && EqQ[Coeff[Pq,x,0]]


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Int[x*ExpandToSum[Pq/x,x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b,n,p},x] && PolyQ[Pq,x] && EqQ[Coeff[Pq,x,0]] && SumQ[Pq]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Module[{u=IntHide[x^m*Pq,x]},
  u*(a+b*x^n)^p - b*n*p*Int[x^(m+n)*(a+b*x^n)^(p-1)*ExpandToSum[u/x^(m+1),x],x]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m+Expon[Pq,x]+1<0


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],i},
  (c*x)^m*(a+b*x^n)^p*Sum[Coeff[Pq,x,i]*x^(i+1)/(m+n*p+i+1),{i,0,q}] + 
  a*n*p*Int[(c*x)^m*(a+b*x^n)^(p-1)*Sum[Coeff[Pq,x,i]*x^i/(m+n*p+i+1),{i,0,q}],x]] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && PositiveIntegerQ[(n-1)/2] && RationalQ[p] && p>0


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],i},
  (a+b*x^n)^p*Sum[Coeff[Pq,x,i]*x^(i+1)/(n*p+i+1),{i,0,q}] + 
  a*n*p*Int[(a+b*x^n)^(p-1)*Sum[Coeff[Pq,x,i]*x^i/(n*p+i+1),{i,0,q}],x]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[(n-1)/2] && RationalQ[p] && p>0


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],i},
  (a*Coeff[Pq,x,q]-b*x*ExpandToSum[Pq-Coeff[Pq,x,q]*x^q,x])*(a+b*x^n)^(p+1)/(a*b*n*(p+1)) + 
  1/(a*n*(p+1))*Int[Sum[(n*(p+1)+i+1)*Coeff[Pq,x,i]*x^i,{i,0,q-1}]*(a+b*x^n)^(p+1),x] /;
 q==n-1] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  -x*Pq*(a+b*x^n)^(p+1)/(a*n*(p+1)) + 
  1/(a*n*(p+1))*Int[ExpandToSum[n*(p+1)*Pq+D[x*Pq,x],x]*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && Expon[Pq,x]<n-1


Int[(d_+e_.*x_+f_.*x_^3+g_.*x_^4)/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
  -(2*a*f+4*a*g*x-2*b*e*x^2)/(4*a*b*Sqrt[a+b*x^4]) /;
FreeQ[{a,b,d,e,f,g},x] && EqQ[b*d+a*g]


Int[(d_+f_.*x_^3+g_.*x_^4)/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
  -(f+2*g*x)/(2*b*Sqrt[a+b*x^4]) /;
FreeQ[{a,b,d,f,g},x] && EqQ[b*d+a*g]


Int[(d_+e_.*x_+g_.*x_^4)/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
  -x*(2*a*g-b*e*x)/(2*a*b*Sqrt[a+b*x^4]) /;
FreeQ[{a,b,d,e,g},x] && EqQ[b*d+a*g]


Int[x_^2*(e_.+f_.*x_+h_.*x_^4)/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
  -(f-2*h*x^3)/(2*b*Sqrt[a+b*x^4]) /;
FreeQ[{a,b,e,f,h},x] && EqQ[b*e-3*a*h]


Int[x_^2*(e_.+h_.*x_^4)/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
  h*x^3/(b*Sqrt[a+b*x^4]) /;
FreeQ[{a,b,e,h},x] && EqQ[b*e-3*a*h]


Int[(d_+e_.*x_^2+f_.*x_^3+g_.*x_^4+h_.*x_^6)/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
  -(a*f-2*b*d*x-2*a*h*x^3)/(2*a*b*Sqrt[a+b*x^4]) /;
FreeQ[{a,b,d,e,f,g,h},x] && EqQ[b*e-3*a*h] && EqQ[b*d+a*g]


Int[(d_+e_.*x_^2+g_.*x_^4+h_.*x_^6)/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
  x*(b*d+a*h*x^2)/(a*b*Sqrt[a+b*x^4]) /;
FreeQ[{a,b,d,e,g,h},x] && EqQ[b*e-3*a*h] && EqQ[b*d+a*g]


Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Module[{Q=PolynomialQuotient[b^(Floor[(q-1)/n]+1)*Pq,a+b*x^n,x],R=PolynomialRemainder[b^(Floor[(q-1)/n]+1)*Pq,a+b*x^n,x],i},
  -x*R*(a+b*x^n)^(p+1)/(a*n*(p+1)*b^(Floor[(q-1)/n]+1)) + 
  1/(a*n*(p+1)*b^(Floor[(q-1)/n]+1))*Int[(a+b*x^n)^(p+1)*ExpandToSum[a*n*(p+1)*Q+n*(p+1)*R+D[x*R,x],x],x]] /;
 q>=n] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[x_^m_*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Module[{Q=PolynomialQuotient[a*b^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n,x],
          R=PolynomialRemainder[a*b^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n,x],i},
  -x*R*(a+b*x^n)^(p+1)/(a^2*n*(p+1)*b^(Floor[(q-1)/n]+1)) + 
  1/(a*n*(p+1)*b^(Floor[(q-1)/n]+1))*Int[x^m*(a+b*x^n)^(p+1)*
    ExpandToSum[n*(p+1)*x^(-m)*Q+Sum[(n*(p+1)+i+1)/a*Coeff[R,x,i]*x^(i-m),{i,0,n-1}],x],x]]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && NegativeIntegerQ[m]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=GCD[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*ReplaceAll[Pq,x->x^(1/g)]*(a+b*x^(n/g))^p,x],x,x^g] /;
 g!=1] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x^n] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  B^3/b*Int[1/(A^2-A*B*x+B^2*x^2),x] /;
FreeQ[{a,b,A,B},x] && EqQ[a*B^3-b*A^3]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  -r*(B*r-A*s)/(3*a*s)*Int[1/(r+s*x),x] + 
  r/(3*a*s)*Int[(r*(B*r+2*A*s)+s*(B*r-A*s)*x)/(r^2-r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b,A,B},x] && NeQ[a*B^3-b*A^3] && PosQ[a/b]


Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r*(B*r+A*s)/(3*a*s)*Int[1/(r-s*x),x] - 
  r/(3*a*s)*Int[(r*(B*r-2*A*s)-s*(B*r+A*s)*x)/(r^2+r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b,A,B},x] && NeQ[a*B^3-b*A^3] && NegQ[a/b]


Int[(A_+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  -C^2/b*Int[1/(B-C*x),x] /;
FreeQ[{a,b,A,B,C},x] && EqQ[B^2-A*C] && EqQ[b*B^3+a*C^3]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/b^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A*b^(2/3)-a^(1/3)*b^(1/3)*B-2*a^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/b^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[a^(1/3)*b^(1/3)*B+2*a^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/b^(1/3)},
  C/b*Int[1/(q+x),x] + C*q/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A*b^(2/3)-2*a^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/(-b)^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A*(-b)^(2/3)-(-a)^(1/3)*(-b)^(1/3)*B-2*(-a)^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/(-b)^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[(-a)^(1/3)*(-b)^(1/3)*B+2*(-a)^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/(-b)^(1/3)},
  C/b*Int[1/(q+x),x] + C*q/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A*(-b)^(2/3)-2*(-a)^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/b^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A*b^(2/3)+(-a)^(1/3)*b^(1/3)*B-2*(-a)^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/b^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[(-a)^(1/3)*b^(1/3)*B-2*(-a)^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a)^(1/3)/b^(1/3)},
  -C/b*Int[1/(q-x),x] - C*q/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A*b^(2/3)-2*(-a)^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/(-b)^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A*(-b)^(2/3)+a^(1/3)*(-b)^(1/3)*B-2*a^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/(-b)^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[a^(1/3)*(-b)^(1/3)*B-2*a^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=a^(1/3)/(-b)^(1/3)},
  -C/b*Int[1/(q-x),x] - C*q/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A*(-b)^(2/3)-2*a^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A-(a/b)^(1/3)*B-2*(a/b)^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[(a/b)^(1/3)*B+2*(a/b)^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  C/b*Int[1/(q+x),x] + C*q/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A-2*(a/b)^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[a/b,3]},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A-Rt[a/b,3]*B-2*Rt[a/b,3]^2*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[a/b,3]},
  C/b*Int[1/(q+x),x] + (B+C*q)/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[Rt[a/b,3]*B+2*Rt[a/b,3]^2*C]


Int[(A_.+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[a/b,3]},
  C/b*Int[1/(q+x),x] + C*q/b*Int[1/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A-2*Rt[a/b,3]^2*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A+(-a/b)^(1/3)*B-2*(-a/b)^(2/3)*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[(-a/b)^(1/3)*B-2*(-a/b)^(2/3)*C]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  -C/b*Int[1/(q-x),x] - C*q/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A-2*(-a/b)^(2/3)*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[-a/b,3]},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A+Rt[-a/b,3]*B-2*Rt[-a/b,3]^2*C]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[-a/b,3]},
  -C/b*Int[1/(q-x),x] + (B-C*q)/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[Rt[-a/b,3]*B-2*Rt[-a/b,3]^2*C]


Int[(A_.+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=Rt[-a/b,3]},
  -C/b*Int[1/(q-x),x] - C*q/b*Int[1/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A-2*Rt[-a/b,3]^2*C]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  Int[(A+B*x)/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,A,B,C},x] && (EqQ[a*B^3-b*A^3] || Not[RationalQ[a/b]])


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  B*Int[x/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,B,C},x] && Not[RationalQ[a/b]]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  A*Int[1/(a+b*x^3),x] + C*Int[x^2/(a+b*x^3),x] /;
FreeQ[{a,b,A,C},x] && Not[RationalQ[a,b,A,C]]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  q^2/a*Int[(A+C*q*x)/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A-B*(a/b)^(1/3)+C*(a/b)^(2/3)]


Int[x_*(B_.+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  C*q^3/a*Int[x/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[B*(a/b)^(1/3)-C*(a/b)^(2/3)]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  q^2/a*Int[(A+C*q*x)/(q^2-q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A+C*(a/b)^(2/3)]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  q/a*Int[(A*q+(A+B*q)*x)/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,B,C},x] && EqQ[A+B*(-a/b)^(1/3)+C*(-a/b)^(2/3)]


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  B*q^2/a*Int[x/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,B,C},x] && EqQ[B*(-a/b)^(1/3)+C*(-a/b)^(2/3)]


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  A*q/a*Int[(q+x)/(q^2+q*x+x^2),x]] /;
FreeQ[{a,b,A,C},x] && EqQ[A+C*(-a/b)^(2/3)]


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  q*(A-B*q+C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(2*A+B*q-C*q^2)-(A-B*q-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NeQ[A-B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NeQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b>0


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  -q*(B*q-C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(B*q-C*q^2)+(B*q+2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NeQ[B*q-C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b>0


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(a/b)^(1/3)},
  q*(A+C*q^2)/(3*a)*Int[1/(q+x),x] + 
  q/(3*a)*Int[(q*(2*A-C*q^2)-(A-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
 NeQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b>0


Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  q*(A+B*q+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(q*(2*A-B*q-C*q^2)+(A+B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NeQ[A+B*q+C*q^2]] /;
FreeQ[{a,b,A,B,C},x] && NeQ[a*B^3-b*A^3] && RationalQ[a/b] && a/b<0


Int[x_*(B_+C_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  q*(B*q+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(-q*(B*q+C*q^2)+(B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NeQ[B*q+C*q^2]] /;
FreeQ[{a,b,B,C},x] && RationalQ[a/b] && a/b<0


Int[(A_+C_.*x_^2)/(a_+b_.*x_^3),x_Symbol] :=
  With[{q=(-a/b)^(1/3)},
  q*(A+C*q^2)/(3*a)*Int[1/(q-x),x] + 
  q/(3*a)*Int[(q*(2*A-C*q^2)+(A-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
 NeQ[A+C*q^2]] /;
FreeQ[{a,b,A,C},x] && RationalQ[a/b] && a/b<0


Int[(c_.*x_)^m_.*Pq_/(a_+b_.*x_^n_),x_Symbol] :=
  With[{v=Sum[(c*x)^(m+ii)*(Coeff[Pq,x,ii]+Coeff[Pq,x,n/2+ii]*x^(n/2))/(c^ii*(a+b*x^n)),{ii,0,n/2-1}]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && PositiveIntegerQ[n/2] && Expon[Pq,x]<n


Int[Pq_/(a_+b_.*x_^n_),x_Symbol] :=
  With[{v=Sum[x^ii*(Coeff[Pq,x,ii]+Coeff[Pq,x,n/2+ii]*x^(n/2))/(a+b*x^n),{ii,0,n/2-1}]},
  Int[v,x] /;
 SumQ[v]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n/2] && Expon[Pq,x]<n


(* Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{q=Rt[b/a,3]},
  2*d*Sqrt[a+b*x^3]/(a*q^2*(1+Sqrt[3]+q*x)) + 
  3^(1/4)*Sqrt[2-Sqrt[3]]*d*(1+q*x)*Sqrt[(1-q*x+q^2*x^2)/(1+Sqrt[3]+q*x)^2]/(q^2*Sqrt[a+b*x^3]*Sqrt[(1+q*x)/(1+Sqrt[3]+q*x)^2])*
    EllipticE[ArcSin[(-1+Sqrt[3]-q*x)/(1+Sqrt[3]+q*x)],-7-4*Sqrt[3]] /;
 EqQ[c*q-d*(1-Sqrt[3])]] /;
FreeQ[{a,b,c,d},x] && PosQ[a] *)


Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  2*d*s^3*Sqrt[a+b*x^3]/(a*r^2*((1+Sqrt[3])*s+r*x)) - 
  3^(1/4)*Sqrt[2-Sqrt[3]]*d*s*(s+r*x)*Sqrt[(s^2-r*s*x+r^2*x^2)/((1+Sqrt[3])*s+r*x)^2]/
    (r^2*Sqrt[a+b*x^3]*Sqrt[s*(s+r*x)/((1+Sqrt[3])*s+r*x)^2])*
    EllipticE[ArcSin[((1-Sqrt[3])*s+r*x)/((1+Sqrt[3])*s+r*x)],-7-4*Sqrt[3]]] /;
FreeQ[{a,b,c,d},x] && PosQ[a] && EqQ[c*Rt[b/a,3]-d*(1-Sqrt[3])]


Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  (c*r-(1-Sqrt[3])*d*s)/r*Int[1/Sqrt[a+b*x^3],x] + d/r*Int[((1-Sqrt[3])*s+r*x)/Sqrt[a+b*x^3],x]] /;
FreeQ[{a,b,c,d},x] && PosQ[a] && NeQ[c*Rt[b/a,3]-d*(1-Sqrt[3])]


Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  2*d*s^3*Sqrt[a+b*x^3]/(a*r^2*((1-Sqrt[3])*s+r*x)) + 
  3^(1/4)*Sqrt[2+Sqrt[3]]*d*s*(s+r*x)*Sqrt[(s^2-r*s*x+r^2*x^2)/((1-Sqrt[3])*s+r*x)^2]/
    (r^2*Sqrt[a+b*x^3]*Sqrt[-s*(s+r*x)/((1-Sqrt[3])*s+r*x)^2])*
    EllipticE[ArcSin[((1+Sqrt[3])*s+r*x)/((1-Sqrt[3])*s+r*x)],-7+4*Sqrt[3]]] /;
FreeQ[{a,b,c,d},x] && NegQ[a] && EqQ[c*Rt[b/a,3]-d*(1+Sqrt[3])]


Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  (c*r-(1+Sqrt[3])*d*s)/r*Int[1/Sqrt[a+b*x^3],x] + d/r*Int[((1+Sqrt[3])*s+r*x)/Sqrt[a+b*x^3],x]] /;
FreeQ[{a,b,c,d},x] && NegQ[a] && NeQ[c*Rt[b/a,3]-d*(1+Sqrt[3])]


Int[(c_+d_.*x_^4)/Sqrt[a_+b_.*x_^6],x_Symbol] :=
  With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
  (1+Sqrt[3])*d*s^3*x*Sqrt[a+b*x^6]/(2*a*r^2*(s+(1+Sqrt[3])*r*x^2)) - 
  3^(1/4)*d*s*x*(s+r*x^2)*Sqrt[(s^2-r*s*x^2+r^2*x^4)/(s+(1+Sqrt[3])*r*x^2)^2]/
    (2*r^2*Sqrt[(r*x^2*(s+r*x^2))/(s+(1+Sqrt[3])*r*x^2)^2]*Sqrt[a+b*x^6])*
    EllipticE[ArcCos[(s+(1-Sqrt[3])*r*x^2)/(s+(1+Sqrt[3])*r*x^2)],(2+Sqrt[3])/4]] /;
FreeQ[{a,b,c,d},x] && EqQ[2*Rt[b/a,3]^2*c-(1-Sqrt[3])*d]


Int[(c_+d_.*x_^4)/Sqrt[a_+b_.*x_^6],x_Symbol] :=
  With[{q=Rt[b/a,3]},
  (2*c*q^2-(1-Sqrt[3])*d)/(2*q^2)*Int[1/Sqrt[a+b*x^6],x] + d/(2*q^2)*Int[(1-Sqrt[3]+2*q^2*x^4)/Sqrt[a+b*x^6],x]] /;
FreeQ[{a,b,c,d},x] && NeQ[2*Rt[b/a,3]^2*c-(1-Sqrt[3])*d]


Int[(c_+d_.*x_^2)/Sqrt[a_+b_.*x_^8],x_Symbol] :=
  -c*d*x^3*Sqrt[-(c-d*x^2)^2/(c*d*x^2)]*Sqrt[-d^2*(a+b*x^8)/(b*c^2*x^4)]/(Sqrt[2+Sqrt[2]]*(c-d*x^2)*Sqrt[a+b*x^8])*
    EllipticF[ArcSin[1/2*Sqrt[(Sqrt[2]*c^2+2*c*d*x^2+Sqrt[2]*d^2*x^4)/(c*d*x^2)]],-2*(1-Sqrt[2])] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c^4-a*d^4]


Int[(c_+d_.*x_^2)/Sqrt[a_+b_.*x_^8],x_Symbol] :=
  (d+Rt[b/a,4]*c)/(2*Rt[b/a,4])*Int[(1+Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] - 
  (d-Rt[b/a,4]*c)/(2*Rt[b/a,4])*Int[(1-Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c^4-a*d^4]


Int[Pq_/(x_*Sqrt[a_+b_.*x_^n_]),x_Symbol] :=
  Coeff[Pq,x,0]*Int[1/(x*Sqrt[a+b*x^n]),x] + 
  Int[ExpandToSum[(Pq-Coeff[Pq,x,0])/x,x]/Sqrt[a+b*x^n],x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && NeQ[Coeff[Pq,x,0]]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],j,k},
  Int[Sum[(c*x)^(m+j)/c^j*Sum[Coeff[Pq,x,j+k*n/2]*x^(k*n/2),{k,0,2*(q-j)/n+1}]*(a+b*x^n)^p,{j,0,n/2-1}],x]] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n/2] && Not[PolyQ[Pq,x^(n/2)]]


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],j,k},
  Int[Sum[x^j*Sum[Coeff[Pq,x,j+k*n/2]*x^(k*n/2),{k,0,2*(q-j)/n+1}]*(a+b*x^n)^p,{j,0,n/2-1}],x]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n/2] && Not[PolyQ[Pq,x^(n/2)]]


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Coeff[Pq,x,n-1]*Int[x^(n-1)*(a+b*x^n)^p,x] + 
  Int[ExpandToSum[Pq-Coeff[Pq,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && Expon[Pq,x]==n-1


Int[(c_.*x_)^m_.*Pq_/(a_+b_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq/(a+b*x^n),x],x] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && IntegerQ[n]


Int[Pq_/(a_+b_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[Pq/(a+b*x^n),x],x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && IntegerQ[n]


Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{Pq0=Coeff[Pq,x,0]},
    Pq0*(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) + 
    1/(2*a*c*(m+1))*Int[(c*x)^(m+1)*ExpandToSum[2*a*(m+1)*(Pq-Pq0)/x-2*b*Pq0*(m+n*(p+1)+1)*x^(n-1),x]*(a+b*x^n)^p,x] /;
 NeQ[Pq0]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && n-1<=Expon[Pq,x]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*(c*x)^(m+q-n+1)*(a+b*x^n)^(p+1)/(b*c^(q-n+1)*(m+q+n*p+1)) + 
    1/(b*(m+q+n*p+1))*Int[(c*x)^m*ExpandToSum[b*(m+q+n*p+1)*(Pq-Pqq*x^q)-a*Pqq*(m+q-n+1)*x^(q-n),x]*(a+b*x^n)^p,x]] /;
  NeQ[m+q+n*p+1] && q-n>=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n]


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*x^(q-n+1)*(a+b*x^n)^(p+1)/(b*(q+n*p+1)) + 
    1/(b*(q+n*p+1))*Int[ExpandToSum[b*(q+n*p+1)*(Pq-Pqq*x^q)-a*Pqq*(q-n+1)*x^(q-n),x]*(a+b*x^n)^p,x]] /;
  NeQ[q+n*p+1] && q-n>=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && PositiveIntegerQ[n]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  -Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n))^p/x^(m+q+2),x],x,1/x]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=Denominator[m],q=Expon[Pq,x]},
  -g/c*Subst[Int[ExpandToSum[x^(g*q)*ReplaceAll[Pq,x->c^(-1)*x^(-g)],x]*
    (a+b*c^(-n)*x^(-g*n))^p/x^(g*(m+q+1)+1),x],x,1/(c*x)^(1/g)]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && NegativeIntegerQ[n] && FractionQ[m]


Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  -(c*x)^m*(x^(-1))^m*Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n))^p/x^(m+q+2),x],x,1/x]] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,m,p},x] && PolyQ[Pq,x] && FractionQ[n]


Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && FractionQ[n]


Int[(c_*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*Pq*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && FractionQ[n]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[ReplaceAll[SubstFor[x^n,Pq,x],x->x^Simplify[n/(m+1)]]*(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*Pq*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(A_+B_.*x_^m_.)*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  A*Int[(a+b*x^n)^p,x] + B*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,A,B,m,n,p},x] && EqQ[m-n+1]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,m,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])


Int[Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])


Int[u_^m_.*Pq_*(a_+b_.*v_^n_.)^p_,x_Symbol] :=
  u^m/(Coeff[v,x,1]*v^m)*Subst[Int[x^m*SubstFor[v,Pq,x]*(a+b*x^n)^p,x],x,v] /;
FreeQ[{a,b,m,n,p},x] && LinearPairQ[u,v,x] && PolyQ[Pq,v^n]


Int[Pq_*(a_+b_.*v_^n_.)^p_,x_Symbol] :=
  1/Coeff[v,x,1]*Subst[Int[SubstFor[v,Pq,x]*(a+b*x^n)^p,x],x,v] /;
FreeQ[{a,b,n,p},x] && LinearQ[v,x] && PolyQ[Pq,v^n]


Int[(c_.*x_)^m_.*Pq_*(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
  Int[(c*x)^m*Pq*(a1*a2+b1*b2*x^(2*n))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && PolyQ[Pq,x] && EqQ[a2*b1+a1*b2] && (IntegerQ[p] || PositiveQ[a1] && PositiveQ[a2])


Int[Pq_*(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
  Int[Pq*(a1*a2+b1*b2*x^(2*n))^p,x] /;
FreeQ[{a1,b1,a2,b2,n,p},x] && PolyQ[Pq,x] && EqQ[a2*b1+a1*b2] && (IntegerQ[p] || PositiveQ[a1] && PositiveQ[a2])


Int[(c_.*x_)^m_.*Pq_*(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
  (a1+b1*x^n)^FracPart[p]*(a2+b2*x^n)^FracPart[p]/(a1*a2+b1*b2*x^(2*n))^FracPart[p]*
    Int[(c*x)^m*Pq*(a1*a2+b1*b2*x^(2*n))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && PolyQ[Pq,x] && EqQ[a2*b1+a1*b2] && Not[EqQ[n,1] && LinearQ[Pq,x]]


Int[Pq_*(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
  (a1+b1*x^n)^FracPart[p]*(a2+b2*x^n)^FracPart[p]/(a1*a2+b1*b2*x^(2*n))^FracPart[p]*
    Int[Pq*(a1*a2+b1*b2*x^(2*n))^p,x] /;
FreeQ[{a1,b1,a2,b2,n,p},x] && PolyQ[Pq,x] && EqQ[a2*b1+a1*b2] && Not[EqQ[n,1] && LinearQ[Pq,x]]


Int[(e_+f_.*x_^n_.+g_.*x_^n2_.)*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.)^p_.,x_Symbol] :=
  e*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(p+1)/(a*c) /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[n2-2*n] && EqQ[a*c*f-e*(b*c+a*d)*(n*(p+1)+1)] && EqQ[a*c*g-b*d*e*(2*n*(p+1)+1)]


Int[(e_+g_.*x_^n2_.)*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.)^p_.,x_Symbol] :=
  e*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(p+1)/(a*c) /;
FreeQ[{a,b,c,d,e,g,n,p},x] && EqQ[n2-2*n] && EqQ[n*(p+1)+1] && EqQ[a*c*g-b*d*e*(2*n*(p+1)+1)]


Int[(h_.*x_)^m_.*(e_+f_.*x_^n_.+g_.*x_^n2_.)*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.)^p_.,x_Symbol] :=
  e*(h*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(p+1)/(a*c*h*(m+1)) /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[n2-2*n] && EqQ[a*c*f*(m+1)-e*(b*c+a*d)*(m+n*(p+1)+1)] && 
  EqQ[a*c*g*(m+1)-b*d*e*(m+2*n*(p+1)+1)] && NeQ[m+1]


Int[(h_.*x_)^m_.*(e_+g_.*x_^n2_.)*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.)^p_.,x_Symbol] :=
  e*(h*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(p+1)/(a*c*h*(m+1)) /;
FreeQ[{a,b,c,d,e,g,h,m,n,p},x] && EqQ[n2-2*n] && EqQ[m+n*(p+1)+1] && EqQ[a*c*g*(m+1)-b*d*e*(m+2*n*(p+1)+1)] && 
  NeQ[m+1]


Int[(A_+B_.*x_^m_.)*(a_.+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  A*Int[(a+b*x^n)^p*(c+d*x^n)^q,x] + B*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,A,B,m,n,p,q},x] && NeQ[b*c-a*d] && EqQ[m-n+1]


Int[Px_^q_.*(a_.+b_.*(c_+d_.*x_)^n_)^p_,x_Symbol] :=
  With[{k=Denominator[n]},
  k/d*Subst[Int[SimplifyIntegrand[x^(k-1)*ReplaceAll[Px,x->x^k/d-c/d]^q*(a+b*x^(k*n))^p,x],x],x,(c+d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && PolynomialQ[Px,x] && IntegerQ[q] && RationalQ[n]





(* ::Subsection::Closed:: *)
(*1.2.3.5 (d x)^m Pq(x) (a+b x^n+c x^(2 n))^p*)


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[SubstFor[x^n,Pq,x]*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && EqQ[Simplify[m-n+1]]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && PositiveIntegerQ[p]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,n},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && PositiveIntegerQ[p]


Int[(d_+e_.*x_^n_.+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*x*(a+b*x^n+c*x^(2*n))^(p+1)/a /;
FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[n2-2*n] && EqQ[a*e-b*d*(n*(p+1)+1)] && EqQ[a*f-c*d*(2*n*(p+1)+1)]


Int[(d_+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*x*(a+b*x^n+c*x^(2*n))^(p+1)/a /;
FreeQ[{a,b,c,d,f,n,p},x] && EqQ[n2-2*n] && EqQ[n*(p+1)+1] && EqQ[c*d+a*f]


Int[(g_.*x_)^m_.*(d_+e_.*x_^n_.+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*(g*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*g*(m+1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[n2-2*n] && EqQ[a*e*(m+1)-b*d*(m+n*(p+1)+1)] && EqQ[a*f*(m+1)-c*d*(m+2*n*(p+1)+1)] && 
  NeQ[m+1]


Int[(g_.*x_)^m_.*(d_+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*(g*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*g*(m+1)) /;
FreeQ[{a,b,c,d,f,g,m,n,p},x] && EqQ[n2-2*n] && EqQ[m+n*(p+1)+1] && EqQ[c*d+a*f] && NeQ[m+1]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p]))*Int[(d*x)^m*Pq*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && EqQ[b^2-4*a*c] && Not[IntegerQ[2*p]]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p]))*Int[Pq*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && EqQ[b^2-4*a*c] && Not[IntegerQ[2*p]]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Pq,x]*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[(d_*x_)^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^m/x^m*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/d*Int[(d*x)^(m+1)*ExpandToSum[Pq/x,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && EqQ[Coeff[Pq,x,0]]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[x*ExpandToSum[Pq/x,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && EqQ[Coeff[Pq,x,0]] && SumQ[Pq]


Int[(d_+e_.*x_^n_+f_.*x_^n2_.+g_.*x_^n3_.)*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  x*(a*d*(n+1)+(a*e-b*d*(n*(p+1)+1))*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*(n+1)) /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[n2-2*n] && EqQ[n3-3*n] && NeQ[b^2-4*a*c] && 
  EqQ[a^2*g*(n+1)-c*(n*(2*p+3)+1)*(a*e-b*d*(n*(p+1)+1))] && 
  EqQ[a^2*f*(n+1)-a*c*d*(n+1)*(2*n*(p+1)+1)-b*(n*(p+2)+1)*(a*e-b*d*(n*(p+1)+1))]


Int[(d_+f_.*x_^n2_.+g_.*x_^n3_.)*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*x*(a*(n+1)-b*(n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*(n+1)) /;
FreeQ[{a,b,c,d,f,g,n,p},x] && EqQ[n2-2*n] && EqQ[n3-3*n] && NeQ[b^2-4*a*c] && 
  EqQ[a^2*g*(n+1)+c*b*d*(n*(2*p+3)+1)*(n*(p+1)+1)] && 
  EqQ[a^2*f*(n+1)-a*c*d*(n+1)*(2*n*(p+1)+1)+b^2*d*(n*(p+2)+1)*(n*(p+1)+1)]


Int[(d_+e_.*x_^n_+g_.*x_^n3_.)*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  x*(a*d*(n+1)+(a*e-b*d*(n*(p+1)+1))*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*(n+1)) /;
FreeQ[{a,b,c,d,e,g,n,p},x] && EqQ[n2-2*n] && EqQ[n3-3*n] && NeQ[b^2-4*a*c] && 
  EqQ[a^2*g*(n+1)-c*(n*(2*p+3)+1)*(a*e-b*d*(n*(p+1)+1))] && 
  EqQ[a*c*d*(n+1)*(2*n*(p+1)+1)+b*(n*(p+2)+1)*(a*e-b*d*(n*(p+1)+1))]


Int[(d_+g_.*x_^n3_.)*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d*x*(a*(n+1)-b*(n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*(n+1)) /;
FreeQ[{a,b,c,d,g,n,p},x] && EqQ[n2-2*n] && EqQ[n3-3*n] && NeQ[b^2-4*a*c] && 
  EqQ[a^2*g*(n+1)+c*b*d*(n*(2*p+3)+1)*(n*(p+1)+1)] && 
  EqQ[a*c*d*(n+1)*(2*n*(p+1)+1)-b^2*d*(n*(p+2)+1)*(n*(p+1)+1)]


Int[x_^m_.*(e_+f_.*x_^q_.+g_.*x_^r_.+h_.*x_^s_.)/(a_+b_.*x_^n_.+c_.*x_^n2_.)^(3/2),x_Symbol] :=
  -(2*c*(b*f-2*a*g)+2*h*(b^2-4*a*c)*x^(n/2)+2*c*(2*c*f-b*g)*x^n)/(c*n*(b^2-4*a*c)*Sqrt[a+b*x^n+c*x^(2*n)]) /;
FreeQ[{a,b,c,e,f,g,h,m,n},x] && EqQ[n2-2*n] && EqQ[q-n/2] && EqQ[r-3*n/2] && EqQ[s-2*n] && 
  NeQ[b^2-4*a*c] && EqQ[2*m-n+2] && EqQ[c*e+a*h]


Int[(d_*x_)^m_.*(e_+f_.*x_^q_.+g_.*x_^r_.+h_.*x_^s_.)/(a_+b_.*x_^n_.+c_.*x_^n2_.)^(3/2),x_Symbol] :=
  (d*x)^m/x^m*Int[x^m*(e+f*x^(n/2)+g*x^((3*n)/2)+h*x^(2*n))/(a+b*x^n+c*x^(2*n))^(3/2),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[n2-2*n] && EqQ[q-n/2] && EqQ[r-3*n/2] && EqQ[s-2*n] && 
  NeQ[b^2-4*a*c] && EqQ[2*m-n+2] && EqQ[c*e+a*h]


Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],i},
  -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c))*
    Sum[((b^2-2*a*c)*Coeff[Pq,x,i]-a*b*Coeff[Pq,x,n+i])*x^i+
      c*(b*Coeff[Pq,x,i]-2*a*Coeff[Pq,x,n+i])*x^(n+i),{i,0,n-1}] + 
  1/(a*n*(p+1)*(b^2-4*a*c))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*
    Sum[((b^2*(n*(p+1)+i+1)-2*a*c*(2*n*(p+1)+i+1))*Coeff[Pq,x,i]-a*b*(i+1)*Coeff[Pq,x,n+i])*x^i+
      c*(n*(2*p+3)+i+1)*(b*Coeff[Pq,x,i]-2*a*Coeff[Pq,x,n+i])*x^(n+i),{i,0,n-1}],x] /;
 q<2*n] /;
FreeQ[{a,b,c},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Module[{Q=PolynomialQuotient[(b*c)^(Floor[(q-1)/n]+1)*Pq,a+b*x^n+c*x^(2*n),x],
          R=PolynomialRemainder[(b*c)^(Floor[(q-1)/n]+1)*Pq,a+b*x^n+c*x^(2*n),x],i},
  -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*
    Sum[((b^2-2*a*c)*Coeff[R,x,i]-a*b*Coeff[R,x,n+i])*x^i+
      c*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}] + 
  1/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*Int[(a+b*x^n+c*x^(2*n))^(p+1)*ExpandToSum[a*n*(p+1)*(b^2-4*a*c)*Q+
    Sum[((b^2*(n*(p+1)+i+1)-2*a*c*(2*n*(p+1)+i+1))*Coeff[R,x,i]-a*b*(i+1)*Coeff[R,x,n+i])*x^i+
     c*(n*(2*p+3)+i+1)*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}],x],x]] /;
 q>=2*n] /;
FreeQ[{a,b,c},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[x_^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x]},
  Module[{Q=PolynomialQuotient[a*(b*c)^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n+c*x^(2*n),x],
          R=PolynomialRemainder[a*(b*c)^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n+c*x^(2*n),x],i},
  -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*
    Sum[((b^2-2*a*c)*Coeff[R,x,i]-a*b*Coeff[R,x,n+i])*x^i+
      c*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}] + 
  1/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*Int[x^m*(a+b*x^n+c*x^(2*n))^(p+1)*
    ExpandToSum[n*(p+1)*(b^2-4*a*c)*x^(-m)*Q+
      Sum[((b^2*(n*(p+1)+i+1)/a-2*c*(2*n*(p+1)+i+1))*Coeff[R,x,i]-b*(i+1)*Coeff[R,x,n+i])*x^(i-m)+
       c*(n*(2*p+3)+i+1)*(b/a*Coeff[R,x,i]-2*Coeff[R,x,n+i])*x^(n+i-m),{i,0,n-1}],x],x]] /;
 q>=2*n] /;
FreeQ[{a,b,c},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[p] && p<-1 && NegativeIntegerQ[m]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  With[{g=GCD[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*ReplaceAll[Pq,x->x^(1/g)]*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g] /;
 g!=1] /;
FreeQ[{a,b,c,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_.*Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && NiceSqrtQ[b^2-4*a*c]


Int[Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  (NiceSqrtQ[b^2-4*a*c] || Expon[Pq,x]<n)


Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    c^p*Pqq*Log[a+b*x+c*x^2]/2 + 
    1/2*Int[ExpandToSum[2*Pq-c^p*Pqq*(b+2*c*x)/(a+b*x+c*x^2)^(p+1),x]*(a+b*x+c*x^2)^p,x]] /;
  q+2*p+1==0] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && NegativeIntegerQ[p]


Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    c^p*Pqq*ArcTanh[(b+2*c*x)/(2*Rt[c,2]*Sqrt[a+b*x+c*x^2])] + 
    Int[ExpandToSum[Pq-c^(p+1/2)*Pqq/(a+b*x+c*x^2)^(p+1/2),x]*(a+b*x+c*x^2)^p,x]] /;
  q+2*p+1==0] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && NegativeIntegerQ[p+1/2] && PosQ[c]


Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    -(-c)^p*Pqq*ArcTan[(b+2*c*x)/(2*Rt[-c,2]*Sqrt[a+b*x+c*x^2])] + 
    Int[ExpandToSum[Pq-(-c)^(p+1/2)*Pqq/(a+b*x+c*x^2)^(p+1/2),x]*(a+b*x+c*x^2)^p,x]] /;
  q+2*p+1==0] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && NegativeIntegerQ[p+1/2] && NegQ[c]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*(d*x)^(m+q-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*d^(q-2*n+1)*(m+q+2*n*p+1)) + 
    Int[(d*x)^m*ExpandToSum[Pq-Pqq*x^q-Pqq*(a*(m+q-2*n+1)*x^(q-2*n)+b*(m+q+n*(p-1)+1)*x^(q-n))/(c*(m+q+2*n*p+1)),x]*
      (a+b*x^n+c*x^(2*n))^p,x]] /;
  q>=2*n && m+q+2*n*p+1!=0 && (IntegerQ[2*p] || n==1 && IntegerQ[4*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*x^(q-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(q+2*n*p+1)) + 
    Int[ExpandToSum[Pq-Pqq*x^q-Pqq*(a*(q-2*n+1)*x^(q-2*n)+b*(q+n*(p-1)+1)*x^(q-n))/(c*(q+2*n*p+1)),x]*(a+b*x^n+c*x^(2*n))^p,x]] /;
  q>=2*n && q+2*n*p+1!=0 && (IntegerQ[2*p] || n==1 && IntegerQ[4*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,c,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],j,k},
  Int[Sum[1/d^j*(d*x)^(m+j)*Sum[Coeff[Pq,x,j+k*n]*x^(k*n),{k,0,(q-j)/n+1}]*(a+b*x^n+c*x^(2*n))^p,{j,0,n-1}],x]] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[PolyQ[Pq,x^n]]


Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],j,k},
  Int[Sum[x^j*Sum[Coeff[Pq,x,j+k*n]*x^(k*n),{k,0,(q-j)/n+1}]*(a+b*x^n+c*x^(2*n))^p,{j,0,n-1}],x]] /;
FreeQ[{a,b,c,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[PolyQ[Pq,x^n]]


Int[(d_.*x_)^m_.*Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
  Int[RationalFunctionExpand[(d*x)^m*Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
  Int[RationalFunctionExpand[Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  -Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+q+2),x],x,1/x]] /;
FreeQ[{a,b,c,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[m],q=Expon[Pq,x]},
  -g/d*Subst[Int[ExpandToSum[x^(g*q)*ReplaceAll[Pq,x->d^(-1)*x^(-g)],x]*
    (a+b*d^(-n)*x^(-g*n)+c*d^(-2*n)*x^(-2*g*n))^p/x^(g*(m+q+1)+1),x],x,1/(d*x)^(1/g)]] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && FractionQ[m]


Int[(d_.*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  -(d*x)^m*(x^(-1))^m*Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+q+2),x],x,1/x]] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,m,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && FractionQ[n]


Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && FractionQ[n]


Int[(d_*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(m-1/2)*Sqrt[d*x]/Sqrt[x]*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && FractionQ[n] && PositiveIntegerQ[m+1/2]


Int[(d_*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(m+1/2)*Sqrt[x]/Sqrt[d*x]*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && FractionQ[n] && NegativeIntegerQ[m-1/2]


Int[(d_*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^m/x^m*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c] && FractionQ[n]


Int[x_^m_.*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[ReplaceAll[SubstFor[x^n,Pq,x],x->x^Simplify[n/(m+1)]]*(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && 
  Not[IntegerQ[n]]


Int[(d_*x_)^m_*Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^m/x^m*Int[x^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2-2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && 
  Not[IntegerQ[n]]


Int[(d_.*x_)^m_.*Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[(d*x)^m*Pq/(b-q+2*c*x^n),x] -
  2*c/q*Int[(d*x)^m*Pq/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c]


Int[Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[Pq/(b-q+2*c*x^n),x] -
  2*c/q*Int[Pq/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c,n},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NegativeIntegerQ[p+1]


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,n},x] && EqQ[n2-2*n] && PolyQ[Pq,x] && NegativeIntegerQ[p+1]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Defer[Int][(d*x)^m*Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2-2*n] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])


Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Defer[Int][Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2-2*n] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])


Int[u_^m_.*Pq_*(a_+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*SubstFor[v,Pq,x]*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2-2*n] && LinearPairQ[u,v,x] && PolyQ[Pq,v^n]


Int[Pq_*(a_+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  1/Coefficient[v,x,1]*Subst[Int[SubstFor[v,Pq,x]*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2-2*n] && LinearQ[v,x] && PolyQ[Pq,v^n]



