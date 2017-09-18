(* ::Package:: *)

(* ::Section:: *)
(*1.3.4 Normalizing algebraic functions*)


(* ::Subsection::Closed:: *)
(*1.3.4 Normalizing algebraic functions*)


Int[(a_.+b_.*(c_.*x_^n_)^q_)^p_.,x_Symbol] :=
  x/(c*x^n)^(1/n)*Subst[Int[(a+b*x^(n*q))^p,x],x,(c*x^n)^(1/n)] /;
FreeQ[{a,b,c,q,n,p},x] && IntegerQ[n*q]


Int[x_^m_.*(a_.+b_.*(c_.*x_^n_)^q_)^p_.,x_Symbol] :=
  x^(m+1)/(c*x^n)^((m+1)/n)*Subst[Int[x^m*(a+b*x^(n*q))^p,x],x,(c*x^n)^(1/n)] /;
FreeQ[{a,b,c,m,n,p,q},x] && IntegerQ[n*q] && IntegerQ[m]


Int[x_^m_.*(e_.*(a_+b_.*x_^n_.)^r_.)^p_*(f_.*(c_+d_.*x_^n_.)^s_)^q_,x_Symbol] :=
  (e*(a+b*x^n)^r)^p*(f*(c+d*x^n)^s)^q/((a+b*x^n)^(p*r)*(c+d*x^n)^(q*s))*
    Int[x^m*(a+b*x^n)^(p*r)*(c+d*x^n)^(q*s),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r,s},x]


Int[u_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  (b*e/d)^p*Int[u,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*c-a*d]


Int[u_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  Int[u*(e*(a+b*x^n))^p/(c+d*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && PositiveQ[b*d*e] && PositiveQ[c-a*d/b]


Int[(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  With[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[
    Int[x^(q*(p+1)-1)*(-a*e+c*x^q)^(1/n-1)/(b*e-d*x^q)^(1/n+1),x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && FractionQ[p] && IntegerQ[1/n]


Int[x_^m_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  With[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[
    Int[x^(q*(p+1)-1)*(-a*e+c*x^q)^(Simplify[(m+1)/n]-1)/(b*e-d*x^q)^(Simplify[(m+1)/n]+1),x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e,m,n},x] && FractionQ[p] && IntegerQ[Simplify[(m+1)/n]]


Int[u_^r_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  With[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[Int[SimplifyIntegrand[x^(q*(p+1)-1)*(-a*e+c*x^q)^(1/n-1)/(b*e-d*x^q)^(1/n+1)*
    ReplaceAll[u,x->(-a*e+c*x^q)^(1/n)/(b*e-d*x^q)^(1/n)]^r,x],x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[u,x] && FractionQ[p] && IntegerQ[1/n] && IntegerQ[r]


Int[x_^m_.*u_^r_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
  With[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[Int[SimplifyIntegrand[x^(q*(p+1)-1)*(-a*e+c*x^q)^((m+1)/n-1)/(b*e-d*x^q)^((m+1)/n+1)*
    ReplaceAll[u,x->(-a*e+c*x^q)^(1/n)/(b*e-d*x^q)^(1/n)]^r,x],x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[u,x] && FractionQ[p] && IntegerQ[1/n] && IntegersQ[m,r]


Int[(a_.+b_.*(c_./x_)^n_)^p_,x_Symbol] :=
  -c*Subst[Int[(a+b*x^n)^p/x^2,x],x,c/x] /;
FreeQ[{a,b,c,n,p},x]


Int[x_^m_.*(a_.+b_.*(c_./x_)^n_)^p_.,x_Symbol] :=
  -c^(m+1)*Subst[Int[(a+b*x^n)^p/x^(m+2),x],x,c/x] /;
FreeQ[{a,b,c,n,p},x] && IntegerQ[m]


Int[(d_.*x_)^m_*(a_.+b_.*(c_./x_)^n_)^p_.,x_Symbol] :=
  -c*(d*x)^m*(c/x)^m*Subst[Int[(a+b*x^n)^p/x^(m+2),x],x,c/x] /;
FreeQ[{a,b,c,d,m,n,p},x] && Not[IntegerQ[m]]


Int[(a_.+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_.,x_Symbol] :=
  -d*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^2,x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && EqQ[n2-2*n]


Int[x_^m_.*(a_+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_.,x_Symbol] :=
  -d^(m+1)*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && EqQ[n2-2*n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_.,x_Symbol] :=
  -d*(e*x)^m*(d/x)^m*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2-2*n] && Not[IntegerQ[m]]


Int[(a_.+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  -d*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^2,x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && EqQ[n2+2*n] && IntegerQ[2*n]


Int[x_^m_.*(a_+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  -d^(m+1)*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && EqQ[n2+2*n] && IntegerQ[2*n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  -d*(e*x)^m*(d/x)^m*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2+2*n] && Not[IntegerQ[m]] && IntegerQ[2*n]


Int[u_^m_,x_Symbol] :=
  Int[ExpandToSum[u,x]^m,x] /;
FreeQ[m,x] && LinearQ[u,x] && Not[LinearMatchQ[u,x]]


Int[u_^m_.*v_^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n,x] /;
FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
FreeQ[{m,n,p},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[u_^m_.*v_^n_.*w_^p_.*z_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p*ExpandToSum[z,x]^q,x] /;
FreeQ[{m,n,p,q},x] && LinearQ[{u,v,w,z},x] && Not[LinearMatchQ[{u,v,w,z},x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(c_.*x_)^m_.*u_^p_.,x_Symbol] :=
  Int[(c*x)^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{c,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[u_^p_.*v_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{p,q},x] && BinomialQ[{u,v},x] && EqQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && Not[BinomialMatchQ[{u,v},x]]


Int[(e_.*x_)^m_.*u_^p_.*v_^q_.,x_Symbol] :=
  Int[(e*x)^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{e,m,p,q},x] && BinomialQ[{u,v},x] && EqQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && Not[BinomialMatchQ[{u,v},x]]


Int[u_^m_.*v_^p_.*w_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p*ExpandToSum[w,x]^q,x] /;
FreeQ[{m,p,q},x] && BinomialQ[{u,v,w},x] && EqQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && 
  EqQ[BinomialDegree[u,x]-BinomialDegree[w,x]] && Not[BinomialMatchQ[{u,v,w},x]]


Int[(g_.*x_)^m_.*u_^p_.*v_^q_.*z_^r_.,x_Symbol] :=
  Int[(g*x)^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q*ExpandToSum[z,x]^r,x] /;
FreeQ[{g,m,p,q,r},x] && BinomialQ[{u,v,z},x] && EqQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && 
  EqQ[BinomialDegree[u,x]-BinomialDegree[z,x]] && Not[BinomialMatchQ[{u,v,z},x]]


Int[(c_.*x_)^m_.*Pq_*u_^p_.,x_Symbol] :=
  Int[(c*x)^m*Pq*ExpandToSum[u,x]^p,x] /;
FreeQ[{c,m,p},x] && PolyQ[Pq,x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && GeneralizedBinomialQ[u,x] && Not[GeneralizedBinomialMatchQ[u,x]]


Int[(c_.*x_)^m_.*u_^p_.,x_Symbol] :=
  Int[(c*x)^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{c,m,p},x] && GeneralizedBinomialQ[u,x] && Not[GeneralizedBinomialMatchQ[u,x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
FreeQ[{m,n,p},x] && LinearQ[{u,v},x] && QuadraticQ[w,x] && Not[LinearMatchQ[{u,v},x] && QuadraticMatchQ[w,x]]


Int[u_^p_.*v_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{p,q},x] && QuadraticQ[{u,v},x] && Not[QuadraticMatchQ[{u,v},x]]


Int[z_^m_.*u_^p_.*v_^q_.,x_Symbol] :=
  Int[ExpandToSum[z,x]^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{m,p,q},x] && LinearQ[z,x] && QuadraticQ[{u,v},x] && Not[LinearMatchQ[z,x] && QuadraticMatchQ[{u,v},x]]


Int[Pq_*u_^p_.,x_Symbol] :=
  Int[Pq*ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && PolyQ[Pq,x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]]


Int[u_^m_.*Pq_*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*Pq*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p},x] && PolyQ[Pq,x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]


Int[(d_.*x_)^m_.*u_^p_.,x_Symbol] :=
  Int[(d*x)^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{d,m,p},x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]


Int[u_^q_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^q*ExpandToSum[v,x]^p,x] /;
FreeQ[{p,q},x] && BinomialQ[u,x] && TrinomialQ[v,x] && Not[BinomialMatchQ[u,x] && TrinomialMatchQ[v,x]]


Int[u_^q_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^q*ExpandToSum[v,x]^p,x] /;
FreeQ[{p,q},x] && BinomialQ[u,x] && BinomialQ[v,x] && Not[BinomialMatchQ[u,x] && BinomialMatchQ[v,x]]


Int[(f_.*x_)^m_.*z_^q_.*u_^p_.,x_Symbol] :=
  Int[(f*x)^m*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
FreeQ[{f,m,p,q},x] && BinomialQ[z,x] && TrinomialQ[u,x] && Not[BinomialMatchQ[z,x] && TrinomialMatchQ[u,x]]


Int[(f_.*x_)^m_.*z_^q_.*u_^p_.,x_Symbol] :=
  Int[(f*x)^m*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
FreeQ[{f,m,p,q},x] && BinomialQ[z,x] && BinomialQ[u,x] && Not[BinomialMatchQ[z,x] && BinomialMatchQ[u,x]]


Int[Pq_*u_^p_.,x_Symbol] :=
  Int[Pq*ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && PolyQ[Pq,x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]


Int[(d_.*x_)^m_.*Pq_*u_^p_.,x_Symbol] :=
  Int[(d*x)^m*Pq*ExpandToSum[u,x]^p,x] /;
FreeQ[{d,m,p},x] && PolyQ[Pq,x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && GeneralizedTrinomialQ[u,x] && Not[GeneralizedTrinomialMatchQ[u,x]]


Int[(d_.*x_)^m_.*u_^p_.,x_Symbol] :=
  Int[(d*x)^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{d,m,p},x] && GeneralizedTrinomialQ[u,x] && Not[GeneralizedTrinomialMatchQ[u,x]]


Int[z_*u_^p_.,x_Symbol] :=
  Int[ExpandToSum[z,x]*ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && BinomialQ[z,x] && GeneralizedTrinomialQ[u,x] && 
  EqQ[BinomialDegree[z,x]-GeneralizedTrinomialDegree[u,x]] && Not[BinomialMatchQ[z,x] && GeneralizedTrinomialMatchQ[u,x]]


Int[(f_.*x_)^m_.*z_*u_^p_.,x_Symbol] :=
  Int[(f*x)^m*ExpandToSum[z,x]*ExpandToSum[u,x]^p,x] /;
FreeQ[{f,m,p},x] && BinomialQ[z,x] && GeneralizedTrinomialQ[u,x] && 
  EqQ[BinomialDegree[z,x]-GeneralizedTrinomialDegree[u,x]] && Not[BinomialMatchQ[z,x] && GeneralizedTrinomialMatchQ[u,x]]





(* ::Section:: *)
(*1.1.4 Improper Binomial Product Integration Rules*)


(* ::Subsection::Closed:: *)
(*1.1.4.1 (a x^j+b x^n)^p*)


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(b*(n-j)(p+1)*x^(n-1)) /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && EqQ[j*p-n+j+1]


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) + 
  (n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
FreeQ[{a,b,j,n},x] && Not[IntegerQ[p]] && NeQ[n-j] && NegativeIntegerQ[Simplify[(n*p+n-j+1)/(n-j)]] && RationalQ[p] && p<-1


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(a*(j*p+1)*x^(j-1)) - 
  b*(n*p+n-j+1)/(a*(j*p+1))*Int[x^(n-j)*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && NegativeIntegerQ[Simplify[(n*p+n-j+1)/(n-j)]] && NeQ[j*p+1]


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/(j*p+1) - 
  b*(n-j)*p/(j*p+1)*Int[x^n*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && p>0 && j*p+1<0


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/(n*p+1) + 
  a*(n-j)*p/(n*p+1)*Int[x^j*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && p>0 && NeQ[n*p+1]


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(b*(n-j)*(p+1)*x^(n-1)) - 
  (j*p-n+j+1)/(b*(n-j)*(p+1))*Int[(a*x^j+b*x^n)^(p+1)/x^n,x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && p<-1 && j*p+1>n-j


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) + 
  (n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && p<-1


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/(p*(n-j)) + a*Int[x^j*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b,j,n},x] && PositiveIntegerQ[p+1/2] && NeQ[n-j] && EqQ[Simplify[j*p+1]]


Int[1/Sqrt[a_.*x_^2+b_.*x_^n_.],x_Symbol] :=
  2/(2-n)*Subst[Int[1/(1-a*x^2),x],x,x/Sqrt[a*x^2+b*x^n]] /;
FreeQ[{a,b,n},x] && NeQ[n-2]


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) + 
  (n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
FreeQ[{a,b,j,n},x] && NegativeIntegerQ[p+1/2] && NeQ[n-j] && EqQ[Simplify[j*p+1]]


Int[1/Sqrt[a_.*x_^j_.+b_.*x_^n_.],x_Symbol] :=
  -2*Sqrt[a*x^j+b*x^n]/(b*(n-2)*x^(n-1)) - 
  a*(2*n-j-2)/(b*(n-2))*Int[1/(x^(n-j)*Sqrt[a*x^j+b*x^n]),x] /;
FreeQ[{a,b},x] && RationalQ[j,n] && 2*(n-1)<j<n


(* Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/(p*(n-j)*((a*x^j+b*x^n)/(b*x^n))^p)*Hypergeometric2F1[-p,-p,1-p,-a/(b*x^(n-j))] /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && EqQ[j*p+1] *)


(* Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^j+b*x^n)^p/((j*p+1)*((a*x^j+b*x^n)/(a*x^j))^p)*
    Hypergeometric2F1[-p,(j*p+1)/(n-j),(j*p+1)/(n-j)+1,-b*x^(n-j)/a] /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && NeQ[j*p+1] *)


Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^FracPart[p]/(x^(j*FracPart[p])*(a+b*x^(n-j))^FracPart[p])*Int[x^(j*p)*(a+b*x^(n-j))^p,x] /;
FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && PosQ[n-j]


Int[(a_.*u_^j_.+b_.*u_^n_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a*x^j+b*x^n)^p,x],x,u] /;
FreeQ[{a,b,j,n,p},x] && LinearQ[u,x] && NeQ[u-x]





(* ::Subsection::Closed:: *)
(*1.1.4.2 (c x)^m (a x^j+b x^n)^p*)


Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && EqQ[Simplify[m-n+1]]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && EqQ[m+n*p+n-j+1] && (IntegerQ[j] || PositiveQ[c])


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) + 
  c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,j,m,n},x] && Not[IntegerQ[p]] && NeQ[n-j] && NegativeIntegerQ[Simplify[(m+n*p+n-j+1)/(n-j)]] && 
  RationalQ[p] && p<-1 && (IntegerQ[j] || PositiveQ[c])


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(m+j*p+1)) - 
  b*(m+n*p+n-j+1)/(a*c^(n-j)*(m+j*p+1))*Int[(c*x)^(m+n-j)*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && NegativeIntegerQ[Simplify[(m+n*p+n-j+1)/(n-j)]] && 
  NeQ[m+j*p+1] && (IntegersQ[j,n] || PositiveQ[c])


Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && NegativeIntegerQ[Simplify[(m+n*p+n-j+1)/(n-j)]]


Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[(m+1)/n]] && 
  NeQ[n^2-1]


Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[(m+1)/n]] && 
  NeQ[n^2-1]


Int[(c_.*x_)^m_*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*(m+j*p+1)) - 
  b*p*(n-j)/(c^n*(m+j*p+1))*Int[(c*x)^(m+n)*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[p]] && RationalQ[j,m,n,p] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && p>0 && m+j*p+1<0


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*(m+n*p+1)) + 
  a*(n-j)*p/(c^j*(m+n*p+1))*Int[(c*x)^(m+j)*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && p>0 && NeQ[m+n*p+1]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a*x^j+b*x^n)^(p+1)/(b*(n-j)*(p+1)) - 
  c^n*(m+j*p-n+j+1)/(b*(n-j)*(p+1))*Int[(c*x)^(m-n)*(a*x^j+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c},x] && Not[IntegerQ[p]] && RationalQ[j,m,n,p] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && p<-1 && m+j*p+1>n-j


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) + 
  c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,m},x] && Not[IntegerQ[p]] && RationalQ[j,n,p] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && p<-1


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a*x^j+b*x^n)^(p+1)/(b*(m+n*p+1)) - 
  a*c^(n-j)*(m+j*p-n+j+1)/(b*(m+n*p+1))*Int[(c*x)^(m-(n-j))*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && Not[IntegerQ[p]] && RationalQ[j,n] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && PositiveQ[m+j*p+1-n+j] && 
  NeQ[m+n*p+1]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(m+j*p+1)) - 
  b*(m+n*p+n-j+1)/(a*c^(n-j)*(m+j*p+1))*Int[(c*x)^(m+n-j)*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && Not[IntegerQ[p]] && RationalQ[j,n] && 0<j<n && (IntegersQ[j,n] || PositiveQ[c]) && NegativeQ[m+j*p+1]


Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a*x^Simplify[j/(m+1)]+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && NeQ[m+1] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && NeQ[m+1] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*p*(n-j)) + a/c^j*Int[(c*x)^(m+j)*(a*x^j+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c,j,m,n},x] && PositiveIntegerQ[p+1/2] && NeQ[n-j] && EqQ[Simplify[m+j*p+1]] && (IntegerQ[j] || PositiveQ[c])


Int[x_^m_./Sqrt[a_.*x_^j_.+b_.*x_^n_.],x_Symbol] :=
  -2/(n-j)*Subst[Int[1/(1-a*x^2),x],x,x^(j/2)/Sqrt[a*x^j+b*x^n]] /;
FreeQ[{a,b,j,n},x] && EqQ[m-j/2+1] && NeQ[n-j]


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) + 
  c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1))*Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,j,m,n},x] && NegativeIntegerQ[p+1/2] && NeQ[n-j] && EqQ[Simplify[m+j*p+1]] && (IntegerQ[j] || PositiveQ[c])


Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && IntegerQ[p+1/2] && NeQ[n-j] && EqQ[Simplify[m+j*p+1]]


(* Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(b*p*(n-j)*x^(n+j*p))*Hypergeometric2F1[1,1,1-p,-a/(b*x^(n-j))] /;
FreeQ[{a,b,j,m,n,p},x] && NeQ[n-j] && EqQ[m+j*p+1] *)


(* Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^n)^(p+1)/(b*(p-1)*(n-j)*x^(2*n+j*(p-1)))*Hypergeometric2F1[1,2,2-p,-a/(b*x^(n-j))] /;
FreeQ[{a,b,j,m,n,p},x] && NeQ[n-j] && EqQ[m+n+(p-1)*j+1] *)


(* Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (x^(m-j+1)*(a*x^j+b*x^n)^(p+1))/(a*(m+j*p+1))*Hypergeometric2F1[1,(m+n*p+1)/(n-j)+1,(m+j*p+1)/(n-j)+1,-b*x^(n-j)/a] /;
FreeQ[{a,b,j,m,n,p},x] && NeQ[n-j] && NeQ[m+j*p+1] && NeQ[m+n+(p-1)*j+1] *)


Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
  c^IntPart[m]*(c*x)^FracPart[m]*(a*x^j+b*x^n)^FracPart[p]/
    (x^(FracPart[m]+j*FracPart[p])*(a+b*x^(n-j))^FracPart[p])*
    Int[x^(m+j*p)*(a+b*x^(n-j))^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n-j] && PosQ[n-j]


Int[u_^m_.*(a_.*v_^j_.+b_.*v_^n_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a*x^j+b*x^n)^p,x],x,v] /;
FreeQ[{a,b,j,m,n,p},x] && LinearPairQ[u,v,x]





(* ::Subsection::Closed:: *)
(*1.1.4.3 (e x)^m (a x^j+b x^k)^p (c+d x^n)^q*)


Int[x_^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a*x^Simplify[j/n]+b*x^Simplify[k/n])^p*(c+d*x)^q,x],x,x^n] /;
FreeQ[{a,b,c,d,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NeQ[k-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] && 
  IntegerQ[Simplify[(m+1)/n]] && NeQ[n^2-1]


Int[(e_*x_)^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^k)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NeQ[k-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] && 
  IntegerQ[Simplify[(m+1)/n]] && NeQ[n^2-1]


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
  c*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*(m+j*p+1)) /;
FreeQ[{a,b,c,d,e,j,m,n,p},x] && EqQ[jn-j-n] && Not[IntegerQ[p]] && NeQ[b*c-a*d] && 
  EqQ[a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1)] && (PositiveQ[e] || IntegersQ[j]) && NeQ[m+j*p+1]


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
  -e^(j-1)*(b*c-a*d)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*b*n*(p+1)) - 
  e^j*(a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(a*b*n*(p+1))*Int[(e*x)^(m-j)*(a*x^j+b*x^(j+n))^(p+1),x] /;
FreeQ[{a,b,c,d,e,j,m,n},x] && EqQ[jn-j-n] && Not[IntegerQ[p]] && NeQ[b*c-a*d] && RationalQ[j,m,p] && p<-1 && 0<j<=m && 
  (PositiveQ[e] || IntegerQ[j])


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
  c*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*(m+j*p+1)) + 
  (a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(a*e^n*(m+j*p+1))*Int[(e*x)^(m+n)*(a*x^j+b*x^(j+n))^p,x] /;
FreeQ[{a,b,c,d,e,j,p},x] && EqQ[jn-j-n] && Not[IntegerQ[p]] && NeQ[b*c-a*d] && RationalQ[m,n] && n>0 && 
  (m+j*p<-1 || IntegersQ[m-1/2,p-1/2] && p<0 && m<-n*p-1) && 
  (PositiveQ[e] || IntegersQ[j,n]) && NeQ[m+j*p+1] && NeQ[m-n+j*p+1]


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
  d*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(b*(m+n+p*(j+n)+1)) - 
  (a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(b*(m+n+p*(j+n)+1))*Int[(e*x)^m*(a*x^j+b*x^(j+n))^p,x] /;
FreeQ[{a,b,c,d,e,j,m,n,p},x] && EqQ[jn-j-n] && Not[IntegerQ[p]] && NeQ[b*c-a*d] && 
  NeQ[m+n+p*(j+n)+1] && (PositiveQ[e] || IntegerQ[j])


Int[x_^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  1/(m+1)*Subst[Int[(a*x^Simplify[j/(m+1)]+b*x^Simplify[k/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NeQ[k-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] && 
  NeQ[m+1] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_*x_)^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a*x^j+b*x^k)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NeQ[k-j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] && 
  NeQ[m+1] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
  e^IntPart[m]*(e*x)^FracPart[m]*(a*x^j+b*x^(j+n))^FracPart[p]/
    (x^(FracPart[m]+j*FracPart[p])*(a+b*x^n)^FracPart[p])*
    Int[x^(m+j*p)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,j,m,n,p,q},x] && EqQ[jn-j-n] && Not[IntegerQ[p]] && NeQ[b*c-a*d] && Not[EqQ[n-1] && EqQ[j-1]]





(* ::Subsection::Closed:: *)
(*1.1.4.4 (c x)^m Pq(x) (a x^j+b x^n)^p*)


Int[Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  With[{d=Denominator[n]},
  d*Subst[Int[x^(d-1)*ReplaceAll[SubstFor[x^n,Pq,x],x->x^(d*n)]*(a*x^(d*j)+b*x^(d*n))^p,x],x,x^(1/d)]] /;
FreeQ[{a,b,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n-j] && RationalQ[j,n] && IntegerQ[j/n] && -1<n<1


Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Pq,x]*(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[(m+1)/n]]


Int[(c_*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^(Sign[m]*Quotient[m,Sign[m]])*(c*x)^Mod[m,Sign[m]]/x^Mod[m,Sign[m]]*Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[(m+1)/n]] && RationalQ[m] && m^2>1


Int[(c_*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  With[{g=GCD[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*ReplaceAll[Pq,x->x^(1/g)]*(a*x^(j/g)+b*x^(n/g))^p,x],x,x^g] /;
 g!=1] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && PositiveIntegerQ[j,n,j/n] && IntegerQ[m]


Int[(c_.*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x]},
    With[{Pqq=Coeff[Pq,x,q]},
    Pqq*(c*x)^(m+q-n+1)*(a*x^j+b*x^n)^(p+1)/(b*c^(q-n+1)*(m+q+n*p+1)) + 
    Int[(c*x)^m*ExpandToSum[Pq-Pqq*x^q-a*Pqq*(m+q-n+1)*x^(q-n)/(b*(m+q+n*p+1)),x]*(a*x^j+b*x^n)^p,x]] /;
  q>n-1 && m+q+n*p+1!=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && Not[IntegerQ[p]] && PositiveIntegerQ[j,n] && j<n


Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[
    Int[ReplaceAll[SubstFor[x^n,Pq,x],x->x^Simplify[n/(m+1)]]*(a*x^Simplify[j/(m+1)]+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_*x_)^m_*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  c^(Sign[m]*Quotient[m,Sign[m]])*(c*x)^Mod[m,Sign[m]]/x^Mod[m,Sign[m]]*Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]] && RationalQ[m] && m^2>1


Int[(c_*x_)^m_*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
FreeQ[{a,b,c,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n-j] && IntegerQ[Simplify[j/n]] && 
  IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_.*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq*(a*x^j+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,j,m,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n]) && Not[IntegerQ[p]] && NeQ[n-j]


Int[Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a*x^j+b*x^n)^p,x],x] /;
FreeQ[{a,b,j,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n]) && Not[IntegerQ[p]] && NeQ[n-j]



