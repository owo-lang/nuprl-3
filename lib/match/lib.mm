-*- Default-character-style: (:FIX :ROMAN :VERY-LARGE) -*-
There are a total of 137 steps in the following theorems.  The first
theorem particular to the match effort (that is, not generally to do
with substitution) is sub_lookup.



Term_ind (8):

>> P:Term->U1. (x:Var. P(x))
                => (l:Term list. f:Fun. (t:l. P(t)) => P(f(l)))
                => t:Term. P(t)
|  BY (OnVar `t` E ...)
|  1. P:Term->U1
|  2. (x:Var. P(x))
|  3. (l:Term list. f:Fun. (t:l. P(t)) => P(f(l)))
|  4. t:Term
|  5. P5:Term->U1
|  6. h7:t:({x6:Term|P5(x6)})->P(t)
|  7. z8:Var|(Fun#({x6:Term|P5(x6)}) list)
|- >> P(z8)
|  |  BY (CaseHyp 7 ...)
|  |  7. a9:Var
|  |- >> P(inl(a9))
|  |  |  BY (NormalizeHyp 2 THEN BackThruHyp 2 ...)
|  |  7. b10:Fun#({x6:Term|P5(x6)}) list
|  |- >> P(inr(b10))
|  |  |  BY (E 7 THEN FoldInConcl ``iap`` THEN BackThruHyp 3 ...)
|  |  |  8. a11:Fun
|  |  |  9. a12:({x6:Term|P5(x6)}) list
|  |  |  10. b10=<a11,a12> in Fun#({x6:Term|P5(x6)}) list
|  |  |- >> a12 in Term list
|  |  |  |  BY (E 9 ...)
|  |  |  8. a11:Fun
|  |  |  9. a12:({x6:Term|P5(x6)}) list
|  |  |  10. b10=<a11,a12> in Fun#({x6:Term|P5(x6)}) list
|  |  |- >> ta12. P(t)
|  |  |  |  BY Thin 10 THEN E 9
|  |  |  |- >> tnil. P(t)
|  |  |  |  |  BY (EvalConcl ...)
|  |  |  |  10. h14:{x6:Term|P5(x6)}
|  |  |  |  11. ta12. P(t)
|  |  |  |- >> t(h14.a12). P(t)
|  |  |  |  |  BY (Simp1 0 ...) THEN (Backchain ...)




Term_unroll (2):

>> P:Term->U1. x:Var. P(x)
                => l:Term list. f:Fun. P(f(l))
                => t:Term. P(t)
|  BY (Id ...)
|  1. P:Term->U1
|  2. x:Var. P(x)
|  3. l:Term list. f:Fun. P(f(l))
|                
|  4. t:Term
|- >> P(t)
|  |  BY (Lemma `Term_ind` ...) THEN (Backchain ...)




vap_sub_eq (2):

>> x,y:Var. s:Sub. t:Term. x=y => (<x,t>.s)(y) = t
|  BY (Id ...) 
|  1. x:Var
|  2. y:Var
|  3. s:Sub
|  4. t:Term
|  5. x=y
|- >> <x,t>.s(y)=t
|  |  BY Expand ``vap_sub`` THEN 
|  |     (ReduceDecisionTerm 1 true ...)




vap_sub_neq (3):

>> x,y:Var. s:Sub. t:Term. (x=y) => (<x,t>.s)(y) = s(y)
|  BY (Id ...)
|  1. x:Var
|  2. y:Var
|  3. s:Sub
|  4. t:Term
|  5. (x=y)
|- >> <x,t>.s(y)=s(y)
|  |  BY Expand ``vap_sub`` THEN 
|  |     (ReduceDecisionTerm 1 false ...)
|  |- >> list_ind(s;y;h,ll,v.atom_eq(h.1;y;h.2;v))
|  |  |  =list_ind(s;y;h,ll,v.atom_eq(h.1;y;h.2;v))
|  |  |  BY (Assert 's(y) in Term' ...)
|  |  |     THEN (Expand ``vap_sub`` ...)




in_dom_eq (2):

>> x,y:Var. s:Sub. t:Term. x=y => xdom((<y,t>).s) <=> True
|  BY (Id ...)
|  1. x:Var
|  2. y:Var
|  3. s:Sub
|  4. t:Term
|  5. x=y
|- >> xdom(<y,t>.s)
|  |  BY Expand ``vap_sub`` THEN (ILeft ...!)




in_dom_neq (3):

>> x,y:Var. s:Sub. t:Term. (x=y) => xdom((<y,t>).s) <=> xdom(s)
|  BY (Id ...)
|  1. x:Var
|  2. y:Var
|  3. s:Sub
|  4. t:Term
|  5. (x=y)
|  6. xdom(<y,t>.s)
|- >> xdom(s)
|  |  BY (E 6 THEN Expand ``in_dom lsome``...)
|  |     THEN (E 5 ...)
|  1. x:Var
|  2. y:Var
|  3. s:Sub
|  4. t:Term
|  5. (x=y)
|  6. xdom(s)
|- >> xdom(<y,t>.s)
|  |  BY (IRight THEN SNorm ``in_dom lsome`` ...)




destruct_var_eq (6):

>> x,y:Var. x=y <=> x=y
|  BY (Expand ``ivar`` ...)
|  1. x:Var
|  2. y:Var
|  3. inl(x)=inl(y)
|- >> x=y
|  |  BY Assert 'd(inl(x);u.u;u."foo") = y in Var'
|  |- >> d(inl(x);u.u;u."foo") = y in Var
|  |  |  BY (SubstFor (h 3 p) ...)
|  |  |  4. z1:Term
|  |  |- >> decide(z1;u.u;u."foo") in Var
|  |  |  |  BY (E 4 ...)
|  |  4. d(inl(x);u.u;u."foo") = y in Var
|  |- >> x=y
|  |  |  BY (Reduce ...)
|  1. x:Var
|  2. y:Var
|  3. x=y
|- >> inl(x)=inl(y)
|  |  BY (SubstFor (h 3 p) ...)




destruct_ap_eq (4):

>> f1,f2:Fun. l1,l2:Term list. f1(l1)=f2(l2) <=> f1=f2 & l1=l2
|  BY (Id ...)
|  1. f1:Fun
|  2. f2:Fun
|  3. l1:Term list
|  4. l2:Term list
|  5. f1(l1)=f2(l2)
|- >> f1=f2
|  |  BY (DestructEqUsing 'ˆz. case z: zz; f,lf' 'Fun' 5 ...)
|  |     THEN (Expand ``Term_case`` ...)
|  1. f1:Fun
|  2. f2:Fun
|  3. l1:Term list
|  4. l2:Term list
|  5. f1(l1)=f2(l2)
|  6. f1=f2
|- >> l1=l2
|  |  BY (DestructEqUsing 
|  |         'ˆz. case z: znil; f,ll' 'Term list' 5 ...)
|  |     THEN (Expand ``Term_case`` ...)
|  1. f1:Fun
|  2. f2:Fun
|  3. l1:Term list
|  4. l2:Term list
|  5. f1=f2
|  6. l1=l2
|- >> f1(l1)=f2(l2)
|  |  BY (SubstFor (h 6 p) ...) THEN
|  |     (SubstFor (h 5 p) ...)




var_neq_ap (5):

>> x:Var. f:Fun. l:Term list. x=f(l) <=> False
|  BY (Id ...)
|  1. x:Var
|  2. f:Fun
|  3. l:Term list
|  4. x=f(l)
|- >> False
|  |  BY Assert 'case x: xFalse; f,lTrue' 
|  |- >> case x: xFalse; f,lTrue
|  |  |  BY (SubstFor (h 4 p) ...*)
|  |  |  5. z1:Term
|  |  |- >> Term_case(z1)(ˆx. False)(ˆf. ˆl. True) in U17
|  |  |  |  BY (Cumulativity 'U1' ...)
|  |  5. case x: xFalse; f,lTrue
|  |- >> False
|  |  |  BY (Eval ...)




Term_eq_dec (14):

>> t1,t2:Term. t1=t2  (t1=t2)
|  BY (On `t1` Induction ...)
|  1. x:Var
|  2. t2:Term
|- >> x=t2  (x=t2)
|  |  BY (On `t2` Unroll ...)
|  |  2. x@0:Var
|  |- >> x=x@0  (x=x@0)
|  |  |  BY (Decide 'x=x@0 in Var' ...)
|  |  |  3. x=x@0
|  |  |- >> x=x@0  (x=x@0)
|  |  |  |  BY (SubstFor (h 3 p) ...+s)
|  |  |  3. (x=x@0)
|  |  |- >> x=x@0  (x=x@0)
|  |  |  |  BY (Id ...sc)
|  |  2. l:Term list
|  |  3. f:Fun
|  |- >> x=f(l)  (x=f(l))
|  |  |  BY (Id ...+s)
|  1. l:Term list
|  2. f:Fun
|  3. t:l. t2:Term. t=t2  (t=t2)
|  4. t2:Term
|- >> f(l)=t2  (f(l)=t2)
|  |  BY (On `t2` Unroll ...)
|  |  4. x:Var
|  |- >> f(l)=x  (f(l)=x) 
|  |  |  BY (Id ...sc)
|  |  4. l@0:Term list
|  |  5. f@0:Fun
|  |- >> f(l)=f@0(l@0)  (f(l)=f@0(l@0))
|  |  |  BY (Decide 'f=f@0' ...sc)
|  |  |  6. f=f@0
|  |  |- >> l=l@0  (l=l@0)
|  |  |  |  BY (BringVar `l@0` THEN On `l` Induction ...sc)
|  |  |  |  1. f:Fun
|  |  |  |  2. f@0:Fun
|  |  |  |  3. f=f@0
|  |  |  |- >> nil=l@0  (nil=l@0)
|  |  |  |  |  BY (On `l@0` Unroll ...+s)
|  |  |  |  3. f@0:Fun
|  |  |  |  4. f=f@0
|  |  |  |  5. h2:Term
|  |  |  |  6. t:l. t2:Term. t=t2  (t=t2) => 
|  |  |  |                       l@0:Term list. l=l@0  (l=l@0)
|  |  |  |  7. t2:Term. h2=t2  (h2=t2)
|  |  |  |  8. t:l. t2:Term. t=t2  (t=t2)
|  |  |  |  9. l@0:Term list
|  |  |  |- >> h2.l=l@0  (h2.l=l@0)
|  |  |  |  |  BY (E 6 ...) THEN Thinning [6;8] 
|  |  |  |  |  6. t2:Term. h2=t2  (h2=t2)
|  |  |  |  |  7. l@0:Term list
|  |  |  |  |  8. l@0:Term list. l=l@0  (l=l@0)
|  |  |  |  |- >> h2.l=l@0  (h2.l=l@0)
|  |  |  |  |  |  BY (ThinVars ``f f@0`` THEN On `l@0` Unroll ...sc)
|  |  |  |  |  |  2. h2:Term
|  |  |  |  |  |  3. t2:Term. h2=t2  (h2=t2)
|  |  |  |  |  |  4. l@0:Term list
|  |  |  |  |  |  5. l@0:Term list. l=l@0  (l=l@0)
|  |  |  |  |  |  6. h4:Term
|  |  |  |  |  |- >> (h2=h4 & l=l@0)  (h2=h4 & l=l@0)
|  |  |  |  |  |  |  BY (HypCases ['l@0'] 5 THEN HypCases ['h4'] 3 ...sc)




eq_sub_aps (8):

>> s1,s2:Sub. t:Term. 
       s1(t)=s2(t)  <=>  x:Var. xt => s1(x)=s2(x)
|  BY (Id ...) THEN (On `t` Induction ...+s)
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. x@0:Var
|  5. x@0=x
|  6. s1(x@0)=s2(x@0)
|- >> s1(x)=s2(x)
|  |  BY (SubstFor 'x=x@0' ...)
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. l:Term list
|  5. f:Fun
|  6. xl
|  7. s1(l)=s2(l)
|  8. t:l. s1(t)=s2(t) => xt => s1(x)=s2(x)
|- >> s1(x)=s2(x)
|  |  BY (On `l` Induction ...sc)
|  |  6. h4:Term
|  |  7. xl => s1(l)=s2(l) => 
|  |       t:l. s1(t)=s2(t) => xt => s1(x)=s2(x) => s1(x)=s2(x)
|  |  8. xh4  xl
|  |  9. s1(h4)=s2(h4)
|  |  10. s1(l)=s2(l)
|  |  11. s1(h4)=s2(h4) => xh4 => s1(x)=s2(x)
|  |  12. t:l. s1(t)=s2(t) => xt => s1(x)=s2(x)
|  |- >> s1(x)=s2(x)
|  |  |  BY HypCases [] 8 THEN Try Backchain
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. x@0:Var. x=x@0 => s1(x@0)=s2(x@0)
|- >> s1(x)=s2(x)
|  |  BY (Backchain ...)
|  1. s1:Sub
|  2. s2:Sub
|  3. l:Term list
|  4. f:Fun
|  5. x:Var. xl => s1(x)=s2(x)
|  6. t:l. x:Var. xt => s1(x)=s2(x) => s1(t)=s2(t)
|- >> s1(l)=s2(l)
|  |  BY (On `l` Induction ...+s)
|  |  5. h4:Term
|  |  6. x:Var. xh4  xl => s1(x)=s2(x)
|  |  7. x:Var. xl => s1(x)=s2(x) => 
|  |        t:l. x:atom. xt => s1(x)=s2(x) => s1(t)=s2(t) => s1(l)=s2(l)
|  |  8. x:Var. xh4 => s1(x)=s2(x) => s1(h4)=s2(h4)
|  |  9. t:l. x:Var => s1(x)=s2(x) => s1(t)=s2(t)
|  |- >> s1(h4)=s2(h4)
|  |  |  BY (BackchainWith Id ...) THEN (OrByHyp ...)
|  |  5. h4:Term
|  |  6. x:Var. xh4  xl => s1(x)=s2(x)
|  |  7. x:Var. xl => s1(x)=s2(x) => 
|  |        t:l. x:Var. xt => s1(x)=s2(x) => s1(t)=s2(t) => s1(l)=s2(l)
|  |  8. x:Var. xh4 => s1(x)=s2(x) => s1(h4)=s2(h4)
|  |  9. t:l. x:Var. xt => s1(x)=s2(x) => s1(t)=s2(t)
|  |  10. s1(h4)=s2(h4)
|  |- >> s1(l)=s2(l)
|  |  |  BY (BackchainWith Id ...) THEN (OrByHyp ...)




eq_sub_laps (1):

>> l:Term list. s1,s2:Sub. s1(l)=s2(l) <=> (x:Var. xl => s1(x)=s2(x))
|  BY (Id ...) THEN
|     (InstLemma `eq_sub_aps` ['s1';'s2';'"f"(l)'] ...+s) THEN
|     (Try Backchain ...)



                     Beginning of "match" section.
                     -----------------------------


sub_lookup (6):

>> x:Var. s:Sub. (xdom(s))  t:Term. xdom(s) & s(x)=t
|  BY (On `s` Induction ...+s)
|  1. x:Var
|  2. s:Sub
|  3. h4:Var#Term
|  4. (xdom(s))  t:Term. xdom(s) & s(x)=t
|- >> (h4.1=x  xdom(s))  t:Term. h4.1=x  xdom(s) & (h4.s)(x)=t
|  |  BY (HypCases [] 4 THEN AndThin E 3 THEN Reduce ...)
|  |  3. (xdom(s))
|  |  4. a5:Var
|  |  5. a6:Term
|  |- >> (a5=x  xdom(s))  t:Term. (a5=x  xdom(s)) & (<a5,a6>.s)(x)=t 
|  |  |  BY (Decide 'a5=x' ...+s)
|  |  |  3. a5:Var
|  |  |  4. a6:Term
|  |  |  5. a5=x
|  |  |  6. (xdom(s))
|  |  |- >> t:Term. a6=t
|  |  |  |  BY (ITerm 'a6' ...)
|  |  3. t:Term. xdom(s) & s(x)=t
|  |  4. a7:Var
|  |  5. a8:Term
|  |- >> (a7=x  xdom(s))  t:Term. (a7=x  xdom(s)) & (<a7,a8>.s)(x)=t
|  |  |  BY (Decide 'a7=x' ...+s)
|  |  |  3. a7:Var
|  |  |  4. a8:Term
|  |  |  5. a7=x
|  |  |  6. t:Term. xdom(s) & s(x)=t
|  |  |- >> t:Term. a8=t
|  |  |  |  BY (ITerm 'a8' ...)




sub_extension_1 (3):

>> s1,s2:Sub. x:Var. t:Term. s1s2 => ( <x,t>.s1  <x,t>.s2 <=> True )
|  BY (Id ...) THEN (Expand ``sub_sub`` ...+s)
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. t:Term
|  5. x@0:Var
|  6. x=x@0  x@0dom(s1)
|  7. x1:Var. x1dom(s1) => x1dom(s2) & s1(x1)=s2(x1)
|- >> x=x@0  x@0dom(s2)
|  |  BY (E 6 THEN (OrByHyp ORELSE (IRight THENW Backchain)) ...)
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. t:Term
|  5. x@0:Var
|  6. x=x@0  x@0dom(s2)
|  7. x=x@0  x@0dom(s1)
|  8. x1:Var. x1dom(s1) => x1dom(s2) & s1(x1)=s2(x1)
|- >> (<x,t>.s1))(x@0) = (<x,t>.s2)(x@0)
|  |  BY (Decide 'x=x@0' ...+s) THEN (Backchain ...)




sub_extension_2 (5):

>> s1,s2:Sub. x:Var. t:Term. 
        s1s2 => (xdom(s1)) => (s1  <x,t>.s2 <=> True)
|  BY (Id ...) THEN (Expand ``sub_sub`` ...+s)
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. t:Term
|  5. x@0:Var
|  6. x@0dom(s1)
|  7. (xdom(s1))
|  8. x1:Var. x1dom(s1) => x1dom(s2) & s1(x1)=s2(x1)
|- >> x=x@0  x@0dom(s2)
|  |  BY (Decide 'x=x@0' 
|  |      THEN (OrByHyp ORELSE (IRight THENW Backchain)) ...)
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. t:Term
|  5. x@0:Var
|  6. x=x@0  x@0dom(s2)
|  7. x@0dom(s1)
|  8. (xdom(s1))
|  9. x1:Var. x1dom(s1) => x1dom(s2) & s1(x1)=s2(x1)
|- >> s1(x@0)=(<x,t>.s2)(x@0)
|  |  BY Decide 'x=x@0' 
|  |  10. x=x@0
|  |- >> s1(x@0)=(<x,t>.s2)(x@0)
|  |  |  BY (SubstForInHyp 'x=x@0' 8 ...) THEN (Contradiction ...)
|  |  10. (x=x@0)
|  |- >> s1(x@0)=(<x,t>.s2)(x@0) in Term
|  |  |  BY (Id ...sc) THEN (Backchain ...)




sub_extension_3 (4):

>> s1,s2:Sub. x:Var. t:Term. 
      s1s2 => xdom(s2) => s2(x)=t => (<x,t>.s1  s2 <=> True)
|  BY (Id ...) THEN (Expand ``sub_sub`` ...+s)
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. t:Term
|  5. x@0:Var
|  6. x=x@0  x@0dom(s1)
|  7. s2(x)=t
|  8. xdom(s2)
|  9. x1:Var. x1dom(s1) => x1dom(s2) & s1(x1)=s2(x1)
|- >> x@0dom(s2)
|  |  BY (E 6 THEN (Backchain ORELSE SubstFor 'x@0=x') ...)
|  1. s1:Sub
|  2. s2:Sub
|  3. x:Var
|  4. t:Term
|  5. x@0:Var
|  6. x@0dom(s2)
|  7. x=x@0  x@0dom(s1)
|  8. s2(x)=t
|  9. xdom(s2)
|  10. x1:Var. x1dom(s1) => x1dom(s2) & s1(x1)=s2(x1)
|- >> (<x,t>.s1)(x@0)=(s2)(x@0)
|  |  BY (Decide 'x=x@0' ...+s) THEN Try (Backchain ...)
|  |  6. x=x@0
|  |  7. x1:Var. x1dom(s1) => x1dom(s2) & s1(x1)=s2(x1)
|  |  8. xdom(s2)
|  |  9. s2(x)=t
|  |  10. x@0dom(s2)
|  |- >> t=s2(x@0)
|  |  |  BY (SubstFor 'x@0=x' ...)




sub_union (23):

>> s1,s2:Sub. min(s1) & min(s2) => 
     ncst(s1,s2)  
      s:Sub. min(s) & s1s & s2s & (x:Var. xdom(s) => xdom(s1)  xdom(s2))
|  BY (Id ...) THEN (On `s1` Induction ...)
|  1. s2:Sub
|  2. min(s2)
|  3. min(nil)
|- >> ncst(nil,s2)  
|  |  s:Sub. min(s) & nils & s2s & (x:Var. xdom(s) => xdom(nil)  xdom(s2))
|  |  BY (IRight ...)
|  |- >> s:Sub. min(s) & nils & s2s 
|  |  |          & x:Var. xdom(s) => xdom(nil)  xdom(s2)
|  |  |  BY (ITerm 's2' ...) THEN (Expand ``sub_sub`` ...sc)
|  1. s1:Sub
|  2. s2:Sub
|  3. min(s2)
|  4. h9:Var#Term
|  5. min(s1) => ncst(s1,s2)  s:Sub. min(s) & s1s & s2s 
|                                      & x:Var. xdom(s) => xdom(s1)  xdom(s2)
|  6. min(h9.s1)
|- >> ncst(h9.s1,s2)  s:Sub. min(s) & h9.s1s & s2s 
|  |                           & x:Var. xdom(s) => xdom(h9.s1)  xdom(s2)
|  |  BY HypCases [] 5
|  |  5. min(h9.s1)
|  |- >> min(s1)
|  |  |  BY (Expand ``min_sub`` ...)
|  |  5. min(h9.s1)
|  |  6. ncst(s1,s2)
|  |- >> ncst(h9.s1,s2)  s:Sub. min(s) & h9.s1s & s2s
|  |  |                           & x:Var. xdom(s) => xdom(h9.s1)  xdom(s2)
|  |  |  BY (ILeft THENW Expand ``ncst`` ...) THEN (OnLast (AndThin E) ...)
|  |  |  6. a17:Var
|  |  |  7. a17dom(s1)
|  |  |  8. a17dom(s2)
|  |  |  9. (s1(a17)=s2(a17))
|  |  |- >> x:Var. xdom(h9.s1) & xdom(s2) & (h9.s1(x)=s2(x))
|  |  |  |  BY (On `h9` (AndThin E) ...) THEN (ITerm 'a17' ...+s)
|  |  |  |  3. a17:Var
|  |  |  |  4. a18:Var
|  |  |  |  5. a19:Term
|  |  |  |  6. (<a18,a19>.s1)(a17)=(s2)(a17)
|  |  |  |  7. (s1(a17)=s2(a17))
|  |  |  |  9. a17dom(s1)
|  |  |  |  10. min(s2)
|  |  |  |  11. (a18dom(s1))
|  |  |  |  12. min(s1)
|  |  |  |- >> False
|  |  |  |  |  BY (Decide 'a18=a17' ...+s)
|  |  |  |  |  6. a18=a17
|  |  |  |  |  7. min(s1)
|  |  |  |  |  8. (a18dom(s1))
|  |  |  |  |  9. min(s2)
|  |  |  |  |  10. a17dom(s1)
|  |  |  |  |  11. a17dom(s2)
|  |  |  |  |  12. (s1(a17)=s2(a17))
|  |  |  |  |  13. a19=s2(a17)
|  |  |  |  |- >> False
|  |  |  |  |  |  BY (SubstForInHyp 'a17=a18' 10 ...) THEN (Contradiction ...)
|  |  5. min(h9.s1)
|  |  6. s:Sub. min(s) & s1s & s2s 
|  |             & x:Var. xdom(s) => xdom(s1)  xdom(s2)
|  |- >> ncst(h9.s1,s2)  s:Sub. min(s) & h9.s1s & s2s
|  |  |                           & x:Var. xdom(s) => xdom(h9.s1)  xdom(s2)
|  |  |  BY (AndThin E 6 THEN On `h9` (AndThin E) ...)
|  |  |  4. a10:Sub
|  |  |  5. a11:Var
|  |  |  6. a12:Term
|  |  |  7. min(a10)
|  |  |  8. s1a10
|  |  |  9. s2a10
|  |  |  10. x:Var. xdom(a10) => xdom(s1)  xdom(s2)
|  |  |  11. min(<a11,a12>.s1)
|  |  |- >> ncst(<a11,a12>.s1,s2) 
|  |  |  |   s:Sub. min(s) & <a11,a12>.s1s & s2s
|  |  |  |            & x:Var. xdom(s) => xdom(<a11,a12>.s1)  xdom(s2)
|  |  |  |  BY (CaseLemma `sub_lookup` ['a11';'s2'] ...) 
|  |  |  |     THENL [(IRight ...); (OnLast (AndThin E) ...)]
|  |  |  |  12. (a11dom(s2))
|  |  |  |- >> s:Sub. min(s) & <a11,a12>.s1s & s2s & 
|  |  |  |  |          x:Var. xdom(s) => xdom(<a11,a12>.s1)  xdom(s2)
|  |  |  |  |  BY (ITerm '<a11,a12>.a10' ...+s)
|  |  |  |  |  3. a10:Sub
|  |  |  |  |  4. a11:Var
|  |  |  |  |  5. a12:Term
|  |  |  |  |  6. (a11dom(s2))
|  |  |  |  |  7. x:Var. xdom(a10) => xdom(s1)  xdom(s2)
|  |  |  |  |  8. s2a10
|  |  |  |  |  9. s1a10
|  |  |  |  |  10. min(a10)
|  |  |  |  |  11. min(s2)
|  |  |  |  |  12. (a11dom(s1))
|  |  |  |  |  13. min(s1)
|  |  |  |  |  14. a11dom(a10)
|  |  |  |  |- >> False
|  |  |  |  |  |  BY (HypCases ['a11'] 7 ...) THEN
|  |  |  |  |  |     (Expand ``sub_sub`` THEN Backchain ...)
|  |  |  |  |  3. a10:Sub
|  |  |  |  |  4. a11:Var
|  |  |  |  |  5. a12:Term
|  |  |  |  |  6. x:Var
|  |  |  |  |  7. a11=x  xdom(a10)
|  |  |  |  |  8. (a11dom(a10))
|  |  |  |  |  9. (a11dom(s2))
|  |  |  |  |  11. s2a10
|  |  |  |  |  12. s1a10
|  |  |  |  |  13. min(a10)
|  |  |  |  |  14. min(s2)
|  |  |  |  |  15. (a11dom(s1))
|  |  |  |  |  16. min(s1)
|  |  |  |  |- >> a11=x  xdom(s1)  xdom(s2)
|  |  |  |  |  |  BY (HypCases [] 7 THEN Try OrByHyp ...)
|  |  |  |  |  |  7. (a11dom(a10))
|  |  |  |  |  |  8. (a11dom(s2))
|  |  |  |  |  |  9. x1:Var. x1dom(a10) => x1dom(s1)  x1dom(s2)
|  |  |  |  |  |  10. s2a10
|  |  |  |  |  |  11. s1a10
|  |  |  |  |  |  12. min(a10)
|  |  |  |  |  |  13. min(s2)
|  |  |  |  |  |  14. (a11dom(s1))
|  |  |  |  |  |  15. min(s1)
|  |  |  |  |  |  16. xdom(a10)
|  |  |  |  |  |- >> a11=x  xdom(s1)  xdom(s2)
|  |  |  |  |  |  |  BY (HypCases ['x'] 9 ...) THEN (OrByHyp ...)
|  |  |  |  12. a14:Term
|  |  |  |  13. a11dom(s2)
|  |  |  |  14. s2(a11)=a14
|  |  |  |- >> ncst(<a11,a12>.s1,s2) 
|  |  |  |  |   s:Sub. min(s) & <a11,a12>.s1s & s2s 
|  |  |  |  |            & x:Var. xdom(s) => xdom(<a11,a12>.s1)  xdom(s2)
|  |  |  |  |  BY (Decide 'a12=a14' ...)
|  |  |  |  |  15. a12=a14
|  |  |  |  |- >> ncst(<a11,a12>.s1,s2) 
|  |  |  |  |  |   s:Sub. min(s) & <a11,a12>.s1s & s2s
|  |  |  |  |  |            & x:Var. xdom(s) => xdom(<a11,a12>.s1)  xdom(s2)
|  |  |  |  |  |  BY (IRight THENM ITerm 'a10' ...s)
|  |  |  |  |  |  3. a10:Sub
|  |  |  |  |  |  4. a11:Var
|  |  |  |  |  |  5. a12:Term
|  |  |  |  |  |  6. a14:Term
|  |  |  |  |  |  7. a12=a14
|  |  |  |  |  |  8. s2(a11)=a14
|  |  |  |  |  |  9. a11dom(s2)
|  |  |  |  |  |  11. s2a10
|  |  |  |  |  |  12. s1a10
|  |  |  |  |  |  13. min(a10)
|  |  |  |  |  |  14. min(s2)
|  |  |  |  |  |  15. (a11dom(s1))
|  |  |  |  |  |  16. min(s1)
|  |  |  |  |  |- >> <a11,a12>.s1a10
|  |  |  |  |  |  |  BY (Lemma `sub_extension_3` ...)
|  |  |  |  |  |  |- >> a11dom(a10)
|  |  |  |  |  |  |  |  BY (Expand ``sub_sub`` THEN Try Backchain ...)
|  |  |  |  |  |  |- >> a10(a11)=a12
|  |  |  |  |  |  |  |  BY (SplitEq 's2(a11)' ...)
|  |  |  |  |  |  |  |- >> a10(a11)=s2(a11)
|  |  |  |  |  |  |  |  |  BY (Expand ``sub_sub`` THEN Backchain ...)
|  |  |  |  |  |  3. a10:Sub
|  |  |  |  |  |  4. a11:Var
|  |  |  |  |  |  5. a12:Term
|  |  |  |  |  |  6. a14:Term
|  |  |  |  |  |  7. a12=a14
|  |  |  |  |  |  8. s2(a11)=a14
|  |  |  |  |  |  9. a11dom(s2)
|  |  |  |  |  |  11. s2a10
|  |  |  |  |  |  12. s1a10
|  |  |  |  |  |  13. min(a10)
|  |  |  |  |  |  14. min(s2)
|  |  |  |  |  |  15. (a11dom(s1))
|  |  |  |  |  |  16. min(s1)
|  |  |  |  |  |  17. <a11,a12>.s1a10
|  |  |  |  |  |  18. x:Var
|  |  |  |  |  |  19. xdom(a10)
|  |  |  |  |  |- >> a11=x  xdom(s1)  xdom(s2)
|  |  |  |  |  |  |  BY (HypCases ['x'] 10 THEN Try OrByHyp ...)
|  |  |  |  |  15. (a12=a14)
|  |  |  |  |- >> ncst(<a11,a12>.s1,s2) 
|  |  |  |  |  |   s:Sub. min(s) & <a11,a12>.s1s & s2s
|  |  |  |  |  |            & x:Var. xdom(s) => xdom(<a11,a12>.s1)  xdom(s2)
|  |  |  |  |  |  BY (ILeft THENM ITerm 'a11' ...sc) THEN 
|  |  |  |  |  |     (BackchainWith Trivial ...)




lmatch_thm (25):

>> l:Term list. (t:l. match?(t)) => match?(l)
|  BY (On `l` Induction ...+s)
|- >> match?(nil)
|  |  BY (Expand ``lmatchp`` ...+s)
|  |  1. l2:Term list
|  |- >> s:Sub. nil=l2 & min(s)
|  |  |       & x:Var. (xdom(s))  s:Sub. (nil=l2)
|  |  |  BY (On `l2` Unroll ...+s)
|  |  |- >> s:Sub. min(s) 
|  |  |  |      & x:Var. (xdom(s))  s:Sub. False
|  |  |  |  BY (ILeft THENM ITerm 'nil' ...+s)
|  1. l:Term list
|  2. h3:Term
|  3. t:l. match?(t) => match?(l)
|  4. match?(h3)
|  5. t:l. match?(t)
|- >> match?(h3.l)
|  |  BY (AndThin E 3 ...)
|  |  3. match?(h3)
|  |  4. t:l. match?(t)
|  |  5. match?(l)
|  |- >> match?(h3.l)
|  |  |  BY (Thin 4 THEN Expand1 ``lmatchp`` 0 ...sc)
|  |  |  4. match?(l)
|  |  |  5. l2:Term list
|  |  |- >> s:Sub. s(h3).s(l)=l2 & min(s) & (x:Var. xdom(s) <=> xh3  xl)
|  |  |  |   s:Sub. (s(h3).s(l)=l2)
|  |  |  |  BY (On `l2` Unroll ...sc)
|  |  |  |  6. h5:Term
|  |  |  |- >> s:Sub. s(h3)=h5 & s(l)=l2 & min(s) 
|  |  |  |  |          & x:Var. xdom(s) <=> xh3  xl 
|  |  |  |  |   s:Sub. (s(h3)=h5 & s(l)=l2)
|  |  |  |  |  BY (Expand ``matchp lmatchp`` THEN HypCases ['h5'] 3 ...)
|  |  |  |  |  3. l2:Term list. s:Sub. s(l)=l2 & min(s) 
|  |  |  |  |                            & x:Var. xdom(s) <=> xl 
|  |  |  |  |      s:Sub. (s(l)=l2)
|  |  |  |  |  4. l2:Term list
|  |  |  |  |  5. h5:Term
|  |  |  |  |  6. s:Sub. s(h3)=h5 & min(s) & (x:Var. xdom(s) <=> xh3)
|  |  |  |  |- >> s:Sub. s(h3)=h5 & s(l)=l2 & min(s) 
|  |  |  |  |  |          & x:Var. xdom(s) <=> xh3  xl 
|  |  |  |  |  |   s:Sub. (s(h3)=h5 & s(l)=l2)
|  |  |  |  |  |  BY (HypCases ['l2'] 3 ...)
|  |  |  |  |  |  3. l2:Term list
|  |  |  |  |  |  4. h5:Term
|  |  |  |  |  |  5. s:Sub. s(h3)=h5 & min(s) & (x:Var. xdom(s) <=> xh3)
|  |  |  |  |  |  6. s:Sub. s(l)=l2 & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |  |- >> s:Sub. s(h3)=h5 & s(l)=l2 & min(s) 
|  |  |  |  |  |  |          & x:Var. xdom(s) <=> xh3  xl 
|  |  |  |  |  |  |   s:Sub. (s(h3)=h5 & s(l)=l2)
|  |  |  |  |  |  |  BY (SomeE ``s2`` 6 THEN SomeE ``s1`` 5 THEN
|  |  |  |  |  |  |      CaseLemma `sub_union` ['s1';'s2']...)
|  |  |  |  |  |  |  5. s2:Sub
|  |  |  |  |  |  |  6. s2(l)=l2
|  |  |  |  |  |  |  7. min(s2)
|  |  |  |  |  |  |  8. x:Var. xdom(s2) <=> xl
|  |  |  |  |  |  |  9. s1:Sub
|  |  |  |  |  |  |  10. s1(h3)=h5
|  |  |  |  |  |  |  11. min(s1)
|  |  |  |  |  |  |  12. x:Var. xdom(s1) <=> xh3
|  |  |  |  |  |  |  13. ncst(s1,s2)
|  |  |  |  |  |  |- >> s:Sub. s(h3)=h5 & s(l)=l2 & min(s) 
|  |  |  |  |  |  |  |          & x:Var. xdom(s) <=> xh3  xl 
|  |  |  |  |  |  |  |   s:Sub. (s(h3)=h5 & s(l)=l2)
|  |  |  |  |  |  |  |  BY (Expand ``ncst`` THEN OnLast (SomeE ``x``) 
|  |  |  |  |  |  |  |      THEN IRight ...)
|  |  |  |  |  |  |  |  13. x:Var
|  |  |  |  |  |  |  |  14. xdom(s1)
|  |  |  |  |  |  |  |  15. xdom(s2)
|  |  |  |  |  |  |  |  16. (s1(x)=s2(x))
|  |  |  |  |  |  |  |  17. s:Sub
|  |  |  |  |  |  |  |  18. s(h3)=h5
|  |  |  |  |  |  |  |  19. s(l)=l2
|  |  |  |  |  |  |  |- >> False
|  |  |  |  |  |  |  |  |  BY (AndThin E 16 ...) THEN SplitEq 's(x)'
|  |  |  |  |  |  |  |  |  16. s:Sub
|  |  |  |  |  |  |  |  |  17. s(h3)=h5
|  |  |  |  |  |  |  |  |  18. s(l)=l2
|  |  |  |  |  |  |  |  |- >> s1(x)=s(x) in Term
|  |  |  |  |  |  |  |  |  |  BY (LemmaUsing `eq_sub_aps` ['h3'] ...) THEN 
|  |  |  |  |  |  |  |  |  |     (Backchain ...)
|  |  |  |  |  |  |  |  |  16. s:Sub
|  |  |  |  |  |  |  |  |  17. s(h3)=h5
|  |  |  |  |  |  |  |  |  18. s(l)=l2
|  |  |  |  |  |  |  |  |- >> s(x)=s2(x) in Term
|  |  |  |  |  |  |  |  |  |  BY (LemmaUsing `eq_sub_laps` ['l'] ...) THEN 
|  |  |  |  |  |  |  |  |  |     (Backchain ...)
|  |  |  |  |  |  |  5. s2:Sub
|  |  |  |  |  |  |  6. s2(l)=l2
|  |  |  |  |  |  |  7. min(s2)
|  |  |  |  |  |  |  8. x:Var. xdom(s2) <=> xl
|  |  |  |  |  |  |  9. s1:Sub
|  |  |  |  |  |  |  10. s1(h3)=h5
|  |  |  |  |  |  |  11. min(s1)
|  |  |  |  |  |  |  12. x:Var. xdom(s1) <=> xh3
|  |  |  |  |  |  |  13. s:Sub. min(s) & s1s & s2s 
|  |  |  |  |  |  |              & x:Var. xdom(s) => xdom(s1)  xdom(s2)
|  |  |  |  |  |  |- >> s:Sub. s(h3)=h5 & s(l)=l2 & min(s) 
|  |  |  |  |  |  |  |          & x:Var. xdom(s) <=> xh3  xl 
|  |  |  |  |  |  |  |   s:Sub. (s(h3)=h5 & s(l)=l2)
|  |  |  |  |  |  |  |  BY (OnLast (SomeE ``s``) THEN ILeft THENM ITerm 's' ...)
|  |  |  |  |  |  |  |  13. s:Sub
|  |  |  |  |  |  |  |  14. min(s)
|  |  |  |  |  |  |  |  15. s1s
|  |  |  |  |  |  |  |  16. s2s
|  |  |  |  |  |  |  |  17. x:Var. xdom(s) => xdom(s1)  xdom(s2)
|  |  |  |  |  |  |  |- >> s(h3)=h5
|  |  |  |  |  |  |  |  |  BY (SplitEq 's1(h3)' THEN Try (Lemma `eq_sub_aps`) ...)
|  |  |  |  |  |  |  |  |     THEN ThinVars ``l l2 h5 s2``
|  |  |  |  |  |  |  |  |  1. h3:Term
|  |  |  |  |  |  |  |  |  2. s1:Sub
|  |  |  |  |  |  |  |  |  3. min(s1)
|  |  |  |  |  |  |  |  |  4. x:Var. xdom(s1) <=> xh3
|  |  |  |  |  |  |  |  |  5. s:Sub
|  |  |  |  |  |  |  |  |  6. min(s)
|  |  |  |  |  |  |  |  |  7. s1s
|  |  |  |  |  |  |  |  |  8. x:Var
|  |  |  |  |  |  |  |  |  9. xh3
|  |  |  |  |  |  |  |  |- >> s(x)=s1(x)
|  |  |  |  |  |  |  |  |  |  BY (Expand ``sub_sub`` THEN Backchain ...)
|  |  |  |  |  |  |  |  13. s:Sub
|  |  |  |  |  |  |  |  14. min(s)
|  |  |  |  |  |  |  |  15. s1s
|  |  |  |  |  |  |  |  16. s2s
|  |  |  |  |  |  |  |  17. x:Var. xdom(s) => xdom(s1)  xdom(s2)
|  |  |  |  |  |  |  |  18. s(h3)=h5
|  |  |  |  |  |  |  |- >> s(l)=l2
|  |  |  |  |  |  |  |  |  BY (SplitEq 's2(l)' THEN Try (Lemma `eq_sub_laps`) ...)
|  |  |  |  |  |  |  |  |     THEN ThinVars ``l2 h3 h5 s1``
|  |  |  |  |  |  |  |  |  2. s2:Sub
|  |  |  |  |  |  |  |  |  3. min(s2)
|  |  |  |  |  |  |  |  |  4. x:Var. xdom(s2) <=> xl
|  |  |  |  |  |  |  |  |  5. s:Sub
|  |  |  |  |  |  |  |  |  6. min(s)
|  |  |  |  |  |  |  |  |  7. s2s
|  |  |  |  |  |  |  |  |  8. x:Var
|  |  |  |  |  |  |  |  |  9. xl
|  |  |  |  |  |  |  |  |- >> s(x)=s2(x)
|  |  |  |  |  |  |  |  |  |  BY (Expand ``sub_sub`` THEN Backchain ...)
|  |  |  |  |  |  |  |  13. s:Sub
|  |  |  |  |  |  |  |  14. min(s)
|  |  |  |  |  |  |  |  15. s1s
|  |  |  |  |  |  |  |  16. s2s
|  |  |  |  |  |  |  |  17. x:Var. xdom(s) => xdom(s1)  xdom(s2)
|  |  |  |  |  |  |  |  18. s(h3)=h5
|  |  |  |  |  |  |  |  19. s(l)=l2
|  |  |  |  |  |  |  |  20. min(s)
|  |  |  |  |  |  |  |  21. x:Var
|  |  |  |  |  |  |  |  22. xdom(s)
|  |  |  |  |  |  |  |- >> xh3  xl
|  |  |  |  |  |  |  |  |  BY (HypCases ['x'] 17 ...)
|  |  |  |  |  |  |  |  |     THENL [(ILeft ...); (IRight ...)] 
|  |  |  |  |  |  |  |  |     THEN (Expand ``sub_sub`` THEN Backchain ...)
|  |  |  |  |  |  |  |  13. s:Sub
|  |  |  |  |  |  |  |  14. min(s)
|  |  |  |  |  |  |  |  15. s1s
|  |  |  |  |  |  |  |  16. s2s
|  |  |  |  |  |  |  |  17. x:Var. xdom(s) => xdom(s1)  xdom(s2)
|  |  |  |  |  |  |  |  18. s(h3)=h5
|  |  |  |  |  |  |  |  19. s(l)=l2
|  |  |  |  |  |  |  |  20. min(s)
|  |  |  |  |  |  |  |  21. x:Var
|  |  |  |  |  |  |  |  22. xh3  xl
|  |  |  |  |  |  |  |- >> xdom(s)
|  |  |  |  |  |  |  |  |  BY (HypCases [] 22 THEN Expand ``sub_sub`` 
|  |  |  |  |  |  |  |  |      THEN Backchain ...)
|  |  |  |  |  |  3. l2:Term list
|  |  |  |  |  |  4. h5:Term
|  |  |  |  |  |  5. s:Sub. s(h3)=h5 & min(s) 
|  |  |  |  |  |                          & x:Var. xdom(s) <=> xh3
|  |  |  |  |  |  6. s:Sub. (s(l)=l2)
|  |  |  |  |  |- >> s:Sub. s(h3)=h5 & s(l)=l2 & min(s)
|  |  |  |  |  |  |          & x:Var. xdom(s) <=> xh3 
|  |  |  |  |  |  |   xl  s:Sub. (s(h3)=h5 & s(l)=l2)
|  |  |  |  |  |  |  BY (IRight ...)
|  |  |  |  |  |  |  7. s:Sub
|  |  |  |  |  |  |  8. s(h3)=h5
|  |  |  |  |  |  |  9. s(l)=l2
|  |  |  |  |  |  |- >> False
|  |  |  |  |  |  |  |  BY (BackThruHypUsing ['s'] 6 ...)
|  |  |  |  |  3. l2:Term list. s:Sub. s(l)=l2 & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |                     s:Sub. (s(l)=l2)
|  |  |  |  |  4. l2:Term list
|  |  |  |  |  5. h5:Term
|  |  |  |  |  6. s:Sub. (s(h3)=h5)
|  |  |  |  |- >> s:Sub. s(h3)=h5 & s(l)=l2 & min(s)  
|  |  |  |  |  |          & x:Var. xdom(s) <=> xh3  xl 
|  |  |  |  |  |   s:Sub. (s(h3)=h5 & s(l)=l2)
|  |  |  |  |  |  BY (IRight ...)
|  |  |  |  |  |  7. s:Sub
|  |  |  |  |  |  8. s(h3)=h5
|  |  |  |  |  |  9. s(l)=l2
|  |  |  |  |  |- >> False
|  |  |  |  |  |  |  BY (BackThruHypUsing ['s'] 6 ...)




match_thm (13):

>> t:Term. match?(t)
|  BY (On `t` Induction ...)
|  1. x:Var
|- >> match?(x)
|  |  BY (Expand ``matchp`` ...+s)
|  |  2. t2:Term
|  |- >> s:Sub. s(x)=t2 & min(s) & (x@0:Var. x@0dom(s) <=> x=x@0)
|  |  |   s:Sub. (s(x)=t2)
|  |  |  BY (ILeft THENM ITerm '[<x,t2>]' ...+s)
|  1. l:Term list
|  2. f:Fun
|  3. t:l. match?(t)
|- >> match?(f(l))
|  |  BY (FLemma `lmatch_thm` [3] ...) THEN Thin 3 
|  |  3. match?(l)
|  |- >> match?(f(l))
|  |  |  BY (Expand ``matchp`` ...+s)
|  |  |  3. t2:Term
|  |  |  4. match?(l)
|  |  |- >> s:Sub. f(s(l))=t2 & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |   s:Sub. (f(s(l))=t2)
|  |  |  |  BY (On `t2` Unroll ...)
|  |  |  |  3. match?(l)
|  |  |  |  4. x:Var
|  |  |  |- >> s:Sub. f(s(l))=x & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |   s:Sub. (f(s(l))=x)
|  |  |  |  |  BY (IRight ...+s)
|  |  |  |  3. match?(l)
|  |  |  |  4. l@0:Term list
|  |  |  |  5. f@0:Fun
|  |  |  |- >> s:Sub. f(s(l))=f@0(l@0) & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |   s:Sub. (f(s(l))=f@0(l@0))
|  |  |  |  |  BY (Decide 'f=f@0' ...)
|  |  |  |  |  6. f=f@0
|  |  |  |  |- >> s:Sub. f(s(l))=f@0(l@0) & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |  |   s:Sub. (f(s(l))=f@0(l@0))
|  |  |  |  |  |  BY (Expand ``lmatchp`` THEN HypCases ['l@0'] 3 ...)
|  |  |  |  |  |  3. l@0:Term list
|  |  |  |  |  |  4. f@0:Fun
|  |  |  |  |  |  5. f=f@0
|  |  |  |  |  |  6. s:Sub. s(l)=l@0 & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |  |- >> s:Sub. f(s(l))=f@0(l@0) & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |  |  |   s:Sub. (f(s(l))=f@0(l@0))
|  |  |  |  |  |  |  BY ((OnLast (SomeE ``s``) THEN ILeft THENM ITerm 's' ...) ...sc)
|  |  |  |  |  |  3. l@0:Term list
|  |  |  |  |  |  4. f@0:Fun
|  |  |  |  |  |  5. f=f@0
|  |  |  |  |  |  6. s:Sub. (s(l)=l@0)
|  |  |  |  |  |- >> s:Sub. f(s(l))=f@0(l@0) & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |  |  |   s:Sub. (f(s(l))=f@0(l@0))
|  |  |  |  |  |  |  BY (IRight ...+s)
|  |  |  |  |  |  |  5. s:Sub
|  |  |  |  |  |  |  6. s(l)=l@0
|  |  |  |  |  |  |  7. s1:Sub. (s1(l)=l@0)
|  |  |  |  |  |  |  8. f=f@0
|  |  |  |  |  |  |- >> False
|  |  |  |  |  |  |  |  BY (EOn 's' 7 ...) THEN (Contradiction ...)
|  |  |  |  |  6. (f=f@0)
|  |  |  |  |- >> s:Sub. f(s(l))=f@0(l@0) & min(s) & (x:Var. xdom(s) <=> xl)
|  |  |  |  |  |   s:Sub. (f(s(l))=f@0(l@0))
|  |  |  |  |  |  BY (IRight ...+s)
