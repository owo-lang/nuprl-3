%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  logic.ml:     PRL-extensions for logic definitions                                       |
|                                                                                           |
+-------------------------------------------------------------------------------------------%



%  I. Constructors, Destructors & Predicates
   -----------------------------------------
%


%  Ia:   Constructors
   ------------------
%

   let make_and_term p q               =  instantiate_def `and` [p;q];;
   let make_or_term  p q               =  make_union_term p q;;
   let make_imp_term p q               =  instantiate_def `imp` [p;q];;
   let make_equiv_term p q             =  instantiate_def `equiv` [p;q];;
   let make_false_term                 =  instantiate_def `false` [];;
   let make_not_term p                 =  instantiate_def `not` [p];;
   let make_all_term x type term       =  instantiate_def `all` [mvar x;type;term];;
   let make_all2_term x y type term    =  instantiate_def `all2` [mvar x;mvar y;type;term];;
   let make_all3_term x y z type term  =
      instantiate_def `all3` [mvar x;mvar y;mvar z;type;term];;
   let make_some_term x type term      =  instantiate_def `some` [mvar x;type;term];;
   let make_some2_term x y type term   =  instantiate_def `some2` [mvar x;mvar y;type;term];;
   let make_some3_term x y z type term =
      instantiate_def `some3` [mvar x;mvar y;mvar z;type;term];;
   
   let FALSE                           =  make_false_term;;


%  Ib:   Destructors
   ------------------
%

   let destruct_and t         =  snd (destruct_product t);;
   let destruct_or t          =  destruct_union t;;
   let destruct_imp t         =  snd (destruct_function t);;
   let destruct_equiv t       =  destruct_imp (fst (destruct_and t));;
   let destruct_not t         =  fst (destruct_imp t);;
   let destruct_all t         =  destruct_function t ;;
   let destruct_all2 t        =  let x,t,term = destruct_all t in x,(destruct_all term);;
   let destruct_all3 t        =  let x,t,term = destruct_all t in x,(destruct_all2 term);;
   let destruct_some t        =  destruct_product t;;
   let destruct_some2 t       =  let x,t,term = destruct_some t in x,(destruct_some term);;
   let destruct_some3 t       =  let x,t,term = destruct_some t in x,(destruct_some2 term);;



%  Ic:   Predicates
   ------------------
%

   let is_and_term t             =  (is_product_term t) & (fst (destruct_product t) = `NIL`);;
   let is_or_term t              =  is_union_term t;;
   let is_imp_term t             =  
      (is_function_term t) & (fst(destruct_function t) =`NIL`);;
   let is_equiv_term t           =  
      (let p,q = destruct_equiv t in t = make_equiv_term p q) ? false;;
   let is_false_term t           =  is_void_term t;;
   let is_not_term t             =  (is_imp_term t) & (snd (destruct_imp t) = FALSE);;
   let is_all_term t             =  
      (is_function_term t) & not (fst (destruct_function t) = `NIL`);;
   let is_all2_term t            =  
      (let x,y,type,T = destruct_all2 t 
       in 
         not (x=`NIL`) & not (y=`NIL`) & (t = make_all2_term x y type T)
      ) ? false
   ;;
   let is_all3_term t            =  
      (let x,y,z,type,T = destruct_all3 t
       in
          not (x=`NIL`) & not (y=`NIL`) & not (z=`NIL`) & (t = make_all3_term x y z type T)
      ) ? false
   ;;
   let is_some_term t            =  
      (is_product_term t) & not (fst (destruct_product t) = `NIL`);;
   let is_some2_term t           =
      (let x,y,type,T = destruct_some2 t
       in 
         not (x=`NIL`) & not (y=`NIL`) & (t = make_some2_term x y type T)
      ) ? false
   ;;
   let is_some3_term t           =
      (let x,y,z,type,T = destruct_some3 t 
       in
          not (x=`NIL`) & not (y=`NIL`) & not (z=`NIL`) & (t = make_some3_term x y z type T)
      ) ? false
   ;;
%  ---------------------------------------------------------------------------------------   %




%  II. Rules
   ---------
%





%  IIa:  Formation   
   ---------------
%

   let and_equality           = refine product_equality_independent;;

   let or_equality            = refine union_equality;;

   let imp_equality           = refine function_equality_independent;;

   let equiv_equality proof   =
      (let A_B.rest,Ui  = destruct_equal (conclusion proof)
       in
         let A,B = destruct_equiv A_B
         in
            Seq   [ make_equal_term Ui [A] ; make_equal_term Ui [B] ]
            THENL [ IDTAC; IDTAC; and_equality THEN imp_equality THEN Equal]
      ) proof
   ;;

   let false_equality         = refine void_equality;;

   let not_equality           = imp_equality THENL [IDTAC; false_equality];;


   let all_equality proof     = 
      (let id = fst (destruct_all (hd (fst (destruct_equal (conclusion proof)))))
       in
          refine (function_equality (new id proof))
      ) proof
   ;;

   letrec repeat_all_equality_for n =
      if n = 1 
         then all_equality
         else all_equality THENL [IDTAC; repeat_all_equality_for (n-1)]
   ;;

   letrec repeat_all_equality proof =
      (all_equality THENL [IDTAC; TRY repeat_all_equality] ) proof;;


   let some_equality proof    = 
      (let id = fst(destruct_some (hd (fst (destruct_equal (conclusion proof)))))
       in
          refine (product_equality (new id proof))
      ) proof
   ;;

   letrec repeat_some_equality_for n   =
      if n = 1 
         then some_equality
         else some_equality THENL [IDTAC; repeat_some_equality_for (n-1)]
   ;;

   letrec repeat_some_equality proof   = 
      ( some_equality THENL [IDTAC; TRY repeat_some_equality]) proof ;;




%  IIb:  Introduction                        
   ------------------
%

   let and_intro              = refine product_intro;;

   letrec repeat_and_intro proof =
      (if is_and_term (conclusion proof) then and_intro THEN repeat_and_intro else IDTAC
      ) proof
   ;;

   let or_intro_left level    = refine (union_intro_left level);;
   let or_intro_right level   = refine (union_intro_right level);;

   let imp_intro level        = refine (function_intro level `nil`);;

   letrec repeat_imp_intro level proof =
      (if is_imp_term (conclusion proof) 
         then imp_intro level THEN (repeat_imp_intro level) else IDTAC
      ) proof
   ;;


   let equiv_intro level      = and_intro THEN imp_intro level;;

   let false_intro            = COMPLETE Decision;;

   let not_intro              = imp_intro;;


   let all_intro level proof  =
      (let id = fst (destruct_all (conclusion proof))
       in
         refine (function_intro level (new id proof))
      ) proof
   ;;

   letrec repeat_all_intro_for n level proof =
      (if n = 1 
         then all_intro level
         else all_intro level THENL [IDTAC; repeat_all_intro_for (n-1) level]
      ) proof
   ;;

   letrec repeat_all_intro level proof       =
      ( all_intro level THENL [IDTAC; TRY (repeat_all_intro level)]) proof
   ;;


   let some_intro level a proof        =
      (let id = fst (destruct_some (conclusion proof))
       in
         refine (product_intro_dependent a level (new id proof))
      ) proof
   ;;


%  ----- The repeated version turns out to become a lot of computation -----  %

   let repeat_some_intro level alist proof   =
      (let l            = length (hypotheses proof) + 1
       and LIMIT        = length alist
       and some_term    = conclusion proof
       in

       let do_repeated_some_introduction  =
         let prove_some_Ui_for howmany    =
            let inst_ais = cut_from (LIMIT-howmany) alist
            in

            let use_hyp no proof       =
               (let inst_list = 
                  inst_ais @ (cut_first (l+2*LIMIT+1) (map mvar (ids (hypotheses proof))))
                in
                  eliminate_using inst_list no THEN Equal
               ) proof
            in
            
            letrec prove_goal index    =
               if index = LIMIT 
                  then use_hyp (l+LIMIT)  
                  else some_equality THENL [use_hyp (l+index); prove_goal (index+1)]
            in
               prove_goal ((LIMIT - howmany)+1)
         in
   
         letrec intro_using aj_list =
            if null aj_list
               then Thinning (intlist l (2*LIMIT+1) )
               else (let aj.rest = aj_list
                     and howmany = length aj_list
                     in
                              some_intro level aj
                        THENL [Equal; intro_using rest; prove_some_Ui_for howmany]
                    )
         in
            intro_using alist
      in
      
      let sequence_ais                    =
         letrec seq_ais ai_list term   =
            if null ai_list
            then do_repeated_some_introduction
            else (let ai.rest       = ai_list
                  and x,A,rest_term = destruct_some term
                  in
                     Seq   [make_equal_term A [ai]]
                     THENL [ Thinning (intlist l (2*LIMIT - (length rest)))
                           ; seq_ais rest (substitute rest_term [(mvar x),ai])]
                 )
         in
            seq_ais alist some_term
      in

      letrec seq_and_prove_term index        =
         let prove_term no    =
            let using_hyp hyp proof = 
               (let inst_list = cut_first (l+no) (map mvar (ids (hypotheses proof)))
                in
                  eliminate_using inst_list hyp THEN Equal
               ) proof
            in

            letrec prove_using i bound =
               if i = bound 
                  then  Thinning (intlist l bound)
                  else  all_intro level THENL [prove_using (i+1) bound; using_hyp (l+i)]
            in
               prove_using 0 no

         and term no    =
            letrec rebuild_some_into_all t i =
               if i = 0
                  then make_equal_term 
                        (make_universe_term level) 
                        [if no = LIMIT  then t  else fst (snd (destruct_some t))]
                  else (let x,A,B = destruct_some t
                        in
                           make_all_term x A  (rebuild_some_into_all B (i-1))
                       )
            in
               rebuild_some_into_all some_term no
         in

            if index > LIMIT
               then sequence_ais
               else Seq [term index] THENL [prove_term index; seq_and_prove_term (index+1)]
      in

         seq_and_prove_term 0
      ) proof
   ;;




   %  -------------  Now everything together by one rule-name  ----------------  %

   let logic_introduction proof  = IDTAC proof;;
   
   let lintro                    = logic_introduction;;





%  IIc:  Elimination
   -----------------
%

   let and_elim hyp              = RepeatAndElim hyp;;         % Doug's tactic %

   let or_elim hyp               = RepeatOrElim hyp;;

   let imp_elim hyp              = refine (function_elim_independent hyp `nil`);;

   let equiv_elim_left hyp proof =
      (let l = length (hypotheses proof)
       in
          refine (product_elim hyp `nil` `nil`) THEN imp_elim (l+1) THEN Thinning [l+1;l+2]
      ) proof
   ;;

   let equiv_elim_right hyp proof =
      (let l = length (hypotheses proof)
       in
          refine (product_elim hyp `nil` `nil`) THEN imp_elim (l+2) THEN Thinning [l+1;l+2]
      ) proof
   ;;

   let false_elim hyp            = refine (void_elim hyp);;

   let not_elim hyp proof        =
      (let l=length (hypotheses proof) in imp_elim hyp THENL [Thinning [hyp];false_elim (l+1)]
      ) proof
   ;;

   let all_elim_on               = eliminate_using;;


   let some_elim1 hyp proof      =
      (let id = fst (destruct_some (term_of_declaration (select hyp (hypotheses proof))))
       in
          refine (product_elim hyp (new id proof) `nil`) THEN Thinning [hyp]
      ) proof
   ;;

   letrec some_elim hyp proof       =
      (if is_some_term (term_of_declaration (select hyp (hypotheses proof)))
        then some_elim1 hyp THEN some_elim (length (hypotheses proof) +1)
        else IDTAC
      ) proof
   ;;       

   letrec some_elim_for no hyp proof =
      (if no =0
         then IDTAC
         else some_elim1 hyp THEN some_elim_for (no-1) (length (hypotheses proof) +1) 
      ) proof
   ;;

   



%  III. Tactics
   ------------
%
   

   let AllIntro level AUjtac           = all_intro level THENL [IDTAC; AUjtac]   ;;
   let All_intro                       = AllIntro 1;;
   let Allintro                        = All_intro membership;;

   let RepeatAllIntro level AiUjtacs   = REPEATL (AllIntro level) AiUjtacs;;
   let Repeat_all_intro                = RepeatAllIntro 1;;


   let SomeIntro level a atac BUitac   = some_intro level a THENL [atac; IDTAC; BUitac];;
   let Some_intro                      = SomeIntro 1;;

   let RepeatSomeIntro level ailist aitacs AiUjtacs BUjtac  =
      repeat_some_intro level ailist  THENL  AiUjtacs @ [BUjtac] @ aitacs @ [IDTAC];;
   let Repeat_some_intro               = RepeatSomeIntro 1;;


   let ImpIntro level AUjtac           = imp_intro level THENL [IDTAC; AUjtac]   ;;
   let Imp_intro                       = ImpIntro 1;;
   let Impintro                        = Imp_intro membership;;

   let EquivIntro level AUjtac BUjtac  = equiv_intro level THENL [IDTAC;AUjtac;IDTAC;BUjtac];;
   let Equiv_intro                     = EquivIntro 1;;
   let Equivintro                      = Equiv_intro membership membership;;



   %  All-introduction for general PRL-types    %

   let int_all_intro          = All_intro Intro;;
   let int_induction proof    =
      (let l = length (hypotheses proof)
       in
         int_all_intro  THEN Int_elim (l+1) THEN Thinning [l+1]
      ) proof
   ;;


%%