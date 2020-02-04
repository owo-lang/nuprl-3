
let ElimLastHyp p = Elim (number_of_hyps p) p ;;





%  Bring all hypotheses which contain id as a free variable to the conclusion
   side of the sequent.
%
let BringDependingHyps id p =
        
  (      let i = find_declaration id p          in
        
        let dependent_hyp_nums =
                tl (propagate_thinning (hypotheses p) [i]) in

         let hyps_to_bring = 
                map (\i. select i (hypotheses p)) dependent_hyp_nums in

        letrec build_function_term hyps =
                ( let x,A = destruct_declaration (hd hyps) in
                  make_function_term x A (build_function_term (tl hyps))
                )
                ?
                concl p                   in

        Seq [build_function_term hyps_to_bring]
        THENL
        [Thinning dependent_hyp_nums
        ;RepeatmFor (length hyps_to_bring)
                 ( Hypothesis
                   ORELSE 
                   (Refine equality)
                   ORELSE 
                   ApplyToLastHyp 
                        (\i p . let x = fst (destruct_function 
                                                (type_of_hyp i p))  in
                                if x = `NIL` then Elim i p 
                                else ElimOn i (make_var_term x) p
                        )
                 )
        ]
  ) p

;;










letrec RepeatAndElim i p =
        Try
        ( IfOnHyp i (\x,A. is_product_term A) (Elim i) Fail
          THEN
          Thinning [i]
          THEN
          RepeatAndElim (number_of_hyps p + 1)
          THEN
          RepeatAndElim (number_of_hyps p)
        )
        p
;;


letrec RepeatOrElim i p =
   Try
        ( IfOnHyp i (\x,A. is_union_term A) (Elim i) Fail
          THEN
          Thinning [i]
          THEN
          ApplyToLastHyp RepeatOrElim
        )
        p
;;




let ForEachHypInRange T i j p =

        letrec Aux j p = if j < i then Idtac p else (T j THEN Aux (j-1)) p       in
        Aux j p
;;



let ForEachHypFrom T i p = ForEachHypInRange T i (number_of_hyps p) p ;;




let RepeatAndOrElim i p =
        Repeat
          ( Progress
              (   ForEachHypFrom (\i. RepeatAndElim i ORELSE RepeatOrElim i) i))
          p
;;


let RepeatSetElim i  =
        letrec Aux i =
                Try
                (ComputeHyp i 
                 THEN IfOnHyp 
                                        i
                                        (\x,H. is_set_term H)
                                        (\p. (Elim i THEN Aux (number_of_hyps p + 1)) p)
                                        (\p. fail))   in
        Aux i
;;



let RepeatFunctionElimFor i n instantiation_list binding_list =

  letrec Aux j n instantiation_list =
  
     if n < 1 then Idtac else

     Try

     (\ p .
        (let (),A = destruct_hyp j p in
         let x,(),() = destruct_function A in
         if x=`NIL` then
                Refine (function_elim_independent j `NIL`)
                THEN
                (if i=j then Idtac else Thinning [j])
                THENL
                [Idtac
                ;(\p. Aux (number_of_hyps p) (n-1) instantiation_list p)
                ]
         else   
                let new_list, term =  (instantiation_list, (lookup binding_list x))
                                        ? (tl instantiation_list, hd instantiation_list)    in
                Refine (function_elim j term `NIL`)
                THEN
                (if i=j then Idtac else Thinning [j])
                THENL
                [Idtac
                ;\p. Aux (number_of_hyps p) (n-1) new_list p
                ]
        )
        p     
     )                            in

   Aux i n instantiation_list

;;



let RepeatFunctionElim i instantiation_list binding_list  =

  letrec Aux j instantiation_list =
  
     Try

     (\ p .
        (let (),A = destruct_hyp j p in
         let x,(),() = destruct_function A in
         if x=`NIL` then
                Refine (function_elim_independent j `NIL`)
                THEN
                (if i=j then Idtac else Thinning [j])
                THENL
                [Idtac
                ;(\p. Aux (number_of_hyps p) instantiation_list p)
                ]
         else
                let new_list, term =  (instantiation_list, (lookup binding_list x))
                                        ? (tl instantiation_list, hd instantiation_list)    in
                Refine (function_elim j term `NIL`)
                THEN
                (if i=j then Idtac else Thinning [j])
                THENL
                [Idtac
                ;\p. Aux (number_of_hyps p) new_list p
                ]
        )
        p     
     )                            in

   Aux i instantiation_list

;;

let RepeatAtomicNotFunctionElim i instantiation_list binding_list  =

  letrec Aux j instantiation_list =
  
     Try

     (\ p .
        (let (),A = destruct_hyp j p in
         if is_not_term A then fail ; 
         let x,(),() = destruct_function A in
         if x=`NIL` then
                Refine (function_elim_independent j `NIL`)
                THEN
                (if i=j then Idtac else Thinning [j])
                THENL
                [Idtac
                ;(\p. Aux (number_of_hyps p) instantiation_list p)
                ]
         else
                let new_list, term =  (instantiation_list, (lookup binding_list x))
                                        ? (tl instantiation_list, hd instantiation_list)    in
                Refine (function_elim j term `NIL`)
                THEN
                (if i=j then Idtac else Thinning [j])
                THENL
                [Idtac
                ;\p. Aux (number_of_hyps p) new_list p
                ]
        )
        p     
     )                            in

   Aux i instantiation_list

;;




%  Match the conclusion against part of the conclusion of the implication in
   hypothesis i, generating the antecedents of the implication as subgoals.
   Use the term list for the terms required to elim the implication.  "not"
   terms are treated specially.
%
let BackThruHypUsing i inst_list p =          
        let T = type_of_hyp i p in
        let C = concl p   in
        let match_bindings = 
                match_part_in_context 
                        (if is_not_term C then atomic_not_consequent else consequent)
                        T
                        (concl p) 
                        p                in
(        Progress (RepeatAndElim i THEN Hypothesis)
        ORELSE
        (        (if is_not_term C then RepeatAtomicNotFunctionElim else RepeatFunctionElim)
                        i inst_list match_bindings
                THEN
                (\ p .
                        (if C = concl p then
                         ApplyToLastHyp RepeatAndElim 
                         THEN Hypothesis
                          else Idtac
                        )
                        p
                )
        )
)  p
;;




let BackThruHyp i p = BackThruHypUsing i [] p ;;




%  Use BackThruHyp repeatedly, trying the tactic argument when unsuccessful.
%
letrec BackchainWith Tactic p =

        let AtomizeConcl =
                REPEAT
                (\ p .
                        let c = concl p in
                        if is_function_term c or is_and_term c then Intro p
                        else fail
                )                        in

        ( AtomizeConcl
          THENW
          ( (ApplyToAHyp BackThruHyp THENM BackchainWith Tactic)
            ORELSE
            Tactic
          )
             
        )
        p
;;

             



let Backchain = BackchainWith (\p. fail) ;;




let Lemma name =

        Refine (lemma name `NIL`)
        THEN
        ApplyToLastHyp BackThruHyp
        THEN
        ApplyToLastHyp (\i. Thinning [i])
;;

let LemmaUsing name term_list =

        Refine (lemma name `NIL`)
        THEN
        ApplyToLastHyp (\i. BackThruHypUsing i term_list)
        THEN
        ApplyToLastHyp (\i. Thinning [i])
;;





let InstantiateLemma name term_list p =

   letrec make_instance ids_so_far t =
      ( if is_not_term t then fail ;
        let x,A,B = destruct_function t   in
        if x = `NIL` then make_instance ids_so_far B
        else make_instance (x.ids_so_far) B
      )
      ?
      substitute t 
         ((map (\ x. make_var_term x) (rev ids_so_far)) com term_list)  in

(  Seq [make_instance [] (main_goal_of_theorem name)]
   THENL
   [Refine (lemma name `NIL`) 
         THEN ApplyToLastHyp (\i. RepeatAtomicNotFunctionElim i term_list [])
         THEN (\p'. let n = number_of_hyps p and n' = number_of_hyps p' in 
                    if n' > n+1 then Thinning [n+1] p' else Idtac p'  )
   ;Idtac
   ]
)  p

;;



let Cases terms =

        Seq [make_disjunction terms]
        THENL [Idtac; ApplyToLastHyp RepeatOrElim]

;;



let ChainSeqWithReln t relnands lemma_name p =

  (      if length relnands < 2 then failwith `ChainSeqWithReln` ;
        let xtok,temp = destruct_lambda t        in
        let ytok,R = destruct_lambda temp        in
        let x,y = make_var_term xtok, make_var_term ytok    in
        let chain = 
                map
                  (\s,t. substitute R [x,s; y,t])
                  ( (remove_last relnands) 
                    com 
                     (tl relnands)
                  )      in
        let m = length relnands       in
        let n = number_of_hyps p      in
        let final_relate = substitute R [x, hd relnands; y, last relnands]  in

        letrec ApplyTransitivity i p =
                ( if i = m-1 then Hypothesis
                  else LemmaUsing lemma_name [select (i+1) relnands]
                       THENM
                       (Hypothesis ORELSE ApplyTransitivity (i+1))
                ) p              in

        Seq (chain @ [final_relate])
        THENL
        build_list [m-1, ThinToEnd (n+1)
                   ;1,   ApplyTransitivity 1
                   ;1,   \p. Thinning (upto (n+1) (number_of_hyps p - 1)) p
                   ]

  ) p

;;

let ChainSeqWithEq equands eq_type p =

  (      if length equands < 2 then failwith `ChainSeqWithEq` ;
        let chain = 
                map
                  (\s,t. make_equal_term eq_type [s;t])
                  ( (remove_last equands) 
                    com 
                     (tl equands)
                  )      in
        let m = length equands        in
        let n = number_of_hyps p      in
        let final_relate = 
                make_equal_term eq_type [hd equands; last equands]   in

        Seq (chain @ [final_relate])
        THENL
        build_list [m-1, ThinToEnd (n+1)
                   ;1,   Refine equality
                   ;1,   \p. Thinning (upto (n+1) (number_of_hyps p - 1)) p
                   ]

  ) p

;;




let ChainSeq term_list p =

        let ThinOut p' = 
                Thinning 
                  (upto (number_of_hyps p + 1) (number_of_hyps p' -1))
                  p'             in
        (Seq term_list THEN ThinOut) p

;;



let ExposeArithableHyps p =

        letrec Aux i p =

                if i < 1 
                then Idtac p
                if is_and_term (type_of_hyp i p)
                   &
                   exists (\t. is_int_term (snd (destruct_equal t))
                               or
                               is_int_term 
                                  (snd (destruct_equal (destruct_not t)))
                               or
                               is_less_term t
                               or
                                is_less_term (destruct_not t)
                               ?
                               false
                          )
                          (destruct_conjunction (type_of_hyp i p))
                then (RepeatAndElim i THEN (Aux (i-1))) p
                else Aux (i-1) p                    in

        Aux (number_of_hyps p) p

;;






let NonNegInduction i newid =

  ComputeHypType i
  THEN
  (\ p .
     (  let T = concl p               in
        let n_tok,H = destruct_hyp i p  in
        if n_tok=`NIL` then failwith `hyp. to elim must have label` ;
        let n = make_var_term n_tok            in
        let x,A,B = destruct_set H     in
        let ineq,P = (destruct_and B)
                     ?
                     (B,make_nil_term)        in
        let no_P = is_nil_term P      in
        let lb = % strict lower bound for n.
                   The first conjunct of B must be of the form c<x, c<x+1, or
                   x<c->void (3 reasonable ways of specifying a lb for x).
                 %
                 ( let c,y = destruct_less ineq in
                   if not x = destruct_var y then fail ;
                   destruct_integer c
                 )
                 ?
                 ( let c,add = destruct_less ineq        in
                   let y,one = destruct_addition add     in
                   if not x = destruct_var y or not destruct_integer one = 1
                        then fail ;
                   destruct_integer c - 1
                 )
                 ?                
                 ( let (),ineq',C = destruct_function ineq in
                   let y,c = destruct_less ineq'        in
                   if not x = destruct_var y or not is_void_term C then fail ;
                   destruct_integer c - 1
                 )
                 ? failwith `hyp. has inappropriate type`  in
        if lb < -1 then failwith `smallest member must be non-neg.` ;

        let lemma = % all n:int. lb<n => ||P[n/x]|| => T  
                        (with appropriate adjustment if no P) 
                    %
                    make_function_term
                        (destruct_var n)
                        make_int_term
                        ( if no_P then
                                make_implication
                                        [make_less_term 
                                                (make_integer_term lb)
                                                n
                                        ;T
                                        ]
                          else    make_implication
                                        [make_less_term 
                                                (make_integer_term lb)
                                                n
                                        ;make_squash_term
                                                (substitute P 
                                                        [make_var_term x,
                                                         n]
                                                )
                                        ;T
                                        ]
                        )        in

        let SetElim = 
                Elim i THENW (if no_P then Idtac 
                              else ApplyToNthLastHyp 2 Elim) in

        let UseLemma p =
                let k = number_of_hyps p      in
                ( ElimOn k n
                  THENM
                  ( ApplyToLastHyp Elim
                    THENL
                    [SetElim THENW Arith
                    ;if no_P then Hypothesis
                     else ApplyToLastHyp Elim
                          THENL
                          [ Refine (explicit_intro make_axiom_term)
                            THEN SetElim
                            THENW SetElementIntro 
                          ; Hypothesis
                          ]
                    ]
                  )
                )
                p                in
        
        let ProveDownCase = Intro THENW Arith in

        let ProveZeroCase p = 
                if lb = -1 then 
                        ( Intro 
                          THENW
                          ( Thinning [number_of_hyps p + 1]
                            THEN
                            (if no_P then Idtac else Intro)
                          )
                        )
                        p
                else (Intro THENW Arith) p             in

        let ProveUpCase p =
                (let base = make_integer_term (lb + 1)    in
                 let k = number_of_hyps p      in
                 let n' = make_var_term (id_of_hyp (k-2) p)        in
                 if lb = -1 then
                        Intro THENW (Elim k THENL [Arith; Thinning [k;k+1]])
                 else     
                        Intro
                        THENW
                        ( Cases [make_equal_term make_int_term [n';base]    
                              ;make_less_term base n']
                          THENL
                          [Arith
                          ;Thinning [k-1;k;k+1] 
                           THEN (if not no_P then Intro else Idtac)
                          ;Elim k THENL [Arith; Thinning [k-1;k;k+1]
                                                THEN
                                                ( if not no_P then Intro
                                                  else Idtac)
                                        ]
                          ]
                        )
                )
                p        in

        Seq [lemma]
        THENL
        [Intro
         THENW ( ApplyToLastHyp (\i. Refine (integer_elim i `NIL` newid))
                 THEN Thinning [i; number_of_hyps p + 1]
                 THENL [FastAp ProveDownCase; ProveZeroCase; ProveUpCase]
               )
        ;FastAp UseLemma
        ]

     )
     p
   
   )


;;




   


   


%  Type of hyp i must be Int.
%
let NonNegInductionUsing i j newid p =

     (  let T = concl p               in
        let n_tok,H = destruct_hyp i p  in
        if n_tok=`NIL` then failwith `hyp. to elim must have label` ;
        let n = make_var_term n_tok            in
        let lb = j-1  % strict lower bound for n %  in
        if lb < -1 then failwith `smallest member must be non-neg.` ;

        let lemma = % all n:Int. lb<n => T  %
                    make_function_term
                        (destruct_var n)
                        make_int_term
                        (make_implication
                                [make_less_term (make_integer_term lb) n
                                ;T
                                ]
                        )        in

        let UseLemma p =
                let k = number_of_hyps p      in
                ( ElimOn k n
                  THENM
                  ApplyToLastHyp Elim
                )
                p                in
        
        let ProveDownCase = Intro THENW Arith     in

        let ProveZeroCase p = 
                if lb = -1 then 
                        ( Intro 
                          THENW 
                          Thinning [number_of_hyps p + 1]
                        )
                        p
                else (Intro THENW Arith) p             in

        let ProveUpCase p =
                (let base = make_integer_term (lb + 1)    in
                 let k = number_of_hyps p      in
                 let n' = make_var_term (id_of_hyp (k-2) p)        in
                 if lb = -1 then
                        Elim k THENL [Arith; Thinning [k]]
                 else     
                        Intro
                        THENW
                        ( Cases [make_equal_term make_int_term [n';base]    
                              ;make_less_term base n']
                          THENL
                          [Arith
                          ;Thinning [k-1;k;k+1] 
                          ;Elim k THENL [Arith; Thinning [k-1;k;k+1]]
                          ]
                        )
                )
                p        in

        Seq [lemma]
        THENL
        [Intro THENW ( ApplyToLastHyp (\i. Refine (integer_elim i `NIL` newid))
                       THEN Thinning [i; number_of_hyps p + 1]
                       THENL [FastAp ProveDownCase; ProveZeroCase; ProveUpCase]
                     )
        ;FastAp UseLemma
        ]

     )
     p

;;



   



   

