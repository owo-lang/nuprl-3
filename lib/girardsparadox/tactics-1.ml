%
********************************************************************************
********************************************************************************
********************************************************************************

   tactics-1

********************************************************************************
********************************************************************************
********************************************************************************
%












let Refine r p = refine r p ;;

let Arith = Refine (arith big_U) ;;

let Thinning l p = Refine (thinning l) p ;;



let Hypothesis p =  hypothesis p ;;

let Immediate p  = immediate p ;;

let Try p = TRY p ;;

let Seq term_list = 
        Refine (seq term_list (replicate `NIL` (length term_list)))
;;

let Idtac p = IDTAC p ;;

let Progress T = PROGRESS T ;;

let Fail p = fail ;;

let Trivial = Hypothesis ORELSE (Refine equality) ;;


lettype bogus_type = (void#void#void+void)->void ;;
lettype tactical = bogus_type;;


let ApplyToLastHyp (T: int->tactic) p = T (number_of_hyps p) p ;;


let ApplyToAHyp (T: int->tactic) p =
        letrec Aux i p = 
                if i=0 then failwith `ApplyToAHyp`
                else (T i ORELSE Aux (i-1)) p   in
        Aux (length (hypotheses p)) p
;;



let If (predicate: proof -> bool) (T1: tactic) (T2: tactic) p =
        if predicate p then T1 p else T2 p
;;

let IfOnConcl (concl_predicate: term -> bool) (T1: tactic) (T2: tactic) p =
        if concl_predicate (concl p) then T1 p else T2 p
;;

let IfOnHyp i (hyp_predicate: tok#term -> bool) (T1: tactic) (T2: tactic) p =
        if hyp_predicate (destruct_declaration
                              (select i (hypotheses p)))
        then T1 p
        else T2 p
;;


let IfThen predicate (T: tactic) =
        If predicate T Idtac
;;

let IfThenOnConcl concl_predicate (T: tactic) =
        IfOnConcl concl_predicate T Idtac
;;

let IfThenOnHyp i hyp_predicate (T: tactic) =
        IfOnHyp i hyp_predicate T Idtac
;;


let ComputeConclUsing tagger p =
   Refine (direct_computation (tagger (concl p))) p
;;


let ComputeHypUsing tagger i p =
   Refine (direct_computation_hyp
            i
            (tagger (type_of_hyp i p)))
          p
;;


% Not too efficient. 
%
let tag_all_legal_subterms t =
   letrec tag_everything t =
        if is_noncanonical_term t then
                make_tagged_term 0 (map_on_subterms tag_everything t)  
        else    map_on_subterms tag_everything t        in
   remove_illegal_tags (tag_everything t)
;;





let ComputeConcl p =
  (     let t = concl p  in
        if is_canonical_type t or is_var_term t then
                Idtac 
        else
                ComputeConclUsing (make_tagged_term 0)
  )

  p

;;




let ComputeConclType p =

(       let t = concl_type p  in
        if is_canonical_type t or is_var_term t then
                Idtac 
        else
                ComputeConclUsing (map_on_equality_type (make_tagged_term 0))
                ORELSE
                ComputeConclUsing (make_tagged_term 0)
)

p

;;



let ComputeConclTypeFor i p =

(       let t = concl_type p  in
        if is_canonical_type t or is_var_term t then
                Idtac
        else
                ComputeConclUsing (map_on_equality_type (make_tagged_term i))
                ORELSE
                ComputeConclUsing (make_tagged_term i)
)

p       

;;


let ComputeHyp i p =
        let t = type_of_hyp i p         in
        if is_canonical_type t or is_var_term t then
                Idtac p
        else ComputeHypUsing (make_tagged_term 0)i p
;;



let ComputeHypType i p =
(       let (),H = destruct_hyp i p in
        let hyp_type = hyp_type i p     in
        if is_canonical_type hyp_type or is_var_term hyp_type then
                Idtac
        else
                ComputeHypUsing (map_on_equality_type (make_tagged_term 0)) i
                ORELSE
                ComputeHypUsing (make_tagged_term 0) i
)
p
;;




let ComputeHypTypeFor n i p =
(       let (),H = destruct_hyp i p in
        let hyp_type = hyp_type i p     in
        if is_canonical_type hyp_type or is_var_term hyp_type then
                Idtac
        else
                ComputeHypUsing (map_on_equality_type (make_tagged_term 0)) i
                ORELSE
                ComputeHypUsing (make_tagged_term n) i
)
p
;;





let ElimOn i term =
        ComputeHypType i
        THEN
        (\ p .
                let x,() = destruct_hyp i p  in
                if x = `NIL` then
                        Refine (function_elim i term `NIL`) p
                else
                        Refine (function_elim i term (undeclared_id p `y`)) p
        )
;;




let Elim i =

  (ComputeHypType i)  
  
  THEN

  (\ p .

      let x, T = destruct_hyp i p  in

      if is_void_term T then
         Refine (void_elim i) p

      if is_int_term T then
        (let new_a = undeclared_id p `a` in
         Refine (integer_elim i `NIL` `NIL`) 
         ORELSE
         Refine (integer_elim i `NIL` (undeclared_id p `n`)) 
        ) p

      if is_list_term T then
        (let new_a = undeclared_id p `a` and new_h = undeclared_id p `h` in
         Refine (list_elim i `NIL` new_h `NIL`)
         ORELSE
         Refine (list_elim i `NIL` new_h (undeclared_id p `t`)) 
        ) p

      if is_union_term T then
         if x=`NIL` then
            Refine (union_elim i `NIL` `NIL`) p
         else
            Refine (union_elim i `a` `a`) p

      if is_function_term T then
         Refine (function_elim_independent i
                        (if x=`NIL` then `NIL` else undeclared_id p `b`)) 
                p

      if is_product_term T then
         if x=`NIL` then
            (   (Refine (product_elim i `NIL` `NIL`))
                ORELSE
                (Refine (product_elim i 
                                (undeclared_id p `a`)
                                `NIL`))
            ) p
         else
            Refine (product_elim i
                        (undeclared_id p `a`)
                        (undeclared_id p `a`))  p

      if is_quotient_term T then
         Refine (quotient_elim i big_U 
                               (undeclared_id p `u`) (undeclared_id p `u`)) 
                p

      if is_set_term T then
        (Refine (set_elim i big_U `NIL`) 
         ORELSE
         Refine (set_elim i big_U (undeclared_id p `z`)) 
        ) p

      if is_rec_term T then
        (   Refine (recursive_type_elim i 1 [] [] [] [undeclared_id_using p x])
            THEN
            (  letrec tag_rec_aps t =
                  let is_rec_ap = (let a,b = destruct_apply t  in
                                   is_rec_term (snd (destruct_lambda a)))
                                   ?
                                   false  in
                  is_rec_ap => make_tagged_term 1 t 
                            |  map_on_subterms tag_rec_aps t  in
               ComputeHypUsing tag_rec_aps (number_of_hyps p + 1)
               THEN
               ComputeHypUsing
                  (map_on_equality_type tag_rec_aps)
                  (number_of_hyps p + 2) )

        ) p

      else  fail

  )

;;



let IntroLeft =
        ComputeConcl
        THEN
        (Refine (union_intro_left big_U))

;;

let IntroRight =
        ComputeConcl
        THEN
        (Refine (union_intro_right big_U))
;;




let IntroTerm term =

   ComputeConcl

   THEN

   (    Refine (product_intro_dependent term big_U `nil`)
        ORELSE
        (\ p .  Refine 
                   (product_intro_dependent
                        term
                        big_U
                        (undeclared_id_using p
                                (fst (destruct_product (concl p)))))
                   p)
        ORELSE
        Refine set_intro_independent 
        ORELSE
        (\ p .  Refine 
                   (set_intro
                        big_U
                        term
                        (undeclared_id_using p
                                (fst (destruct_set (concl p)))))
                   p)
   )
;;




let Intro =

   ComputeConcl

   THEN

   (\ p .

        let T = concl p  in

        if is_atom_term T then
           Refine (atom_intro (make_token_term `foo`)) p

        if is_universe_term T then
           Refine universe_intro_void p

        if is_int_term T then
           Refine (integer_intro_integer 0) p

        if is_list_term T then
           Refine (list_intro_nil big_U) p

        if is_union_term T then
           fail

        if is_function_term T then
           (  Refine (function_intro big_U `nil`) 
              ORELSE
              Refine (function_intro
                         big_U
                         (undeclared_id_using p (fst (destruct_function T))))
           ) p
   
        if is_product_term T & (`NIL` = (fst (destruct_product T))) then
           Refine product_intro p
           
        if is_quotient_term T then
           Refine (quotient_intro big_U) p

        if is_set_term T then
           Refine set_intro_independent p

        if is_rec_term T then
           Refine (recursive_type_intro big_U) p

        else failwith `Intro: fell through`
   )

;;


let SetElementIntro p =
  (     ComputeConclType 
        THEN
        ( Refine (set_equality_element big_U `NIL`)
          ORELSE
          Refine (set_equality_element big_U (undeclared_id p `x`))
        )
  ) p
;;
 


let SquashIntro p =
(       Refine (explicit_intro make_axiom_term)
        THEN
        SetElementIntro
) p
;;      






% Prove subgoals of the form 
     H, membership-hyp, H' >> t in T'
  where "membership-hyp" is the i-th hypothesis and is of the form
  t:T for t a var, or t in T.  Currently, this succeeds only if
  T' is a quotient_type with base type T, or T is a set type with
  base type T', or if both are universes with appropriate levels, 
  or T is equal to T', all modulo computation.
%

let Inclusion i p =

        let DeclaredInSubset i =
                Elim i
                THEN
                (\p. if is_wf_goal p then Idtac p else (Refine equality) p)  in
        
        let (t.rest),T' = destruct_equal (concl p) in

        let x,A = destruct_hyp i p  in
        
        let t_is_declared = (x = (destruct_var t) ? false)  in
        
        let subtype p =
                if t_is_declared then type_of_hyp i p
                else (T where (),T = destruct_equal (type_of_hyp i p))  in

        let TrivialInclusion =
                ComputeConclType
                THEN
                ComputeHypType i
                THEN
                Refine equality                 in

        let QuotientInclusion =
                ComputeConclType
                THEN
                (\ p .
                        if (subtype p = base_type 
                                where (),(),base_type,()
                                      = destruct_quotient (concl_type p))
                        then Idtac p
                        else ComputeHypType i p
                )
                THEN
                Refine (quotient_intro big_U)
                THEN
                (\ p . if is_wf_goal p then Idtac p 
                       else Try (Refine equality) p)    in

        let SubsetInclusion =
                if not is_membership_goal p then failwith
                        `Inclusion: need membership goal for SubsetInclusion` ;
                ComputeHypType i
                THEN
                (\ p .
                        if (concl_type p = base_type 
                                where (),base_type,() = 
                                        destruct_set (subtype p))
                        then Idtac p
                        else ComputeConclType p
                )                  
                THEN
                (\ p .
                        (if  t_is_declared then
                                DeclaredInSubset i 
                         else
                                let new_id = undeclared_id p `v`  in
                                let subset_assertion =
                                        make_function_term
                                          new_id
                                          (subtype p)
                                          (make_equal_term 
                                              (concl_type p)
                                              [make_var_term new_id])  in
                                Refine (seq [subset_assertion] [`nil`])
                                THENL
                                [Intro 
                                   THEN 
                                        (\p. if is_wf_goal p then Idtac p
                                             else DeclaredInSubset
                                                        (number_of_hyps p + 1)
                                                        p
                                        )
                                ;ElimOn (number_of_hyps p + 1) t 
                                   THEN (Refine equality)
                                ]
                        ) p 
                )                 in

        let UniverseInclusion =
                ComputeHypType i
                THEN
                ComputeConclType
                THEN
                (\ p.
                     Refine (cumulativity (destruct_universe (subtype p))) p)
                THEN
                (Refine equality)      in

       (TrivialInclusion
        ORELSE
        UniverseInclusion
        ORELSE
        QuotientInclusion
        ORELSE
        SubsetInclusion
       )
       p
;;







 
% Do the intro appropriate to the first equand of the conclusion,
  guessing all required parameters.  Fails if parameters cannot be
  guessed.  No attempt is made yet to guess over terms. %

let EqualityIntro p =


        let (t.rest),T = destruct_equal (concl p)  in

        if is_token_term t then 
                Refine atom_equality_token p

        if is_any_term t then
                Refine void_equality_any p

        if is_natural_number_term t then 
                Refine integer_equality_natural_number p

        if is_minus_term t then 
                Refine integer_equality_minus p

        if is_addition_term t then 
                Refine integer_equality_addition p
                    
        if is_subtraction_term t then 
                Refine integer_equality_subtraction p
                    
        if is_multiplication_term t then 
                Refine integer_equality_multiplication p
                    
        if is_division_term t then 
                Refine integer_equality_division p
                    
        if is_modulo_term t then 
                Refine integer_equality_modulo p

        if is_axiom_term t then
                if is_equal_term T then Refine axiom_equality_equal p
                else Refine axiom_equality_less p
 
        if is_nil_term t then 
                Refine (list_equality_nil big_U) p

        if is_cons_term t then 
                Refine list_equality_cons p

        if is_inl_term t then 
                Refine (union_equality_inl big_U) p
  
        if is_inr_term t then 
                Refine (union_equality_inr big_U) p

        if is_lambda_term t then
               (Refine (function_equality_lambda big_U `nil`)
                ORELSE
                Refine (function_equality_lambda big_U
                        (undeclared_id_using p (fst (destruct_lambda t))))
               ) p

        if is_pair_term t then 
               (let v,(),() = destruct_product T  in
                if v=`nil` then
                   (Refine product_equality_pair_independent) p
                else
                   (   Refine (product_equality_pair big_U `nil`) 
                       ORELSE
                       Refine (product_equality_pair big_U 
                                        (undeclared_id_using p v))
                   ) p)

        if is_integer_induction_term t then 
               (Refine  (integer_equality_induction 
                                `nil` make_nil_term `nil` `nil`)
                ORELSE
                let (),(),(),u = destruct_integer_induction t  in
                let [n;y],() = destruct_bound_id u  in
                Refine  (integer_equality_induction
                                `nil` make_nil_term
                                (undeclared_id_using p n) 
                                (undeclared_id_using p y))
               ) p

        if is_list_induction_term t then
               (let using = compute (get_type p (fst (destruct_list_induction t)))  in 
                Refine  (list_equality_induction 
                                `nil` make_nil_term using `nil` `nil` `nil`)
                ORELSE
                let (),(),u = destruct_list_induction t  in
                let [h;t;v],() = destruct_bound_id u in
                Refine  (list_equality_induction
                                `nil` make_nil_term using
                                (undeclared_id_using p h) 
                                (undeclared_id_using p t) 
                                (undeclared_id_using p v))
               ) p

        if is_decide_term t then 
               (let using = compute (get_type p (fst (destruct_decide t)))  in 
                Refine  (union_equality_decide
                                `nil` make_nil_term using `nil` `nil`)
                ORELSE
                let (),u,v = destruct_decide t  in
                let [x],() = destruct_bound_id u in
                let [y],() = destruct_bound_id v  in
                Refine  (union_equality_decide
                                `nil` make_nil_term using 
                                (undeclared_id_using p x) 
                                (undeclared_id_using p y))
               ) p


        if is_spread_term t then
               (let using = compute (get_type p (fst (destruct_spread t)))  in 
                Refine  (product_equality_spread
                                `nil` make_nil_term using `nil` `nil`)
                ORELSE
                let (),u = destruct_spread t  in
                let [x;y],() = destruct_bound_id u in
                Refine  (product_equality_spread
                                `nil` make_nil_term using
                                (undeclared_id_using p x) 
                                (undeclared_id_using p y))
               ) p

        if is_apply_term t then
               (let b,a = destruct_apply t  in
                ( let using = (compute (get_type p b))  in
                  let x,A,B = destruct_function using   in
                  let T' = if x=`NIL` then B 
                           else substitute B [make_var_term x,a]        in
                  if T'=T then
                        Refine  (function_equality_apply using)
                  if is_universe_term T' & is_universe_term T then
                        Refine (cumulativity (destruct_universe T'))
                        THEN
                        Refine  (function_equality_apply using)
                  else  Seq [make_equal_term T' (t.rest)]
                        THENL
                        [Refine (function_equality_apply using)
                        ;ApplyToLastHyp Inclusion
                        ]
                )
                ORELSE
                Refine  (function_equality_apply
                                (make_function_term `nil` (compute (get_type p a)) T))
               ) p

        if is_rec_ind_term t then 
                failwith `EqualityIntro: not implemented yet for rec_ind`
        
        if is_atom_eq_term t then Refine atom_eq_equality p
  
        if is_int_eq_term t then Refine int_eq_equality p

        if is_intless_term t then Refine int_less_equality p

        if is_atom_term t then Refine atom_equality p

        if is_void_term t then Refine void_equality p

        if is_int_term t then Refine integer_equality p

        if is_less_term t then Refine less_equality p

        if is_universe_term t then Refine universe_equality p

        if is_list_term t then Refine list_equality p
 
        if is_equal_term t then Refine equal_equality p

        if is_function_term t then
               (Refine (function_equality `nil`) 
                ORELSE
                Refine (function_equality 
                          (undeclared_id_using p (fst (destruct_function t))))
               ) p

        if is_product_term t then
               (Refine (product_equality `nil`)
                ORELSE
                Refine (product_equality 
                          (undeclared_id_using p (fst (destruct_product t))))
               ) p

        if is_set_term t then
               (Refine (set_equality `nil`)
                ORELSE
                Refine (set_equality (undeclared_id_using p 
                                        (fst (destruct_set t))))
               ) p

        if is_union_term t then Refine union_equality p

        if is_quotient_term t then 
               (let v= fst (destruct_quotient t) in
                Refine (quotient_equality 
                         (undeclared_id_using p v) 
                         (undeclared_id_using p v))
               ) p

        if is_rec_term t then 
               (let l,(),(),a = destruct_rec_without_fix t  in
                let A = compute (get_type p a)  in
                Refine (recursive_type_equality (map (\x.A) l)) 
               ) p

        else failwith `EqualityIntro`

;;















