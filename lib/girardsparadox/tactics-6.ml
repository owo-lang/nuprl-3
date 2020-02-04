
let permute_args_for_def_instantiation name args =
   letrec remove_prior_duplicates l =
      if null l then []
      if member (hd l) (tl l) then remove_prior_duplicates (tl l)
      else (hd l) . (remove_prior_duplicates (tl l))     in
   let formals = formal_list_of_def name  in
   let first_occurrences =
      rev (remove_prior_duplicates (rev (rhs_formal_occurrences_of_def name)))   in
   if not length formals = length first_occurrences then failwith `permute_args_for_def_instantiation` ;
   map   (\id. select (find_position id first_occurrences) args)
         formals 
;;


letrec restore_def_refs t =
   ( let h.l = decompose_application t in
     let def_name = 
      implode (remove_last (explode (destruct_term_of_theorem h)))  in
     instantiate_def def_name (permute_args_for_def_instantiation def_name (map restore_def_refs l))
   )
   ? map_on_subterms restore_def_refs t
;;


let RestoreDefRefsInConcl p =
  (Seq [restore_def_refs (concl p)] 
   THENL [Idtac; Refine (hyp (number_of_hyps p + 1))]
  ) p
;;

let RestoreDefRefsInHyp i p =
  (   Seq [restore_def_refs (type_of_hyp i p)] 
   THENL [Refine (hyp i); Thinning [i]]
  ) p
;;




let SwapEquandsInConcl p =

(  let [t;t'],T = destruct_equal (concl p)   in
   Seq [make_equal_term T [t';t]]
   THENL [Idtac; Refine equality]
)  p
?  failwith `SwapEquandsInConcl`
;;


let SwapEquandsInHyp i p =
(  let [t;t'],T = destruct_equal (type_of_hyp i p) in
   Seq [make_equal_term T [t';t]]
   THENL [Refine equality; Thinning [i]]
)  p
?  failwith `SwapEquandsInHyp`
;;


% Equality subgoal comes first %
let SubstConcl t' p =

(  ParallelSeq [make_equal_term (make_universe_term big_U) [t';concl p]
               ;t'
               ]
   THENL [Idtac
         ;Idtac
         ;\p. let x = undeclared_id p `x` in
              (TagHyp (number_of_hyps p) x
               THEN Refine (explicit_intro (make_var_term x))
               THEN Refine equality
              ) p
         ]
) p

;;




% Equality subgoal comes first %
let SubstHyp i H' p =
(  let x,H = destruct_hyp i p in
   let n = number_of_hyps p   in
   if not x=`NIL` then failwith `SubstHyp: not yet implemented for tagged hyps.` 
   else
      let y = undeclared_id p `y`   in
      Seq [make_equal_term (make_universe_term big_U) [H';H]
          ;H'
          ]
      THENL [Idtac
            ;TagHyp i y THEN Refine (explicit_intro (make_var_term y)) THEN Refine equality 
            ;Thinning [i; n+1]
            ]
)  p
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


let ChainHypTactics TacticList p =
   letrec Aux Ts p' =
      if null Ts then Idtac p'
      else (hd Ts THEN IfThenOnConcl (\c. c = concl p') (Aux (tl Ts))) p'    in
   Aux TacticList p
;;

let RepeatHypTactic T hyps =
   ChainHypTactics (map T hyps)
;;

let RewriteConclWithLemmasOver (name_and_over_id_list: (tok#tok) list) over_term p =
   
(  let over_ids = map (\x,y. y) name_and_over_id_list    in
   let over_vars = map (\x. make_var_term x) over_ids in
   let over_bindings = match over_term (concl p) over_ids   in
   let replacements, lemma_instantiators =
      split
         (map (\name, over_id.
               let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
               let instance = lookup over_bindings over_id  in
               let instantiation_terms = 
                  map (lookup (match e instance ids)) ids      in
               let subst_list = (map (\x. make_var_term x) ids) com instantiation_terms  in
               substitute e' subst_list
               ,
               InstantiateLemma name instantiation_terms
              )
              name_and_over_id_list
         )        in
   SubstConcl (substitute over_term (over_vars com replacements))
   THENL [ChainHypTactics lemma_instantiators; Idtac]
)  p
;;







let RewriteConclWithLemmas names p =
   letrec aux remaining_names partial_over_term collected_names_and_ids =
      if null remaining_names then partial_over_term, collected_names_and_ids
      else 
        (let over_id = undeclared_id p `z`   in
         let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem (hd names))  in
         let newer_over_term = 
            replace_subterm
               (get_contained_instance partial_over_term e ids)
               (make_var_term over_id)
               partial_over_term         in
         aux remaining_names newer_over_term ((hd names, over_id).collected_names_and_ids)
        )
        ? aux (tl remaining_names) partial_over_term collected_names_and_ids     in
   let over_term, names_and_ids = aux names (concl p) []  in       
   RewriteConclWithLemmasOver names_and_ids over_term p
;;


let ModifyConcl f p =
   (SubstConcl (f (concl p)) THEN RestoreDefRefsInConcl)
   p
;;

let ModifyHyp f i p =
   (SubstHyp i (f (type_of_hyp i p))
    THENL [ApplyToLastHyp RestoreDefRefsInHyp; RestoreDefRefsInConcl]
   ) p
;;



% Wimpy for now. %
let certainly_equal type1 type2 =
   simplify (compute type1) = simplify (compute type2)
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
          (Refine    (integer_equality_induction 
            `nil` make_nil_term `nil` `nil`)
      ORELSE
      let (),(),(),u = destruct_integer_induction t  in
      let [n;y],() = destruct_bound_id u  in
      Refine   (integer_equality_induction
            `nil` make_nil_term
            (undeclared_id_using p n) 
            (undeclared_id_using p y))
          ) p

   if is_list_induction_term t then
          (let using = compute (get_type p (fst (destruct_list_induction t)))  in 
      Refine   (list_equality_induction 
            `nil` make_nil_term using `nil` `nil` `nil`)
      ORELSE
      let (),(),u = destruct_list_induction t  in
      let [h;t;v],() = destruct_bound_id u in
      Refine   (list_equality_induction
            `nil` make_nil_term using
            (undeclared_id_using p h) 
            (undeclared_id_using p t) 
            (undeclared_id_using p v))
               ) p

   if is_decide_term t then 
          (let using = compute (get_type p (fst (destruct_decide t)))  in 
      Refine   (union_equality_decide
            `nil` make_nil_term using `nil` `nil`)
      ORELSE
      let (),u,v = destruct_decide t  in
      let [x],() = destruct_bound_id u in
      let [y],() = destruct_bound_id v  in
      Refine   (union_equality_decide
            `nil` make_nil_term using 
            (undeclared_id_using p x) 
            (undeclared_id_using p y))
               ) p


   if is_spread_term t then
          (let using = compute (get_type p (fst (destruct_spread t)))  in 
      Refine   (product_equality_spread
            `nil` make_nil_term using `nil` `nil`)
      ORELSE
      let (),u = destruct_spread t  in
      let [x;y],() = destruct_bound_id u in
      Refine   (product_equality_spread
            `nil` make_nil_term using
            (undeclared_id_using p x) 
            (undeclared_id_using p y))
               ) p

   if is_apply_term t then
      (let b,a = destruct_apply t  in
         (  let using = (compute (get_type p b))   in
            let x,A,B = destruct_function using in
            let T' = if x=`NIL` then B 
                     else substitute B [make_var_term x,a]  in
            if T'=T then
               Refine   (function_equality_apply using)
            if is_universe_term T' & is_universe_term T then
               Refine (cumulativity (destruct_universe T'))
               THEN
               Refine   (function_equality_apply using)
            else  Seq [make_equal_term T' (t.rest)]
                  THENL
                  [Refine  (function_equality_apply using)
                  ;ApplyToLastHyp Inclusion
                  ]
                  ORELSE IfThen (\p. certainly_equal T T') (SubstConclType T')
         )
         ORELSE
         (\p. Refine (function_equality_apply
                        (make_function_term `nil` (compute (get_type p a)) T))
                     p)
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











let MemberIntro =

  Try
     (\ p .
   let tl,T = destruct_equal (concl p) in
   let T'.tl' = map_on_some 
                 (\x. if is_macro_term x then fail;
           let (),n = no_extraction_compute x in
           if n=0 then fail
           else (make_tagged_term n x))
           (T.tl)    in
   Refine (direct_computation (make_equal_term T' tl')) p)
  
  THEN

  (\ p .
       (let (t.tl),T = destruct_equal (concl p)  in
   if not (null (filter (\x. not term_kind x = term_kind t) tl))  
   then fail 
   ;
   let type = compute T in 

   if is_macro_term t then
                Trivial
                ORELSE
      SequenceOnSameConcl
      [ Refine (lemma (membership_theorem_of_macro_term t) `nil`)
      ; RepeatFunctionElim (number_of_hyps p + 1)
                 (map (\x. snd x) 
                         (match_part_in_context
                  member_of_membership_theorem_matrix
                  (main_goal_of_theorem
                     (membership_theorem_of_macro_term t))
                  t
                  p ))
                 []
      ; Refine equality
        ORELSE
        ApplyToLastHyp Inclusion
      ]

   if is_apply_term t & is_rec_term T then
      Trivial
      ORELSE   
      (  Refine (recursive_type_equality_rec big_U)
         THEN
         ComputeConclTypeFor 1 )
   
   if is_apply_term t 
      & (is_set_term T or (is_set_term type & (not T = get_type p t ? false))) then
      Trivial
      ORELSE
      (ComputeConclType THEN SetElementIntro)

   if is_apply_term t & is_quotient_term type then
      Trivial 
      ORELSE
      Refine (quotient_equality_element big_U)

   if is_any_term t then EqualityIntro 

   if is_canonical_term t then
   
          ComputeConclType

          THEN

          (if is_set_term type then
         SetElementIntro

      if is_quotient_term type then
         Refine (quotient_equality_element big_U)

      if is_rec_term type then
         (Refine (recursive_type_equality_rec big_U))
            THEN
            ComputeConclTypeFor 1
            
      else EqualityIntro )

   if is_int_exp t & not is_int_term T then
      ComputeConclType
      THEN
      SetElementIntro
      THEN
      Try (Refine (arith big_U))
         
   if is_noncanonical_term t then EqualityIntro

   if is_term_of_theorem_term t then
                Trivial
                ORELSE
      (   Refine (def (destruct_term_of_theorem t) `nil`)
          THEN
          ( Refine equality
            ORELSE
            Inclusion (number_of_hyps p + 1)
          )
      )

   if is_var_term t then
                Trivial
                ORELSE
      SetElementIntro
      ORELSE
      Inclusion (find_declaration (destruct_var t) p)

   else fail

       )
       p )

;;








let StrongMember = Repeat MemberIntro ;;




let Member =
   Repeat
   (\p.   
        if
         ((let (t.t'.()),() = destruct_equal (concl p) in not compute t = compute t') ? false)
         or
         (let (t'.()),() = destruct_equal (concl p) in
            let t = fst (no_extraction_compute t')  in   
            not is_macro_term t'
            & 
            (  is_list_induction_term t 
               or
               is_integer_induction_term t
               or 
               is_rec_ind_term t
            )
         )
        then fail
        else MemberIntro p
   )
;; 

% Check out Setup.. in temp first %
let SetUpForNonComputationalPortion p =
   let c = concl p   in
   if not (is_equal_term c or is_less_term c or is_squash_term c or is_void_term c) then
      failwith `SetUpForNonComputationalPortion: conclusion not appropriate` ;
(  IfThen (\p. is_squash_term c) (Refine (explicit_intro make_axiom_term))
   THEN ChainHypTactics (map (\i. let x,A = destruct_hyp i p   in
                                  let A' = compute A  in
                                  if is_squash_term A' then SquashElim i
                                  if not x=`NIL` & is_set_term A' then ExposeProperties [i]
                                  if is_set_term A' then Elim i
                                  else Idtac )
                            (upto 1 (number_of_hyps p))
                        )
)  p
;;





let StrongAutotactic =

   Repeat
   ( Trivial
     ORELSE
     StrongMember
     ORELSE
     Arith
   )
;;


let set_weak () = set_auto_tactic `refine (tactic \`WeakAutotactic\`)` ;;

let set () = set_auto_tactic `refine (tactic \`Autotactic\`)` ;;

let unset () = set_auto_tactic `Idtac` ;;

set () ;;






% (*->**->*) -> * -> (** list) -> * %
let accumulate f init_val l =
   letrec aux l =
      if null l then init_val 
      else let h.t = l  in f (aux t) h    in
   aux (rev l)
;;



% SquashElim or set elim hypotheses which might be needed in the subsequent
  proof 
%
let UnsetifyNeededHyps p =
   let c = concl p   in
   if not (is_equal_term c or is_less_term c or is_squash_term c or is_void_term c) then
      failwith `UnsetifyNeededHyps: conclusion not appropriate` ;
   let hyp_types = map type_of_declaration (hypotheses p)   in
   let already_elimd id = exists (\x. (let [t],() = destruct_equal x in destruct_var t = id) ? false)
                                 hyp_types   % this is a heuristic % in
   let tactics_etc = 
      accumulate (\(ids,tactics) (i,x,A) .
                     let A' = compute A   in
                     let hyp_is_needed =
                        not null (intersect (map destruct_var (free_vars A)) ids)
                        or member x ids   in
                     (if hyp_is_needed & not x = `NIL` 
                      then x.ids else ids
                     )
                     , 
                     (if not hyp_is_needed then tactics
                      if is_squash_term A' then SquashElim i . tactics
                      if not x=`NIL` & is_set_term A' then
                        (if already_elimd x then tactics else ExposeProperties [i] . tactics)
                      if is_set_term A' then Elim i . tactics
                      else tactics)
                 )
                 (map destruct_var (if is_void_term c then free_vars (type_of_hyp (number_of_hyps p) p)
                                                      else free_vars c)
                  ,[])
                 (rev ( (upto 1 (number_of_hyps p)) com (map destruct_declaration (hypotheses p))))
   in
(  IfThen (\p. is_squash_term c) (Refine (explicit_intro make_axiom_term))
   THEN ChainHypTactics  (snd tactics_etc)  % tactics left in reverse order because of thinning %
)  p
;;



let Autotactic =
   
      (Repeat
         (  Trivial
            ORELSE Member
            ORELSE Arith
            ORELSE (IfThenOnConcl (\c. exists is_arith_exp (fst (destruct_equal c)))
                                  SetElementIntro)
            ORELSE Intro
            ORELSE UnsetifyNeededHyps
         )
      )
;;


letrec RepeatUntil halting_predicate Tactic p =
   IfThen (\p. not halting_predicate p) (Try (Tactic THEN RepeatUntil halting_predicate Tactic)) p
;;

let is_arith_goal p = 
   (exists is_arith_exp (fst (destruct_equal (concl p))))
   ? false
;;


let ReduceConclToAssumedEqualities =
   Repeat
      (IfThenOnConcl
         (\c. (let [t;t'],() = destruct_equal c in not t=t') ? false)
         (MemberIntro THEN Try (Refine equality)))
;;


letrec IntroTerms terms =
   IntroTerm (hd terms) 
   THEN 
   (\p.IntroTerms (tl terms) p
       ?
       Idtac p
   )
;;
