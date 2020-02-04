
let InstantiateHyp i term_list p =

  ( letrec make_instance ids_so_far t =
    ( if is_not_term t then fail ;
      let x,A,B = destruct_function t in
      if x = `NIL` then make_instance ids_so_far B
      else make_instance (x.ids_so_far) B
    )
    ?
    substitute t 
       ((map (\x. make_var_term x)
       (rev ids_so_far)) com term_list)  in

  Seq [make_instance [] (compute (type_of_hyp i p))]
  THENL
  [ComputeHyp i THEN RepeatAtomicNotFunctionElim i term_list
  ;Idtac
  ]
  ) p
;;



let ref t p = refine_using_prl_rule t p ;; 









let get_ids_equands_and_type t =
  letrec aux t ids_so_far =
    ( let x,(),B = destruct_function t  in
      aux B (if x=`NIL` then ids_so_far 
                else x.ids_so_far)
    )
    ?
    rev ids_so_far, destruct_equal t  in
  aux t []
;;



let RewriteConclWithLemmaOver name over_id over_term p =
  ( let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let instance = lookup (match over_term  (concl p) [over_id]) over_id  in
  let instantiation_terms = 
    map (lookup (match e instance ids)) ids   in
  let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
  let replacement = substitute e' subst_list  in
  let type_inst = substitute T subst_list   in
  Refine (substitution big_U
      (make_equal_term type_inst [instance; replacement])
      over_id over_term )
  THENL [Refine (lemma name `NIL`) 
         THEN (ApplyToLastHyp (\i. RepeatFunctionElim i instantiation_terms))
        ;Idtac
        ;Idtac
        ]
  ) p
;;


letrec get_contained_instance term pattern ids =
  substitute pattern (map (\x,t. make_var_term x, t) (match pattern term ids))
  ?
  letrec try_on_each_member l =
    get_contained_instance (hd l) pattern ids
    ?
    try_on_each_member (tl l)
    ?
    failwith `get_contained_instance`   in
  try_on_each_member (subterms term)
;;


let RewriteConclWithLemma name p =
  let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let over_id = undeclared_id p `z` in
  let over_term = 
    replace_subterm
      (get_contained_instance (concl p) e ids)
      (make_var_term over_id)
      (concl p)     in
  RewriteConclWithLemmaOver name over_id over_term p
;;


let RewriteConclWithRevLemmaOver name over_id over_term p =
  ( let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let instance = lookup (match over_term  (concl p) [over_id]) over_id  in
  let instantiation_terms = 
    map (lookup (match e' instance ids)) ids    in
  let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
  let replacement = substitute e subst_list in
  let type_inst = substitute T subst_list   in
  Refine (substitution big_U
      (make_equal_term type_inst [instance; replacement])
      over_id over_term )
  THENL [Refine (lemma name `NIL`) 
         THEN (ApplyToLastHyp (\i. RepeatFunctionElim i instantiation_terms))
        ;Idtac
        ;Idtac
        ]
  ) p
;;

let RewriteConclWithRevLemma name p =
  let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let over_id = undeclared_id p `z` in
  let over_term = 
    replace_subterm
      (get_contained_instance (concl p) e' ids)
      (make_var_term over_id)
      (concl p)     in
  RewriteConclWithRevLemmaOver name over_id over_term p
;;













let RewriteHypWithLemmaOver i name over_id over_term p =
  ( let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let instance = lookup (match over_term  (type_of_hyp i p) [over_id]) over_id  in
  let instantiation_terms = 
    map (lookup (match e instance ids)) ids   in
  let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
  let replacement = substitute e' subst_list  in
  let type_inst = substitute T subst_list   in
  Seq [substitute over_term [make_var_term over_id, replacement]]
      THENL  [RewriteConclWithRevLemmaOver name over_id over_term
         ;Idtac
         ]
  ) p 

;;




let RewriteHypWithLemma i name p =
  let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let over_id = undeclared_id p `z` in
  let over_term = 
    replace_subterm
      (get_contained_instance (type_of_hyp i p) e ids)
      (make_var_term over_id)
      (type_of_hyp i p)     in
  RewriteHypWithLemmaOver i name over_id over_term p
;;



let RewriteConclWithLemmasOver (name_and_over_id_list: (tok#tok) list) over_term p =
(  let over_ids = map (\x,y. y) name_and_over_id_list   in
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



let SubstForInHyp i eq_term p =
  ( 
  let [e;e'],T = destruct_equal eq_term 
  and H = type_of_hyp i p   in
  let over_id = undeclared_id p `z`   in
  let over_term = replace_subterm e (make_var_term over_id) H in

  Seq [substitute over_term [make_var_term over_id, e']]
      THENL [Refine (substitution big_U (make_equal_term T [e';e])
      over_id over_term)
        ;Idtac
        ]
  ) p
;;


let InstantiatePolyDefinedTermLemma t p =
( Refine (lemma (membership_theorem_of_poly_defined_term t) `nil`)
  THEN
  RepeatFunctionElim (number_of_hyps p + 1)
      (map (\x. snd x) 
           (  let thm = main_goal_of_theorem (membership_theorem_of_poly_defined_term t)  in
              ( match_part (get_type p) member_of_membership_theorem_matrix thm t
                ? match_part (\t. reduce (get_type p t)) member_of_membership_theorem_matrix thm t
              )
           )
      )
)
p
;;



let MemberIntro =

  Refine equality

  ORELSE

( Try ReduceConcl

  THEN

  Try
     (\ p .
  let tl,T = destruct_equal (concl p) in
  let T'.tl' = map_on_some 
               (\x. 
        let (),n = fast_ap no_extraction_compute x in
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
  let type = fast_ap compute T  in  

  if is_poly_defined_term t then
    SequenceOnSameConcl
    [ InstantiatePolyDefinedTermLemma t
    ; Refine equality
      ORELSE
      FastAp (OnLastHyp Inclusion)
    ]

  if is_apply_term t & is_rec_term T then
    (  Refine (recursive_type_equality_rec big_U)
       THEN
       ComputeConclTypeFor 1 )
  if is_apply_term t 
     & (is_set_term T or (is_set_term type & (not T = get_type p t ? false))) then
    (ComputeConclType THEN SetElementIntro)

  if is_apply_term t & is_quotient_term type then
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
    (   Refine (def (destruct_term_of_theorem t) `nil`)
        THEN
        ( Refine equality
          ORELSE
          FastAp (Inclusion (number_of_hyps p + 1))
        )
    )

  if is_var_term t then
    SetElementIntro
    ORELSE
    FastAp (Inclusion (find_declaration (destruct_var t) p))

  else fail

       )
       p )
)
;;






let Member =
  Repeat
  (\p.   
      if
      ((let (t.t'.()),() = destruct_equal (concl p) in not fast_ap compute t = fast_ap compute t') ? false)
      or
      (let (t'.()),() = destruct_equal (concl p) in
        let t = fst (fast_ap no_extraction_compute t')  in  
        (   is_list_induction_term t 
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





let StrongMember = Repeat MemberIntro ;;



