letref goal_index = 1 ;;

letref completed_proofs = []: proof list ;;

letref partial_results = []: ((proof list) # ((proof list) -> proof)) list ;;


let CollectBecausedOutGoals () =
  letrec Aux p =
    ( if rule_kind (refinement p) = `BECAUSE` then
        (postponed_membership_goals := p . postponed_membership_goals ; ())
      else ()
      ?
      ()
    )
    ;
    ( ((Aux o subproof_of_tactic_rule o refinement) p; ()) ? () )
    ;
    ( (map Aux (children p); ()) ? () )  in
  map (\ name . Aux (proof_of_theorem name) ? ()) (library ())
  ;
  ()
;;


let reset_for_membership_beating new_goals =
  postponed_membership_goals := new_goals ;
  goal_index := 1 ;
  completed_proofs := [] ;
  partial_results := [] ;
  ()
;;

let BeatOnMembershipGoalsWith T =
  let n = length postponed_membership_goals in
  if not goal_index > n loop
    ( let pl,v = T (select goal_index postponed_membership_goals) in
      ( if not null pl then (partial_results := (pl , v) . partial_results ; ())
        else (completed_proofs := v pl . completed_proofs ; ())
      )
      ; goal_index := goal_index + 1
    )
  else ()
;; 


let RealAutotactic =
    (Repeat
      ( Trivial
        ORELSE Repeat (\p. if (top_def_of_term (concl p); true) ? false
                            then (if (member (top_def_of_term (concl p))
                                             ([`imp`;`all`;`all2`;`all3`;`all4`;`uall`;`uall2`]))
                                  then Intro p else fail )
                            else (if is_function_term (concl p) then Intro p else fail)
                      )
        ORELSE Repeat NonReducingMemberIntro
      )
    )
;;


let is_ok_rule rule = 
  member_of_tok_list (rule_kind rule)
  [`EQUAL-INTRO-FUNCTION`; `EQUAL-INTRO-LAMBDA`; `EQUAL-INTRO-APPLY`; 
   `HYP`; `LEMMA` ; `EQUALITY`; `THINNING`; `CUMULATIVITY`;
   `FUNCTION-INTRO`; `DIRECT-COMP-HYP`]
;;

let no_equal_subterms t =
  letrec aux t = 
    if is_equal_term t then fail else (map aux (subterms t); true)  in
  aux t ? false
;;

let is_ok_concl_term t = 
  if is_equal_term t then 
    ( let [t'],T = destruct_equal t in 
      no_equal_subterms t' & no_equal_subterms T
    ) 
  else
    no_equal_subterms t
  ? false
;;

let have_ok_concls pfs =
  (map (\p. if not is_ok_concl_term (concl p) then fail) pfs ; true)
  ? false
;;


let first_equand_of_concl = hd o fst o destruct_equal o concl ;;

let is_ok_direct_comp p =
  first_equand_of_concl p = (first_equand_of_concl o hd o children) p
  ? true
;;


letref questionable_subproofs = []: proof list ;;

let add_questionable_subproof p =
  questionable_subproofs := p . questionable_subproofs ;
  ()
;;

let make_wf_term t = 
  make_equal_term (make_term_of_theorem_term `Type_`) [t]
;;

let direct_comp_addition p =
  let T = concl p in
  let computed_term =
    if is_equal_term T then snd (destruct_equal T) else T in
  make_sequent (hypotheses p) [] (make_wf_term computed_term)
;;

let seq_addition p =
  make_sequent (hypotheses p) [] ((make_wf_term o concl o hd o children) p)
;;


letref additional_subgoals = []: proof list ;;

let is_tau t = 
  is_universe_term t 
  or (is_term_of_theorem_term t & destruct_term_of_theorem t = `Type_`)
;;

let is_axiom t =
  ( let [t'],T = destruct_equal t in
    (is_tau t' & is_tau T)
    or (is_term_of_theorem_term t' & T = main_goal_of_theorem (destruct_term_of_theorem t'))
    or  (is_term_of_theorem_term t' & is_tau T 
          & is_tau (main_goal_of_theorem (destruct_term_of_theorem t'))
        )
  ) ? false
;;


let add_additional_subgoal p =
  let k = rule_kind (refinement p)  in
  ( if k = `DIRECT-COMP` then
      (let p' = direct_comp_addition p in 
       if is_axiom (concl p') then [] else additional_subgoals :=  p' . additional_subgoals 
      )
    if k = `SEQUENCE` then
      additional_subgoals :=  seq_addition p . additional_subgoals
    else failwith `add_additional_subgoal`
  )
  ;
  ()
;;



let is_identity_seq p =
  ( let [t],T = (destruct_equal o concl) p  in
    let [t'],T' = (destruct_equal o concl o hd o children) p  in
    t=t' & is_tau T & is_tau T'
  ) ? false
;;

% An optimization %
letrec skip_ok_direct_comps p =
  if is_refined p & rule_kind (refinement p) = `DIRECT-COMP` & is_ok_direct_comp p then
    (skip_ok_direct_comps o hd o children) p
  else p
;;

let filter_proofs pfs =
  letrec aux p =
    if not is_refined p or is_axiom (concl p) then ()
    if (rule_kind o refinement) p = `SEQUENCE` & is_identity_seq p then
      (aux o hd o children) p
    if (rule_kind o refinement) p = `SEQUENCE` 
        & not (no_equal_subterms o concl o hd o children) p 
      then add_questionable_subproof p
    else
      ( ( let k = rule_kind (refinement p)  in
          if k = `DIRECT-COMP` then 
            (add_additional_subgoal p ;
             if not is_ok_direct_comp p then add_questionable_subproof p )
          if k = `SEQUENCE` then add_additional_subgoal p 
          if k = `EXPLICIT-INTRO` or k = `FUNCTION-ELIM` then
            (if not (have_ok_concls (children p)) then add_questionable_subproof p)
          if k = `TACTIC` then aux (subproof_of_tactic_rule (refinement p))
          if k = `BECAUSE` or is_ok_rule (refinement p) then ()
          else add_questionable_subproof p
        )
        ; 
        (if rule_kind (refinement p) = `DIRECT-COMP` then (aux (skip_ok_direct_comps p); ())
         if is_refined p then (map aux (children p); ())
        )
      ) in
  map (\p. if not is_ok_concl_term (concl p) then add_questionable_subproof p; aux p)
      pfs         
;;

