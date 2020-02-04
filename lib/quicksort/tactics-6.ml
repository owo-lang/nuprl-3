
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

let firstn n l =
  if n<0 then failwith `firstn: n must be nonnegative.` ;
  letrec aux n l = if n=0 then [] else hd l . aux (n-1) (tl l)   in
  aux n l ? failwith `firstn: n too large.`
;;

letrec nthcdr n l = 
   if n=0 then l else nthcdr (n-1) (tl l)
;;


% (*->**->*) -> * -> (** list) -> * %
let accumulate f init_val l =
   letrec aux l =
      if null l then init_val 
      else let h.t = l  in f (aux t) h    in
   aux (rev l)
;;



letrec restore_def_refs t =
   ( let h.l = decompose_application t in
     let def_name = 
      implode (remove_last (explode (destruct_term_of_theorem h)))  in
     let num_args = length (rhs_formal_occurrences_of_def def_name)  in
     let l' = map restore_def_refs l   in
     accumulate make_apply_term
                (instantiate_def def_name (permute_args_for_def_instantiation def_name (firstn num_args l')))
                (nthcdr num_args l')
   )
   ? map_on_subterms restore_def_refs t
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



let RedefConcl p =
  (Seq [restore_def_refs (concl p)] 
   THENL [Idtac; Refine (hyp (number_of_hyps p + 1))]
  ) p
;;

let RedefHyp i p =
   if not id_of_hyp i p = `NIL`  then failwith `can't redef a tagged hyp.` ;
  (   Seq [restore_def_refs (type_of_hyp i p)] 
      THENL [Refine (hyp i); Thinning [i]]
  ) p
;;


let OnEveryHyp T p =                                                           
  ChainHypTactics                                                              
    (map T (rev (upto 1 (number_of_hyps p))))                                  
    p                                                                          
;;                                                                             
                                                                               


let Redef = 
   OnEveryHyp (\i. Try (RedefHyp i)) THEN (RedefConcl THEN Try Hypothesis) ;; 




let ModifyConcl f p =
   (SubstConcl (f (concl p)) THEN RedefConcl)
   p
;;

let ModifyHyp f i p =
   (SubstHyp i (f (type_of_hyp i p))
    THENL [ApplyToLastHyp RedefHyp; RedefConcl]
   ) p
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


