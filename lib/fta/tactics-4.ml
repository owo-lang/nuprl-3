	
let InstantiateHyp i term_list p =

  (	letrec make_instance ids_so_far t =
		( let x,A,B = destruct_function t	in
		  if x = `NIL` then fail
		  else make_instance (x.ids_so_far) B
		)
		?
		substitute t 
		   ((map (\x. make_var_term x)
			 (rev ids_so_far)) com term_list)  in

	Seq [make_instance [] (type_of_hyp i p)]
	THENL
	[RepeatFunctionElimFor i (length term_list) term_list
	;Idtac
 	]
  ) p
;;



let ref t p = refine_using_prl_rule t p ;; 


let SetElementIntro p =
  (     ComputeConclType 
	THEN
	(refine_using_prl_rule ($^ (`intro new `) (undeclared_id p `x`)))
  ) p
;;
 








let get_ids_equands_and_type t =
	letrec aux t ids_so_far =
		( let x,(),B = destruct_function t	in
		  aux B (if x=`NIL` then ids_so_far 
						    else x.ids_so_far)
		)
		?
		rev ids_so_far, destruct_equal t	in
	aux t []
;;



let RewriteConclWithLemmaOver name over_id over_term p =
	
  (	let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
	let instance = lookup (match over_term 	(concl p) [over_id]) over_id	in
	let instantiation_terms = 
		map (lookup (match e instance ids)) ids		in
	let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
	let replacement = substitute e' subst_list	in
	let type_inst = substitute T subst_list		in
	
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
		failwith `get_contained_instance`		in
	try_on_each_member (subterms term)
;;


let RewriteConclWithLemma name p =
	let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
	let over_id = undeclared_id p `z`	in
	let over_term = 
		replace_subterm
			(get_contained_instance (concl p) e ids)
			(make_var_term over_id)
			(concl p)			in
	RewriteConclWithLemmaOver name over_id over_term p
;;


let RewriteConclWithRevLemmaOver name over_id over_term p =
	
  (	let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
	let instance = lookup (match over_term 	(concl p) [over_id]) over_id	in
	let instantiation_terms = 
		map (lookup (match e' instance ids)) ids		in
	let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
	let replacement = substitute e subst_list	in
	let type_inst = substitute T subst_list		in
	
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
	let over_id = undeclared_id p `z`	in
	let over_term = 
		replace_subterm
			(get_contained_instance (concl p) e' ids)
			(make_var_term over_id)
			(concl p)			in
	RewriteConclWithRevLemmaOver name over_id over_term p
;;


letrec restore_def_refs t =
	( let h.l = decompose_application t	in
	  let def_name = 
		implode (remove_last (explode (destruct_term_of_theorem h)))  in
	  instantiate_def def_name (map restore_def_refs l)
	)
	? map_on_subterms restore_def_refs t
;;


let RestoreDefRefsInConcl p =
  (	Seq [restore_def_refs (concl p)] 
	THENL [Idtac; Refine (hyp (number_of_hyps p + 1))]
  ) p
;;

let RestoreDefRefsInHyp i p =
  (	Seq [restore_def_refs (type_of_hyp i p)] 
	THENL [Refine (hyp i); Thinning [i]]
  ) p
;;



ml_curried_infix `THENO` ;;   

let $THENO T T' p =
	let c = concl p in
	(T THEN (\p. if concl p = c then Idtac p else T' p)) p
;;  

   
let SquashAndBringHyps hyps p =
  (	let squashed_hyps = map (\i. make_squash_term (type_of_hyp i p)) hyps	in
	letrec make_seq_term l =
		(let h.t = l in make_implies_term h (make_seq_term t))
		? (concl p)	in
	let n = number_of_hyps p 	in
	Seq [make_seq_term squashed_hyps]
  	THENL [Thinning hyps
  	      ;RepeatFunctionElimFor (n+1) (length hyps) []
		THEN Thinning [n+1]
	      ]
  ) p
;;


let SequenceOnSameConcl T_list p =

	let c = concl p 	in

	letrec Aux T_list p =
		( if concl p = c then (hd T_list THEN Try (Aux (tl T_list))) p
		  else Idtac p
		) 					in

	Aux T_list p
;;











let RewriteHypWithLemmaOver i name over_id over_term p =
	
  (	let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
	let instance = lookup (match over_term 	(type_of_hyp i p) [over_id]) over_id	in
	let instantiation_terms = 
		map (lookup (match e instance ids)) ids		in
	let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
	let replacement = substitute e' subst_list	in
	let type_inst = substitute T subst_list		in
	
	Seq [substitute over_term [make_var_term over_id, replacement]]
    	THENL  [RewriteConclWithRevLemmaOver name over_id over_term
	       ;Idtac
	       ]
  ) p 

;;




let RewriteHypWithLemma i name p =
	let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
	let over_id = undeclared_id p `z`	in
	let over_term = 
		replace_subterm
			(get_contained_instance (type_of_hyp i p) e ids)
			(make_var_term over_id)
			(type_of_hyp i p)			in
	RewriteHypWithLemmaOver i name over_id over_term p
;;




let SubstForInHyp i eq_term p =
  (	
	let [e;e'],T = destruct_equal eq_term	
 	and H = type_of_hyp i p		in
	let over_id = undeclared_id p `z`  	in
 	let over_term = replace_subterm e (make_var_term over_id) H	in

	Seq [substitute over_term [make_var_term over_id, e']]
     	THENL [Refine (substitution big_U (make_equal_term T [e';e])
			over_id over_term)
 	      ;Idtac
	      ]
  ) p
;;



