let InstantiateHyp i term_list p =

  (	letrec make_instance ids_so_far t =
		( if is_not_term t then fail ;
		  let x,A,B = destruct_function t	in
		  if x = `NIL` then make_instance ids_so_far B
		  else make_instance (x.ids_so_far) B
		)
		?
		substitute t 
		   ((map (\x. make_var_term x)
			 (rev ids_so_far)) com term_list)  in

	Seq [make_instance [] (type_of_hyp i p)]
	THENL
	[RepeatAtomicNotFunctionElim i term_list []
	;Idtac
 	]
  ) p
;;



let ref t p = refine_using_prl_rule t p ;; 









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
	       THEN (ApplyToLastHyp (\i. RepeatFunctionElim i instantiation_terms []))
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
	       THEN (ApplyToLastHyp (\i. RepeatFunctionElim i instantiation_terms []))
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
  	      ;RepeatFunctionElimFor (n+1) (length hyps) [] []
		THEN IfThenOnConcl is_squash_term SquashIntro 
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
	let type = compute T	in	

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
	(\p. if	(let (t'.()),() = destruct_equal (concl p) in
		 let t = fst (no_extraction_compute t')  in	
		 not is_macro_term t'
		 & 
		 ( is_list_induction_term t 
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


let Autotactic =

   Repeat
	( Trivial
	  ORELSE
	  Member
 	  ORELSE
	  Arith
	)
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






let ExposeProperties hyps =
	
	% For variables declared to be in a set type %
	let Aux i p =

		let xtok = id_of_hyp i p	in
		let x = make_var_term xtok	in
		let properties =
		       	let x',A,B = destruct_set (compute (type_of_hyp i p))	in
			let B = if xtok=x' then B
			        else substitute B [make_var_term x',x]	in
			make_product_term `NIL` (make_equal_term A [x]) B	in

	     (	Seq [make_squash_term properties]
		THENL
		[Refine (explicit_intro make_axiom_term)
		 THEN Elim i THENW (MemberIntro THEN Try Intro)
		;ApplyToLastHyp SquashElim 
		 THENW ApplyToLastHyp RepeatAndElim
		]
	     )
	     p						in

	% For hypotheses of the form t in {..} %
	let Aux' i p = 
	    (	let H = type_of_hyp i p	in
		let [t],T = destruct_equal H	in
 		let set = compute T 	in
		let x,A,B = destruct_set set	in
		let seq_term =
			% all x:{x:A|B}. squash(B & x in A) %
			let eq_term = make_equal_term A [make_var_term x]	in
			make_function_term x set (make_squash_term
						    (make_and_term B eq_term))	in
		
		Seq [seq_term]
		THENL
		[Intro 
		THENW (Refine (explicit_intro make_axiom_term)
		       THEN ApplyToLastHyp Elim 
		       THENW (MemberIntro THEN Try Intro))
		;ApplyToLastHyp (\i. ElimOn i t)
		 THEN Try (ApplyToLastHyp SquashElim 
		           THENW (Thinning [number_of_hyps p + 1]
				  THEN ApplyToLastHyp RepeatAndElim))
		]
 	    ) p						in

	let Both x = Aux x ORELSE Aux' x		in

	Both (hd hyps) 
	THEN
	ForAllArgs (\x. Autotactic THEN Both x) (tl hyps)

;;	


let Same = SequenceOnSameConcl ;; 
