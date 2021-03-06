%
********************************************************************************
********************************************************************************
********************************************************************************

   tactics-3

********************************************************************************
********************************************************************************
********************************************************************************
%

let SubstOver in_term ztok B p =
	let [b],A = destruct_equal in_term	in
	let a = lookup (match B (concl p) [ztok]) ztok	in
	Refine (substitution big_U (make_equal_term A [a;b]) ztok B) p
;;


let SubstFor equality_term p =
	let [a;()],() = destruct_equal equality_term	in
	let ztok = undeclared_id p `z`		in
	let B = replace_subterm a (make_var_term ztok) (concl p)	in
	Refine (substitution big_U equality_term ztok B) p
;;




let ExpandDefsInConcl name_list =
	ComputeConclUsing (tag_named_defined_terms name_list)
;;

let ExpandDefsInHyp name_list  =
	ComputeHypUsing (tag_named_defined_terms name_list) 
;;

let ExpandDefsInHyps name_list hyp_list =
	iterate_fun 
		(\T T'. T THEN T') 
		(map (ExpandDefsInHyp name_list) hyp_list) 
;;


let ExpandDefs name_list =
	ExpandDefsInConcl name_list
	THEN
	ForEachHypFrom (ExpandDefsInHyp name_list) 1
;;


let NormalizeConcl =
   	ComputeConclUsing tag_all_legal_subterms 
;;


let NormalizeHyp i p =
   	ComputeHypUsing tag_all_legal_subterms i p
;;



let NormalizeHyps hyp_list =
	iterate_fun 
		(\T T'. T THEN T') 
		(map (\i. NormalizeHyp i) hyp_list) 

;;

let Normalize =
	NormalizeConcl
	THEN
	ForEachHypFrom NormalizeHyp 1
;;
	

let TopLevelComputeConcl =
	ComputeConclUsing tag_for_top_level_compute
;;

let TopLevelComputeHyp =
	ComputeHypUsing tag_for_top_level_compute
;;

let TopLevelComputeHyps hyp_list =
	iterate_fun 
		(\T T'. T THEN T') 
		(map (\i. TopLevelComputeHyp i) hyp_list) 

;;

let TopLevelCompute =
	TopLevelComputeConcl
	THEN
	ForEachHypFrom TopLevelComputeHyp 1
;;



%  "Abs" as a prefix below indicates that the computations stop
   short of substituting extracted terms for term_of terms.
%



let AbsSweepReduceConcl =
	ComputeConclUsing tag_for_abs_sweep_reduce
;;

let AbsSweepReduceHyp =
	ComputeHypUsing tag_for_abs_sweep_reduce
;;

let AbsSweepReduceHyps hyp_list =
	iterate_fun 
		(\T T'. T THEN T') 
		(map (\i. AbsSweepReduceHyp i) hyp_list) 
;;

let AbsSweepReduce =
	AbsSweepReduceConcl
	THEN
	ForEachHypFrom AbsSweepReduceHyp 1
;;






letrec AbsNormalizeConcl p =
  (	AbsSweepReduceConcl 
	THEN
	(\ p' . if concl p = concl p' then Idtac p' else AbsNormalizeConcl p')
  ) 
  p
;;

letrec AbsNormalizeHyp i p =
  (	AbsSweepReduceHyp i 
	THEN
	(\ p' . if type_of_hyp i p = type_of_hyp i p' then Idtac p'
		else AbsNormalizeHyp i p')
  )
  p
;;

let AbsNormalizeHyps hyp_list =
	iterate_fun 
		(\T T'. T THEN T') 
		(map (\i. AbsNormalizeHyp i) hyp_list) 
;;

let AbsNormalize =
	AbsNormalizeConcl 
	THEN
	ForEachHypFrom AbsNormalizeHyp 1
;;





let Member = REPEAT (\p. if (is_list_induction_term t 
			     or
			     is_integer_induction_term t
			     or 
			     is_rec_ind_term t
			     where t = fst (no_extraction_compute t')
			     where (t'.()),() = destruct_equal (concl p)
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


let set () = set_auto_tactic `refine (tactic \`Autotactic\`)` ;;

let unset () = set_auto_tactic `Idtac` ;;

set () ;;



let Contradiction =
	Seq [make_void_term]
	THENL
	[Try Backchain; ApplyToLastHyp Elim]
;;





let ListUnrollNew i h t p =

  (	let type = type_of_hyp i p	in
	if not is_list_term (compute type) then failwith
		`ListUnroll: hyp. must compute to a list type` ;
	let l = id_of_hyp i p 	in
	let l' = undeclared_id p `l`	in
	let l_var, l'_var = make_var_term l, make_var_term l'	in
	let seq_term =
		% all l':type. (l=l' in type) => T[l'/l] %
		make_function_term l' type
			(make_implies_term
				(make_equal_term type [l_var; l'_var])
				(substitute (concl p) [l_var, l'_var]) )	in

	Seq [seq_term]
	THENL
	[ Intro
	  THENL
	  [ ApplyToLastHyp ComputeHypType
	    THEN
	    ApplyToLastHyp (\i. Refine (list_elim i `NIL` h t))
	    THENL
	    [Intro; ApplyToLastHyp (\i. Thinning [i]) THEN Intro]
	    THEN
	    Thinning [number_of_hyps p + 1]
	  ;Idtac
	  ]
	; ApplyToLastHyp (\i. RepeatFunctionElimFor i 2 [l_var])
	  THEN
	  Trivial
	]
  )
  p
;;


let ListUnroll i p =
	ListUnrollNew i (undeclared_id p `h`) (undeclared_id p `t`) p
;;





let LemmaFromHyps name hyps terms p =

  (	letrec combine_alists l l' =
		if null l then l'
		if null l' then l	
		else (let (x,t).l'' = l in
		      if (lookup l' x) = t then (combine_alists l'' l')
		      else failwith `die`
		      ?? [`die`] fail
		      ?  (x,t).(combine_alists l'' l') )	in
		
	letrec aux
		ids % = [x(i-1);...;x1] %
		t % = xi:Ai->...->xn:An->B %
		hyps % remaining to be matched %
		alist % bindings produced from matches so far %
		=
		if null hyps & length alist + length terms + 1 > length ids then
			alist, rev ids
		if null hyps then fail
		else
			let xi,Ai,t' = destruct_function t	in
			let ids' = if xi=`NIL` then ids else xi.ids	in
			aux ids' t' (tl hyps)
				(combine_alists	(match Ai (hd hyps) ids) alist)
			?
			aux ids' t' hyps alist			in

	
	let inst_list =
		let match_bindings, xi_list =
			aux
			  []
			  (main_goal_of_theorem name)
			  (map (\i. type_of_hyp i p) hyps)
			  []					in
		letref term_list = terms in
		let inst_list_prefix =
			map 
			   (\xi. lookup match_bindings xi
				 ?
				 let h.rest = term_list in
				 term_list := rest ;
				 h) 
			   xi_list				in
		inst_list_prefix @ term_list			in

	Refine (lemma name `nil`)
	THEN
	RepeatFunctionElim (number_of_hyps p + 1) inst_list
	THEN
	Thinning [(number_of_hyps p + 1)]
  
  )
  p

;;



letrec RepeatFor n T p =

 	Try
	  ( if n>0 then T THEN RepeatFor (n-1) T
		   else Idtac
	  )
	  p
;;


letrec ForAllArgs (T: *->tactic) (args: * list) p =
	if null args then Idtac p
	else ( T (hd args) THEN ForAllArgs T (tl args) ) p
;;


let number_of_new_hyps p p' = number_of_hyps p' - number_of_hyps p ;;



letrec UglyRepeatSetElim i p =
	if is_set_term (compute (type_of_hyp i p)) then
	     (Elim i THENW UglyRepeatSetElim (number_of_hyps p + 1)) p 
 
	else Idtac p 
;;




let Complete = COMPLETE ;; 

let is_squash_term t =
	(let x,A,B = destruct_set t in
	 x=`NIL` & is_equal_term A
	)
	?
	false
;;


let SquashElim i p =
	if not is_squash_term (compute (type_of_hyp i p)) then
		failwith `SquashElim` ;
	(Elim i THEN ApplyToNthLastHyp 2 (\j. Thinning [i;j]) ) p
;; 


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




let ComputeSomeEquands nums p =
	let equands,T = destruct_equal (concl p)    in
	Refine
	   (direct_computation
	      (make_equal_term
		  T
	          (map (\t,n. if member n nums then make_tagged_term 0 t else t)
		       (equands com (upto 1 (length equands))))))
           p
;;

let ReduceDecisionTerm equand_num case =

	ComputeSomeEquands [equand_num]
        THEN
        (\p.
	  let t = select equand_num (fst (destruct_equal (concl p)))   in
	  if is_int_eq_term t then Refine (int_eq_computation equand_num case) p
	  if is_atom_eq_term t then Refine (atom_eq_computation equand_num case) p 
	  if is_intless_term t then Refine (int_less_computation equand_num case) p
	  else fail
	)
;;





% Will not always work, since try_to_replace_subterm doesn't. %
let AddDefInstancesToConcl instances p =
  (	letrec aux instances t =
		try_to_replace_subterm (aux (tl instances) t)
				       (compute (hd instances))
				       (hd instances)
		?
		t			in
	Seq [aux instances (concl p)]
	THENL [Idtac; ApplyToLastHyp NormalizeHyp 
		      THEN NormalizeConcl 
		      THEN Hypothesis]
  ) p
;;


