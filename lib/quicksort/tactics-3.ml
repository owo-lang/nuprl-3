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






let Contradiction =
	Seq [make_void_term]
	THENL
	[Try Backchain; ApplyToLastHyp Elim]
;;





let ListUnrollNew i h t p =

  (	let type = type_of_hyp i p	in
	if not is_list_term (fast_ap compute type) then failwith
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
	; FastAp
	  ( ApplyToLastHyp (\i. RepeatFunctionElimFor i 2 [l_var])
	    THEN
	    Trivial
	  )
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
			let pattern =
				if is_squash_term Ai then 
					(t where (),(),t = destruct_set Ai)
				else Ai			in
			let ids' = if xi=`NIL` then ids else xi.ids	in
			aux ids' t' (tl hyps)
				(combine_alists	(match pattern (hd hyps) ids) alist)
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
	RepeatAtomicNotFunctionElim (number_of_hyps p + 1) inst_list
	THEN
	Thinning [(number_of_hyps p + 1)]
  
  )
  p

;;




letrec ForAllArgs (T: *->tactic) (args: * list) p =
	if null args then Idtac p
	else ( T (hd args) THEN ForAllArgs T (tl args) ) p
;;


let number_of_new_hyps p p' = number_of_hyps p' - number_of_hyps p ;;



letrec UglyRepeatSetElim i p =
	if is_set_term (fast_ap compute (type_of_hyp i p)) then
	     (Elim i THENW UglyRepeatSetElim (number_of_hyps p + 1)) p 
 
	else Idtac p 
;;




let Complete = COMPLETE ;; 



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


