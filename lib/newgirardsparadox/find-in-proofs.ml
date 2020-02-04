%-*- Tab-Width: 2; Fonts: TVFONT -*-%

let find_in_proofs pred pfs =
	letref ps = pfs in
	letref pf = void_goal_proof in
	letrec aux p = if pred p then (pf:=p; failwith `found`) if not is_refined p then () else (map aux (children p);())	in
(	if null ps then failwith `not found`
	loop (aux (hd ps); ps:= tl ps; ())
)
?\id (if id = `found` then `found`, pf, (hd ps) else `not found`, pf, hd ps)
;; 

letrec number_of_leaves pf =
	letref count = 0 in
	if not is_refined pf then (count:= count+1; ())
	else (map number_of_leaves (children pf); ())
	;
	count
;;


let count_maximal_membership_subtrees pfs =
	letref ps = pfs in
	letref count = 0 in
	letrec aux p = 
		if is_membership_goal p & ( (Trivial p;true) ? false ) then ()
		if is_membership_goal p then (count:= (count + 1) - (number_of_leaves p);())
		if not is_refined p then ()
		if (rule_kind o refinement) p = `TACTIC` then (%aux (subproof_of_tactic_rule (refinement p));% map aux (children p); ())
		else (map aux (children p);())	in
(	if null ps then ()
	loop (aux (hd ps); ps:= tl ps; ())
);
count
;; 

