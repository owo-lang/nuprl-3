%
********************************************************************************
********************************************************************************
********************************************************************************

   term-1

********************************************************************************
********************************************************************************
********************************************************************************
%








let first l = select 1 l ;;
let second l = select 2 l ;;
let third l = select 3 l ;;
let fourth l = select 4 l ;;
let fifth l = select 5 l ;;

let concl = conclusion ;;

let l t = loadt (`Mrbig:>howe>=nml>`^t) ;;

let c t = compilet (`Mrbig:>howe>=nml>`^t) ;;



%
***************************************************************************

The following are the names of some useful functions which are implemented
in Lisp.  

>nuprl>ml>ml-term:  
	main_goal_of_theorem: tok -> term.
	extracted_term_of_theorem: tok -> term.
	map_on_subterms: (term -> term) -> term.  Replaces the immediate 
			subterms of a term with the result of applying the
			function argument. 
        list_subterms: term -> term list
	free_vars: term -> term list
	remove_illegal_tags: term -> term.  Remove all the tags that the
			direct computation rule wouldn't like.
	member_of_tok_list: tok -> tok list -> bool.  Lifted memq.
	do_computations: term -> term.  Do the computations indicated by tags.
	compute:  term -> term.  \t. do_computations '[[*;,t]]'
	no_extraction_compute: as compute, except that term_of terms will not
			be replaced by extracted terms.
	set_snapshot_file:  tok -> void. 
	reset_snapshot_file: void -> void.  Restore the snapshot file to the
			default.  ("mrbig:>snapshot.lisp").

>nuprl>ml>ml-refine: 
	top_def_of_term:  term -> tok.
	arity_of_def: tok -> int.  Number of distinct formal parameters in the
			named DEF object.
	instantiate_def: tok -> term list -> term.  May give strange results
			when defs are not fully parenthesized.

>howe>=nml>ml-primitives
	lib: tok -> tok list.  Give all library object names of which the
			given name is a prefix.
	library:  void -> tok list.  List the names of all objects in the
			library.
	object_kind: tok -> tok.
	rename_object: tok -> tok -> void.  First tok it the name of the object
			to rename.
	eval_term:  term -> term.  Run the evaluator on the term.
    	make_eval_binding: tok -> term -> term.  Create a binding in the eval
			subsystem, just as in doing "E>let x=...".

***************************************************************************
%





% Variables, term_of terms, and any(.) terms are neither canonical or 
  non-canonical.  Unary minus is regarded as a non-canonical term, although
  -n, for n a non-negative canonical integer, is not regarded as a redex.
%




let is_canonical_nontype t =

  member_of_tok_list (term_kind t)
    [`TOKEN`; `NATURAL-NUMBER`; `AXIOM`; `NIL`; `CONS`; `INL`;
     `INR`; `LAMBDA`; `PAIR`]
;;



let is_canonical_type t =

  member_of_tok_list (term_kind t)
    [`UNIVERSE`; `VOID`; `ATOM`; `INT`; `LIST`; `UNION`; `PRODUCT`;
     `FUNCTION`; `QUOTIENT`; `SET`; `EQUAL`; `LESS`; `RECURSIVE`]
;;



let is_canonical_term t = is_canonical_nontype t or is_canonical_type t
;;



let is_noncanonical_term t = 
  member_of_tok_list (term_kind t)
    [`INTEGER-INDUCTION`; `LIST-INDUCTION`; `DECIDE`; `SPREAD`;
     `APPLY`; `ATOMEQ`; `INTEQ`; `INTLESS` ; 
     `MINUS`; `ADDITION`; `SUBTRACTION`; `MULTIPLICATION`; 
     `DIVISION`; `MODULO`; `REC-IND` ]
;;




% t is a kind of term to which it is sometimes possible to apply
  at least one computation step and end up with a canonical type.
%
%let might_compute_to_type t =
  member_of_tok_list (term_kind t)
    [`INTEGER-INDUCTION`; `LIST-INDUCTION`; `DECIDE`; `SPREAD`;
     `APPLY`; `ATOMEQ`; `INTEQ`; `INTLESS` ; `REC-IND` ]
;;%



% Doesn't include decide. %
let is_decision_term t = 
  member_of_tok_list (term_kind t) [`ATOMEQ`; `INTEQ`; `INTLESS`]
;;




letref big_U = 17;;



let is_int_exp t = 
  member_of_tok_list (term_kind t) 
    [ `NATURAL-NUMBER`; `MINUS`; `ADDITION`; 
      `SUBTRACTION`; `MULTIPLICATION`; `DIVISION`; `MODULO` ]
;;



let is_wf_goal proof = 

       (let t.rest, T = destruct_equal (concl proof)  in
	is_universe_term T
	&
	(null rest or null (filter (\x. not x=t) rest))
       )
       ?
       false
;;


let is_membership_goal p =
       (let t.rest, T = destruct_equal (concl p)  in
	(null rest or null (filter (\x. not x=t) rest))
       )
       ?
       false
;;



let not_is_wf_goal proof = not is_wf_goal proof ;;


% :term->proof->int.  If the term is a variable,
  return the position of its declaration
  in the hypothesis list of the  proof 
%

let find_declaration id proof =
  find_position
    id
    (map id_of_declaration (hypotheses proof))
;;


let number_of_hyps proof = length (hypotheses proof)
;;


% (int#*) list -> * list.  Construct a list of * from l using the integers
  as repetition factors.
%
letrec build_list l =
	letrec ncons n x l = if n<1 then l else x.(ncons (n-1) x l)  in
	(let (n,x).tl = l  in  ncons n x (build_list tl))
	?
	[]
;;




let id_of_hyp i proof = 
  id_of_declaration (select i (hypotheses proof))
  ?
  failwith `hyp. number out of range`
;;


let type_of_hyp i proof = 
  type_of_declaration (select i (hypotheses proof))
  ?
  failwith `hyp. number out of range`
;;



let destruct_hyp i proof =
  destruct_declaration (select i (hypotheses proof))
  ?
  failwith `hyp. number out of range`
;;







let map_on_equality_type f T =
   let equands,T = destruct_equal T  in
   make_equal_term (f T) equands
;;




% On H >> T: if T is t1=...=tn in T' then T' else T %
let concl_type proof =
	let A = concl proof  in
	(snd (destruct_equal A)) ? A
;;


let hyp_type i p =
	let A = type_of_hyp i p in
	(snd (destruct_equal A)) ? A
;;





let update a_list updates = updates @ a_list ;;

let lookup a_list x = snd (assoc x a_list) ;;








let term_of_term_of_theorem t =
	extracted_term_of_theorem (destruct_term_of_theorem t)
;;



let type_of_term_of_theorem t =
	main_goal_of_theorem (destruct_term_of_theorem t)
;;





% :term->term list.   Let x1(x2)...(xn) be a breakdown of t maximal for its 
  form.  Return [x1;x2;...;xn].   %

let decompose_application t =

	letrec aux fun args =
	       (let f,a = destruct_apply fun in
		aux f (a . args)
	       )
	       ?
	       fun . args
	in
	aux t []
;;






% return x1 (see comment on decompose_application)
%
letrec head_of_application t =

  (head_of_application (fst (destruct_apply t)))  ?  t

;;




letrec arity_of_application t =

  (arity_of_application (fst (destruct_apply t)) + 1)  ?  0

;;


% Try to map f on each element of the list, failing if f did not
  succeed at least once.
%
let map_on_some f l =
  	letrec do_it l =
		null l => [],false | let l',b = do_it (tl l) 
				     and a = hd l  in
				     ((f a).l', true) ? (a.l', b)
   	in
  	let res, b = do_it l  in
	b => res | failwith `map_on_some: no successful applications`
;;



% Arg. must be a term_of term.  Find the explicit lambda-arity of the
  extracted term.
%
let arity_of_extraction t =

   letrec lambda_count t =
      (lambda_count (snd (destruct_lambda t)) + 1)  ?  0   in
   lambda_count (extracted_term_of_theorem (destruct_term_of_theorem t))

;;

			


let is_term_of_with_args t =

   is_term_of_theorem_term (head_of_application t)

;;



%  A "defined term" is a term_of of term applied to a number of arguments
   which is equal to the arity of the extracted term.
%
let is_defined_term t =
   let a = head_of_application t  in
   arity_of_extraction a = arity_of_application t
   ?
   false
;;


%  Tag for direct computation: [[n+1;t]] where n is the arity.  ("+1" is because
   the extraction counts as one step.)
%
let tag_defined_term t = 
   let a = head_of_application t  in  
   let n = arity_of_extraction a  in
   let m = arity_of_application t in
   m = n  =>  make_tagged_term (n+1) t  |  failwith `tag_defined_term`
;;






%  A few list operations follow.
%



letrec remove_last l =
	(let x.l' = l in if null l' then [] else x . (remove_last l'))
	?
	failwith `remove_last`
;;

letrec last l = 
	(let x.l' = l in if null l' then x else last l')
	?
	failwith `last`
;;




% :(*->*->*)->* list->*.  [x1;...;xn] ---> f(...(f(f x1 x2)(x3))....)xn 
  for n>1, [x] ---> x, [] ---> failure. 
%
let iterate_fun f args =
  letrec aux accumulation args =
    (let (x.l) = args in aux (f accumulation x) l)
    ?
    accumulation  in
  if null args then failwith `iterate_fun`
  if length args = 1 then hd args
  else aux (hd args) (tl args)
;;



% :(*->*->*)->* list->*.  [x1;...;xn] ---> f x1 (f x2 (... (f x(n-1) xn)...)
  for n>1, [x] ---> x, [] ---> failure.
%
let reverse_iterate_fun f args =

  letrec aux args =
	(let [x;y] = args in f x y)
	?
	(let (x.l) = args in f x (aux l))  in
  if null args then failwith `reverse_iterate_fun`
  if length args = 1 then hd args
  else aux args
;;









% :term->term->term.  Inefficiently replace all occurrences of u by v in t. %
letrec replace_subterm u v t =
  if u=t 
    then v
    else map_on_subterms (replace_subterm u v) t 
;;  







% :term->bool %
let is_integer_term t = 
  is_natural_number_term t 
  or ( is_minus_term t & is_natural_number_term (destruct_minus t) )
;;

% :term->int %
let destruct_integer t =
  if is_minus_term t
    then (-destruct_natural_number (destruct_minus t))
    else destruct_natural_number t
  ? failwith `destruct_integer`
;;


% :int->term %
let make_integer_term n =
  if n<0
    then make_minus_term (make_natural_number_term (-n))
    else make_natural_number_term n
;;

let make_some_term (var:tok) type prop  =
	let l = [make_var_term var; type; prop]  in
	instantiate_def `some` l
	?
	instantiate_def `exists` l
	?
	make_product_term var type prop
;;


let make_some_where_term (var:tok) type prop  =
	let l = [make_var_term var; type; prop]  in
	instantiate_def `some_where` l
	?
	instantiate_def `exists_where` l
	?
	make_set_term var type prop
;;


let make_all_term (var:tok) type prop =
	let l = [make_var_term var; type; prop]  in
	instantiate_def `all` l
	?
	make_function_term var type prop
;;



let is_and_term t =
  (let x,(),() = destruct_product t in x=`NIL`) ? false
;;

let destruct_and t =
  (let x,p = destruct_product t in 
   if x=`NIL` then p else fail
  )
  ?
  failwith `destruct_and`
;;

let make_and_term s t =
	instantiate_def `and` [s;t]
	?
	make_product_term `NIL` s t
;;



let is_or_term t =
	is_union_term t 
;;

let destruct_or t =
	destruct_union t ? failwith `destruct_or`
;;

let make_or_term s t =
	instantiate_def `or` [s;t]
	?
	make_union_term s t
;;





let is_implies_term t =
  	(let x,(),() = destruct_function t in x=`NIL`) ? false
;;

let destruct_implies t =
  (let x,p = destruct_function t in 
   if x=`NIL` then p else fail
  )
  ?
  failwith `destruct_implies`
;;

let make_implies_term s t =
	instantiate_def `imp` [s;t]
	?
	instantiate_def `implies` [s;t]
	?
	make_function_term `NIL` s t
;;




let make_not_term t =
	instantiate_def `not` [t]
	?
	make_implies_term t make_void_term
;;

let is_not_term t =
	(is_void_term (snd (destruct_implies t)))
	?
	false
;;

let destruct_not t =
	( let a,b = destruct_implies t in 
	  if not (is_void_term b) then fail else a)	
	?
	failwith `destruct_not`
;;



let make_disjunction term_list =

	reverse_iterate_fun make_or_term term_list  
	? 
	failwith `make_disjunction`
;;

let destruct_disjunction t =
	letrec Aux t accum =
		( let a,b = destruct_or t in
		  Aux a (Aux b accum)
		)
		?
		t.accum		in
	Aux t []
;;



let make_conjunction term_list =

	reverse_iterate_fun make_and_term term_list  
	? 
	failwith `make_conjunction`
;;

let destruct_conjunction t =
	letrec Aux t accum =
		( let a,b = destruct_and t in
		  Aux a (Aux b accum)
		)
		?
		t.accum		in
	Aux t []
;;




let make_implication term_list =

	reverse_iterate_fun make_implies_term term_list
	? 
	failwith `make_implication`
;;

letrec destruct_implication t =
	( let a,b = destruct_implies t in
	  a . (destruct_implication b)
	)
	?
	[t]
;;



let is_squash_term t =
	(let x,A,B = destruct_set t in
	 x=`NIL` & is_equal_term A
	)
	?
	false
;;


let make_squash_term t =
	instantiate_def `squash` [t]
	?
	make_set_term
		`NIL` 
		(make_equal_term
			make_int_term 
			[make_integer_term 0])
		t
;;



% term -> term list -> term list.  For t = x1:A1-> . . . -> xn:An -> B,
  where B is not a function term, and where some xi's may be nil, return
  the Ai with the xi instantiated from the term list.  The length of the
  term list must equal the number of non-nil xi.
%
letrec antecedants t inst_list =
	(let x,A,B = destruct_function t  in
	 if x = `NIL` then A . (antecedants B inst_list)
	 else let x = make_var_term x  in
	      let a.rest = inst_list  in
	      make_equal_term A [a]
	      .
	      antecedants (substitute B [x,a]) rest
	)
	?
	[]
;;






%  Following are some functions for a version of new_id, 
   called undeclared_id.
%
let number_suffixing_letter tok =
   int_of_tok (implode (tl (explode tok)))  ?  -1
;;


% Max over all the declared variables.
%
let max_number_suffixing_letter proof =
   list_max
	(0 . (map (number_suffixing_letter o id_of_declaration)
	           (hypotheses proof)))
;;



let undeclared_id proof letter = 
  if not new_id_initialized then
    (new_id_initialized := true;
     new_id_count := max_number_suffixing_letter proof;
     ());
  new_id_count := new_id_count + 1;
  implode (letter . explode (tok_of_int new_id_count))
  ?
  failwith `undeclared_id: tok arg must be a letter`
;;
 

let undeclared_id_using proof token = undeclared_id proof (hd (explode token))
;;








% Resulting bindings ((tok#term) list) are ordered %
let match_part
	(term_typer: term->term)
	(destructor: term -> term
		% takes a term and returns a term to which instance is to
    		  be matched. % )
	pattern_container  % a universally quantified formula %
	instance

	=

	letrec get_matrix_and_vars_with_types t =
		(let x,A,B = destruct_function t  in
		 let matrix, vars_with_types = get_matrix_and_vars_with_types B in
		 if x=`NIL` then fail
		 else matrix, ((x,A) . vars_with_types)
		)
		?
		t,[]		in

	let matrix, vars_with_types = get_matrix_and_vars_with_types pattern_container	in
	let vars = map (\x. fst x) vars_with_types	in

	let beat_on_conjunction conjunction =
		letrec beat_it conjunction =
			if is_and_term conjunction then
				(let A,B = destruct_and conjunction in
				 beat_it A ? beat_it B
				)
			else match conjunction instance vars	in
		if is_and_term instance then match conjunction instance vars
		else beat_it conjunction			in
	
	letrec get_bindings_from_types vars_with_types =
		(let (x,A).rest = vars_with_types	in
		 let alist = get_bindings_from_types rest	in
		 let vars = free_vars A		in
		 if null vars then alist
		 else (match A (term_typer (lookup alist x)) (map (\x. destruct_var x) vars))
		        @ alist
		      ? alist
		)
		? beat_on_conjunction (destructor matrix) in

	map (\x. assoc (fst x) (get_bindings_from_types  vars_with_types))
	     vars_with_types
	
;;






letrec member_of_membership_theorem_matrix t =
	member_of_membership_theorem_matrix (snd (destruct_implies t))
	?
	(let [t'],() = destruct_equal t  in  t')
;;

letrec type_of_membership_theorem t =
	type_of_membership_theorem (snd (snd (destruct_function t)))
	?
	(let [()],T = destruct_equal t  in  T)
;;
	

let substitute_using_bindings t (bindings: (tok#term) list) =
	substitute t (map (\x,t. make_var_term x, t) bindings)
;;




let is_macro_term t = 
	(let name = (implode (explode (top_def_of_term t) @ [`_`]))  in
	 status_of_object name = `COMPLETE`
	 & object_kind name = `THM` 
	 & not ((is_term_of_theorem_term t or is_apply_term t)
		& is_defined_term t)	 
	)
	?
	false
;;




let membership_theorem_of_macro_term t =
	implode (explode (top_def_of_term t) @ [`_`])
;;



% Guess type of t in context of pf, failing if unsuccessful 
%
let get_type pf t =

letrec g e t =

  if is_macro_term t then
	(let thm = main_goal_of_theorem (membership_theorem_of_macro_term t)  in
	 substitute_using_bindings
		(type_of_membership_theorem thm)
		(match_part (g e) member_of_membership_theorem_matrix thm t)
	)
    
  if is_token_term t then make_atom_term

  if is_any_term t then fail

  if is_int_exp t then make_int_term

  if term_kind t=`AXIOM` then fail
 
  if is_nil_term t then fail

  if is_cons_term t then (let a,b = destruct_cons t in 
        		  make_list_term (g e a) ? g e b)

  if is_inl_term t or is_inr_term t then fail

  if is_lambda_term t then fail

  if is_pair_term t then (let a,b = destruct_pair t in
			  make_product_term `nil` (g e a) (g e b))

  if is_integer_induction_term t 
    then (let (),(),t0,() = destruct_integer_induction t in g e t0)

  if is_list_induction_term t 
    then (let (),tnil,() = destruct_list_induction t in  g e tnil)

  if is_rec_ind_term t 
    then fail

  if is_decide_term t 
    then (let arg,b1,b2 = destruct_decide t in
 	  let [x_tok],t1 = destruct_bound_id b1  in
          let [y_tok],t2 = destruct_bound_id b2   in
	  let x,y = make_var_term x_tok, make_var_term y_tok  in
          let A,B = destruct_union (g e arg)  in
          g (update e [x,A]) t1 ? g (update e [y,B]) t2 )

  if is_spread_term t
    then (let arg,b = destruct_spread t  in
          let [x_tok;y_tok],t1 = destruct_bound_id b  in
          let x,y = make_var_term x_tok,make_var_term y_tok  in
          let z_tok,A,B = destruct_product (g e arg)  in
          if z_tok=`NIL`
            then g (update e [x,A;y,B]) t1
            else let z = make_var_term z_tok in
                 let fstof_arg = 
		   make_spread_term 
		     arg
		     (make_bound_id_term [`u`;`v`] (make_var_term `u`))  in
                 g (update e [ x, A; y, substitute B [z,fstof_arg] ]) t1 )

  if is_apply_term t 
    then (let a,b = destruct_apply t  in
          let z_tok,(),B = destruct_function (g e a)  in
          substitute B [make_var_term z_tok, b] )

  if is_var_term t then lookup e t

  if is_term_of_theorem_term t then type_of_term_of_theorem t

  if is_atom_eq_term t or is_int_eq_term t or is_intless_term t
    then (let [();();t1;t2] = list_subterms t in (g e t1) ? (g e t2))

  if is_atom_term t or is_void_term t or is_int_term t or is_less_term t
    then make_universe_term 1

  if is_universe_term t then make_universe_term ((destruct_universe t)+1)

  if is_list_term t then g e (destruct_list t)
 
  if is_equal_term t then g e (snd (destruct_equal t))

  if is_function_term t 
    then (let x_tok,A,B = destruct_function t  in
          let B_type = if x_tok=`NIL` 
		         then g e B 
			 else g (update e [make_var_term x_tok,A]) B  in
          make_universe_term 
            (max (destruct_universe (g e A)) (destruct_universe B_type))  )

  if is_product_term t 
    then (let x_tok,A,B = destruct_product t  in
          let B_type = if x_tok=`NIL` 
		         then g e B 
			 else g (update e [make_var_term x_tok,A]) B  in
          make_universe_term 
            (max (destruct_universe (g e A)) (destruct_universe B_type)) )

  if is_set_term t 
    then (let x_tok,A,B = destruct_set t  in
          let B_type = if x_tok=`NIL` 
		         then g e B 
			 else g (update e [make_var_term x_tok,A]) B  in
          make_universe_term 
            (max (destruct_universe (g e A)) (destruct_universe B_type))  )

  if is_union_term t 
    then (let A,B = destruct_union t in
          make_universe_term
            (max (destruct_universe (g e A)) (destruct_universe (g e B)))  )

  if is_quotient_term t 
    then (let x_tok,y_tok,A,E = destruct_quotient t  in
          let x,y = make_var_term x_tok,make_var_term y_tok  in
          make_universe_term
            (max (destruct_universe (g e A)) 
                 (destruct_universe (g (update e [x,A;y,A]) E)))  )

  if is_rec_term t 
    then (let T_list, bnd_term_list, (), Ti, a = destruct_rec t  in
	  let A = g e a  in
	  let Ti_param_list, Ti_term = destruct_bound_id
				         (select (find_position Ti T_list)
				        	 bnd_term_list)  in
	  let Ti_param = hd Ti_param_list  in
	  g 
	    (update 
	       e 
               [make_var_term Ti_param, A;
		make_var_term Ti, make_function_term `nil` A (make_universe_term 1)])
            Ti_term )

  else failwith `fallthru`

  in

  letrec initialize_env decl_list =
    if null decl_list 
    then []
    else let x_tok,A = destruct_declaration (hd decl_list) in
         if x_tok=`NIL` 
           then initialize_env (tl decl_list)
           else update 
		  (initialize_env (tl decl_list)) [make_var_term x_tok,A]

  in


  g (initialize_env (hypotheses pf)) t

  ?\id failwith `get_type;`^id

;;


let match_part_in_context destructor pattern_container instance p =
	match_part (get_type p) destructor pattern_container instance 
;;

letrec consequent t = 
	(let (),(),B = destruct_function t in consequent B) ? t
;;

letrec atomic_not_consequent t =
	(if is_not_term t then fail
	 ;let (),(),B = destruct_function t in atomic_not_consequent B
	) 
	? t
;;



let match_part_using s t term_list =

	letrec get_xi_list_and_B_term t =
		(let x,(),t' = destruct_function t  in
		 let xis,B_term = get_xi_list_and_B_term t'  in
		 if x=`NIL` then xis,B_term
		 else (x.xis),B_term
		)
		?
		[],t		in

	let xi_list,B_term = get_xi_list_and_B_term t  in
	
	letrec match_against_Bis Bis =
		(let x,B,B' = destruct_product Bis  in
		 if x=`NIL` then
			(match_against_Bis B  ?  match_against_Bis B')
		 else fail
		)
		?
		match Bis s xi_list	in

	let match_bindings = match_against_Bis B_term	in

	letref term_list = term_list in

	map 
	   (\xi. snd (assoc xi match_bindings)
		 ?
		 let h.rest = term_list in
		 term_list := rest ;
		 h) 
	   xi_list

;;    



let match_part s t = match_part_using s t [] ;;





