%-*- Mode: Fundamental; Default-character-style: (:FIX :ROMAN :VERY-LARGE); -*-%


%%
%***************************************************************************
                                  General.
***************************************************************************%

letrec every l P =
  if null l then true
  else P (hd l) & every (tl l) P
;;

letrec some l P =
  if null l then false
  else P (hd l) or some (tl l) P
;;

letrec dotimes n f =
  if n=0 then () else (f (); dotimes (n-1) f)
;;

let update_alist i v l =
  letrec f l = 
    if null l then [i,v] 
    else let (i',v').l' = l in 
         if i'=i then (i,v).l' 
         else (i',v'). f l' in
  f l
;;

let remove_alist_entry i l =
  letrec f l = 
    if null l then []
    else let (i',v').l' = l in 
         if i'=i then f l' 
         else (i',v'). f l' in
  f l
;;

let update_2d_alist i j v l =
  letrec f l = 
   if null l then [i, [j,v]] 
   else let (i',v').l' = l in 
        if i'=i then (i, update_alist j v v') . l' 
        else (i',v') . f l'  in
  f l
;;

lettype context = (tok#term) list ;;

let first_fun2 fun_list x y =
  letrec f l = hd l x y ? f (tl l) in
  f fun_list ? failwith `first_fun2`
;;

let num_hyps p = length (hypotheses p) ;;

let sequent_type i p = 
  if i=0 then concl p else h i p 
;;

let no_id = `NIL`;;
let is_no_id x = (x = `NIL`) ;;

let BackThruImplies i p =
  let ctxt,A = explode_function (h i p) in
  if concl p = A & every ctxt (is_no_id o fst) then
    RepeatFunAndEThen (\i. Refine (hyp i)) [] i p
  else failwith `BackThruImplies`
;;

letrec SimpleBackchainWith Tactic =

  let AtomizeConcl =
    REPEAT (IfOnConcl (\c. is_function_term c or is_and_term c)
                      (I THENG OnLastHyp RepeatAndE)
                      Fail) in

  letrec Aux (history: (term#term) list) =
    let AuxAux = 
      ApplyToAHyp 
      (\i p. (let A = h i p and C = concl p in
              if member (C,A) history then Fail 
              else BackThruImplies i THENM Aux ((C,A) . history)
             ) p)  in
    Try Hypothesis THEN 
    (AuxAux ORELSE (Progress AtomizeConcl THENW AuxAux)
            ORELSE Tactic)  in

  OnEveryHyp RepeatAndE THEN Aux []
;;

let SimpleBackchain = SimpleBackchainWith Fail ;;

% exclusive of start and end %
let library_open_interval ob1 ob2 =
( letrec f l = if hd l = ob1 then tl l else f (tl l)  in
  letrec g l l' = if hd l' = ob2 then rev l else g (hd l' . l) (tl l') in
  g [] (f (library()))
) ? failwith `library_open_interval`
;;

%%
%***************************************************************************
                           Definitions and terms.
***************************************************************************%

let append_underscore x = concatenate_tokens x `_` ;;

let defining_lemma_for_def name = append_underscore name;;

let def_has_membership_lemma name =
  main_goal_of_theorem (defining_lemma_for_def name) 
  = make_object_term
;;

let membership_lemma_for_def name = 
( let name' = defining_lemma_for_def name in
  if main_goal_of_theorem name' = make_object_term then
    append_underscore name'
  else fail
) ? failwith (`membership_lemma_for_def: no lemma for `^name)
;;

% wimpy arities for now (no binding structure) %
letref def_arities = []: (tok#int) list ;;

let def_arity_from_library name =
  length (fst (destruct_lambdas (extracted_term_of_theorem 
                                  (defining_lemma_for_def name))))
;;  

let add_def_arity name =
  def_arities := update_alist name (def_arity_from_library name) def_arities
;;

let def_arity name = 
  assq name def_arities ? (add_def_arity name; assq name def_arities)
;;

% fails if t not a defined term %
let name_of_def_instance t =
( let h,n = head_and_length_of_iterated_ap t in
  let name = remove_trailing_underscores (destruct_term_of_theorem h) in
  if n-1 = def_arity name then name else fail
) ? failwith `name_of_def_instance`
;;

let is_def_instance t =
  (name_of_def_instance t ; true) ? false
;;

% Because we're killing ttrees everywhere, we need a hack to
preserve a bit of readability: we'll save the term_of terms that
head def instances (since these will not have the ttrees ripped 
out) and reuse them when rebuilding a term .%

letref saved_pretty_def_heads = []: (tok#term) list ;;

let destruct_def_head term =
  let name = remove_trailing_underscores (destruct_term_of_theorem term) in
  saved_pretty_def_heads := update_alist name term saved_pretty_def_heads ;
  name
;;

let make_def_head name = 
  assq name saved_pretty_def_heads 
  ? make_term_of_theorem_term (append_underscore name)
;;

let clean_up_term_for_simping t =
  saved_pretty_def_heads := [] ;
  remove_display_forms t 
;;

let destruct_def_instance t =
( let h.l = destruct_iterated_ap t in
  let name = destruct_def_head h in
  if length l = def_arity name then name, (map (\x. [],x) l)
  else fail
) ? failwith `destruct_def_instance`
;;

% fails if arity mismatch %
let make_def_instance k l =
( if not length l = def_arity k then 
    fail ;
  make_iterated_ap
    (make_def_head k)
    (map snd l)
) ? failwith `make_def_instance: `^k 
;;

% fails on terms with no subterms %
let destruct_term t =

  let db = destruct_bound_id in

  (let a = destruct_any t in `ANY`, [[],a])
  ? 
  (let a = destruct_minus t in `MINUS`, [[],a])
  ?
  (let a,b = destruct_addition t in `ADDITION`, [[],a; [],b])
  ?
  (let a,b = destruct_subtraction t in `SUBTRACTION`, [[],a; [],b])
  ?
  (let a,b = destruct_multiplication t in `MULTIPLICATION`, [[],a; [],b])
  ?
  (let a,b = destruct_division t in `DIVISION`, [[],a; [],b])
  ?
  (let a,b = destruct_modulo t in `MODULO`, [[],a; [],b])
  ?
  (let a,b,c,d = destruct_integer_induction t in 
   `INTEGER-INDUCTION`, [[],a; db b; [],c; db d])
  ?
  (let a = destruct_list t in `LIST`, [[],a])
  ?
  (let a,b = destruct_cons t in `CONS`, [[],a; [],b])
  ?
  (let a,b,c = destruct_list_induction t in 
   `LIST-INDUCTION`, [[],a; [],b; db c])
  ?
  (let a,b = destruct_simple_rec_ind t in 
   `SIMPLE-REC-IND`, [[],a; db b])
  ?
  (let a,b = destruct_union t in `UNION`, [[],a; [],b])
  ?
  (let a = destruct_inl t in `INL`, [[],a])
  ?
  (let a = destruct_inr t in `INR`, [[],a])
  ?
  (let a,b,c = destruct_decide t in `DECIDE`, [[],a; db b; db c])
  ?
  (let x,A,B = destruct_product t in `PRODUCT`, [[],A; [x],B])
  ?
  (let a,b = destruct_pair t in `PAIR`, [[],a; [],b])
  ?
  (let a,b = destruct_spread t in `SPREAD`, [[],a; db b])
  ?
  (let x,A,B = destruct_function t in `FUNCTION`, [[],A; [x],B])  
  ?
  (let x,b = destruct_lambda t in `LAMBDA`, [[x],b])
  ?
  (let x,b = destruct_simple_rec t in 
   `SIMPLE-REC`, [[x],b])
  ?
  (let a,b = destruct_apply t in `APPLY`, [[],a; [],b])
  ?
  (let x,y,A,E = destruct_quotient t in `QUOTIENT`, [[],A; [x;y],E])
  ?
  (let x,A,B = destruct_set t in `SET`, [[],A; [x],B]) 
  ?
  (let l,A = destruct_equal t in `EQUAL`, map (\t. [],t) (A . l))
  ?
  (let a,b = destruct_less t in `LESS`, [[],a; [],b])
  ?
  (let a,b,c,d = destruct_atomeq t in `ATOMEQ`, [[],a; [],b; [],c; [],d])
  ?
  (let a,b,c,d = destruct_inteq t in `INTEQ`, [[],a; [],b; [],c; [],d])
  ?
  (let a,b,c,d = destruct_intless t in `INTLESS`, [[],a; [],b; [],c; [],d])
  ?
  failwith `destruct_term`
;;  

let abs_destruct_term t =
  destruct_def_instance t 
  ? 
  let k,l = destruct_term t in
  if k = `FUNCTION` & (let [[],A; [x],B] = l in is_no_id x)
    then `implies`, l
  if k = `FUNCTION` then `all`, l
  if k = `PRODUCT` & (let [[],A; [x],B] = l in is_no_id x)
    then `and`, l
  if k = `PRODUCT` then `some`, l
  if k = `SET ` & (let [[],A; [x],B] = l in is_no_id x)
    then `where`, l
  if k = `PRODUCT` then `some_where`, l
  if k = `UNION` then `or`, l
  else k,l     
;; 

let abs_term_kind t = 
  name_of_def_instance t ? 
  let k = term_kind t in
  if memq k ``PRODUCT UNION SET FUNCTION`` then fst (abs_destruct_term t) 
  else k
;;

% "abs" to distinguish it from the built in subterms %
let abs_subterms t =
  map snd (snd (abs_destruct_term t))
  ? []
;;

% tok -> (tok list # term) list -> term.  Inverse of abs_destruct_term. 
Accounts for the degenerate forms (where a bound id is NIL) by accepting an
empty bound id list in place of a list [`NIL`] %
let make_term k l =

( let b (ids, t) = 
    if null ids then t else make_bound_id_term ids t in
  let F1 g [w] = g (b w) and
      F2 g [w;x] = g (b w) (b x) and
      F3 g [w;x;y] = g (b w) (b x) (b y) and
      F4 g [w;x;y;z] = g (b w) (b x) (b y) (b z) in

  if k = `ANY` then F1 make_any_term l
  if k = `MINUS` then F1 make_minus_term l
  if k = `ADDITION` then F2 make_addition_term l
  if k = `SUBTRACTION` then F2 make_subtraction_term l
  if k = `MULTIPLICATION` then F2 make_multiplication_term l
  if k = `DIVISION` then F2 make_division_term l
  if k = `MODULO` then F2 make_modulo_term l
  if k = `INTEGER-INDUCTION` then F4 make_integer_induction_term l
  if k = `LIST` then F1 make_list_term l
  if k = `CONS` then F2 make_cons_term l
  if k = `LIST-INDUCTION` then F3 make_list_induction_term l
  if k = `UNION` or k = `or` then F2 make_union_term l
  if k = `INL` then F1 make_inl_term l
  if k = `INR` then F1 make_inr_term l
  if k = `DECIDE` then F3 make_decide_term l
  if k = `PRODUCT` or k = `and` or k = `some`
    then (let [[],A; u,B] = l in
          let x = if null u then no_id else (let [y]=u in y) in
          make_product_term x A B)
  if k = `PAIR` then F2 make_pair_term l
  if k = `SPREAD` then F2 make_spread_term l
  if k = `FUNCTION` or k = `all` or k = `implies`
    then (let [[],A; u,B] = l in
          let x = if null u then no_id else (let [y]=u in y) in 
          make_function_term x A B)
  if k = `LAMBDA`
    then (let [[x],b] = l in make_lambda_term x b)
  if k = `APPLY` then F2 make_apply_term l
  if k = `QUOTIENT` 
    then (let [[],A; [x;y],E] = l in make_quotient_term x y A E)
  if k = `SIMPLE-REC` then (let [[x],b] = l in make_simple_rec_term x b)
  if k = `SIMPLE-REC-IND` then F2 make_simple_rec_ind_term l
  if k = `SET` or k = `where` or k = `some_where`
    then (let [[],A; u,B] = l in
          let x = if null u then no_id else (let [y]=u in y) in 
          make_set_term x A B)
  if k = `EQUAL` then make_equal_term (snd (hd l)) (map snd (tl l))
  if k = `LESS` then F2 make_less_term l        
  if k = `ATOMEQ` then F4 make_atomeq_term l
  if k = `INTEQ` then F4 make_inteq_term l
  if k = `INTLESS` then F4 make_intless_term l
  else make_def_instance k l
) ? failwith (`make_term ` ^ k)
;;  

let add_to_list_q item l =
  if memq item l then l else item . l
;;

let defs_in_term t =
  letref defs = [] in
  letrec f t =
    (defs := add_to_list_q (name_of_def_instance t) defs ? []) ;
    (map f (abs_subterms t); ())  in
  f t; defs
;;

let subset l1 l2 = all (C member l2) l1 ;;

let abs_map_on_subterms f t =
  (let k,l = abs_destruct_term t in 
   make_term k (map (\x,y. f x y) l))
  ?? ``destruct_term`` t
;;

let remove_numerical_suffix x =
  let nums = ``0 1 2 3 4 5 6 7 8 9`` in
  letrec eat_while_num chs = 
    if null chs then [] 
    if member (hd chs) nums then eat_while_num (tl chs)
    else chs in
  implode (rev (eat_while_num (rev (explode x))))
;;

let id_avoiding_ids x ids =
  letrec f i x = let x' = x ^ (tok_of_int i) in
                 if memq x' ids then f (i+1) x else x'  in
  if memq x ids then f 1 (remove_numerical_suffix x) else x
;;

letrec associate item alist =
  if null alist then failwith `associate`
  if fst (hd alist) = item then snd (hd alist)
  else associate item (tl alist)
;;

let apply_alist alist item = associate item alist ? item
;;

let X f pair = f (fst pair), f (snd pair) ;;

let remove_no_ids l =
  filter (\id. not is_no_id id) l
;;

% ids must include all the free vars of t %
letrec rename_to_avoid_vars ids t = 
  abs_map_on_subterms
    (\ids' t.  
       letrec renaming ids_to_miss ids_to_rename = 
         (if null ids_to_rename then []
          else (let x = id_avoiding_ids (hd ids_to_rename) ids_to_miss in
               (hd ids_to_rename,x) . renaming (x . ids_to_miss) 
                                               (tl ids_to_rename)))  in
       let renaming = renaming ids (make_set (remove_no_ids ids')) in
       let renamed_ids = map (apply_alist renaming) ids' in
       renamed_ids,
       rename_to_avoid_vars (ids @ renamed_ids)
                            (substitute t (map (X mvt) renaming)))
    t
;;

let rename_to_avoid_sequent p t =
  rename_to_avoid_vars 
   (remove_no_ids (map id_of_declaration (hyps p)))
   t
;;

let make_not_term t = 
  make_function_term no_id t make_void_term
;;

let pattern_to_discriminator pattern =
  let ids = map dv (free_vars pattern) in
  \t. (first_order_match pattern t ids; true) ? false 
;;

% assume free_vars returns vars in left-to-right order. %
let pattern_to_destructor pattern =
  let ids = map dv (free_vars pattern) in
  \t. (let match_result = first_order_match pattern t ids in
       map (\x. assq x match_result) ids)
;;

let make_iff_term a b =
  make_product_term no_id (make_function_term no_id a b)
                          (make_function_term no_id b a)
;;

let iff_pattern = make_iff_term (mvt `p`) (mvt `q`) ;;

let is_iff_term = pattern_to_discriminator iff_pattern ;; 

let destruct_iff = 
  let f = pattern_to_destructor iff_pattern in
  \t. let [a;b] = f t in a,b  
;;

let is_equality_goal p = 
  (let [();()],() = destruct_equal (concl p) in true)
  ? false
;;

% Will be updateable from the library at some point %
let destruct_eq_reln_ap t =
  (let [t;t'],() = destruct_equal t in `equality`, t, t')
  ? (let t,t' = destruct_iff t in `iff`, t, t')
  ? failwith `destruct_eq_reln_ap`
;;

let is_eq_reln_ap t = 
  (destruct_eq_reln_ap t; true) ? false
;;

let abstract_function_type_and_tag t =
  let x,A,B = destruct_function t in
  make_function_term x A 
   (make_tagged_term 1 (make_apply_term (make_lambda_term x B) (mvt x)))
;;

let abstract_product_type_and_tag t =
  let x,A,B = destruct_product t in
  make_product_term x A 
    (make_tagged_term 1 (make_apply_term (make_lambda_term x B) (mvt x)))
;;

let abstract_set_type_and_tag t =
  let x,A,B = destruct_set t in
  make_set_term x A 
    (make_tagged_term 1 (make_apply_term (make_lambda_term x B) (mvt x)))
;;

% Hyp tac must not change conclusion %
let OnConclAndHyps (T: int->tactic) p =
  Same ( map T (rev (upto 0 (num_hyps p))) ) p
;;

% Hyp tac must not change conclusion %
let OnConclAndUntaggedHyps (T: int->tactic) p =
  Same ( map T (rev (filter (\i. i=0 or is_no_id (id_of_hyp i p))
                            (upto 0 (num_hyps p)))))
       p
;;

% Bag the stupid progress check %
ml_curried_infix `ELSE` ;;
let $ELSE (f1:tactic) (f2:tactic) (g:proof) = f1 g ? f2 g ;;

% Try uses ORELSE which has a Progress check %
let Attempt T p =  T p ? Id p ;;

let MoveToEnd i p =
  (Assert (h i p) THENL [Refine (hyp i); Thin i]) p
;;

let context_to_hyp_list ctxt =
  map (uncurry make_declaration) ctxt 
;;

let make_sequent2 (ctxt: context) (concl:term) =
  make_sequent (context_to_hyp_list ctxt) [] concl
;;

let extend_sequent p (ctxt: context) =
  make_sequent (hyps p @ (context_to_hyp_list ctxt)) (hidden p) (concl p)
;;

let change_concl_of_sequent p new_concl =
  make_sequent (hyps p) (hidden p) new_concl
;;

letrec map2 f l1 l2 =
  if null l1 & null l2 then []
  if null l2 or null l2 then failwith `map2`
  else f (hd l1) (hd l2) . map2 f (tl l1) (tl l2)
;;

let refine_proof p T = 
  let pl,v = T p in 
  assert ($= p) (v pl) 
;;

let Compute1Using tagger i =
  if i=0 then ComputeConclUsing tagger else ComputeHypUsing tagger i
;;

let Reduce1 i =
  Repeat (Compute1Using tag_redices i)
;;

% For tagless hyps only %
let Replace1 new_type Justification i =
  if i=0 then Assert new_type THENL [Id; Justification]
  else Assert new_type THENL [MoveToEnd i THEN Justification; Thin i]
;;
  
% (*->**) -> (* list) -> (**+void list) %
letrec map_trapping_failure f l =
  if null l then [] else (inl(f(hd l)) ? inr(()) ) 
                         . map_trapping_failure f (tl l)
;;

let sum_cases left_case right_case (val: *+**) =
  if isl val then left_case (outl val)
  else right_case (outr val)
;;


let FilterThen (T: tactic) (P: proof->bool) (Tlist:tactic list) (p:proof) =
  % hack it %
  letref l = Tlist in
  let pl,v = T p  in
  let pll,vl = 
    split (map (\p. if not P p then Id p
                    if null l then failwith `FilterThen` 
                    else (let T = hd l in l := tl l; T p))
               pl) in
  if not null l then failwith `FilterThen`
  else flat pll,  (v o mapshape (map length pll) vl)
;;


% Subgoals will have E'd hyp removed and no extra hyps. %
let CleanlyRepeatFunctionEOnLastHypThen Tac terms p =
  letrec T terms p = 
    let A = type_of_declaration (last (hyps p)) in
    let n = num_hyps p in
    if not is_function_term A then Tac p
    else  let x,(),() = destruct_function A in
          if is_no_id x then 
            (Refine (function_elim_independent n no_id)
             THENS T terms) p
          else (Refine (function_elim n (hd terms) no_id)
                THENS T (tl terms)) p  in
  (T terms THEN ThinToEnd (num_hyps p)) p
;;

let CleanlyRepeatFunctionEOnLastHyp terms =
  CleanlyRepeatFunctionEOnLastHypThen Id terms
;;
 
let CleanlyApplyLemma name terms =
  Refine (lemma name no_id) THEN
  CleanlyRepeatFunctionEOnLastHypThen (OnLastHyp (\i. refine (hyp i)))
                                      terms
;;

let set_equal l1 l2 =
  length (intersection l1 l2) = length l1 & length l1 = length l2
;;

% ordered wrt ids.  Fails if only a partial match is obtained. %
let terms_from_match pattern instance ids =
  (let match_result = first_order_match pattern instance ids in
   map (\x. assq x match_result) ids)
  ? 
  failwith `terms_from_match`
;;

%  The vars in match_bindings should be a subset of the ctxt vars. %
let extend_match_using_context match_bindings ctxt term_typer =
( letrec aux ctxt_etc =
    if null ctxt_etc then match_bindings
    else
      let ((x,A),ids) . rest = ctxt_etc in
      let bindings = aux rest in  
      if exists (\v. memq (dv v) ids & not is_bound (dv v) bindings)
                (free_vars A)
      then (  union (first_order_match A (term_typer (assq x bindings)) ids)
                    bindings
              ? bindings
           )
      else bindings  in
    aux (accumulate_and_combine (\ids (x,A). x.ids) [] ctxt)
) ? failwith `extend_match_using_context`
;;


let match_using_context pattern instance ids ctxt term_typer =
  extend_match_using_context (first_order_match pattern instance ids)
    ctxt term_typer
  ? failwith `match_using_context`
;;

let terms_from_match_using_context pattern instance ids context term_typer =
  (let match_result = 
     match_using_context pattern instance ids context term_typer in
   map (\x. assq x match_result) ids)
  ? 
  failwith `term_from_match_using_context`
;;  

let print_typing_table () =
  map (\p. map destruct_declaration (hyps p), concl p) 
      (flat (stored_proofs ()))
;;

letref delayed_typing_generator = id: void->void ;;
letref initial_typing_generated = false ;;

let maybe_generate_initial_typing () =
  if not initial_typing_generated then
    (initial_typing_generated := true; delayed_typing_generator (); ())
  else ()
;;

let lookup_typings t =
  maybe_generate_initial_typing ();
  apply_proof_store t
;;

let find_smallest measure l =
  letrec f i l = if null l then i 
                 else f (min i (measure (hd l))) 
                        (tl l) in
  if null l then l 
  else let min = f (measure (hd l)) (tl l) in
       filter (\x. measure x = min) l
;;

let best_typing t : term#proof =
  let pl = lookup_typings t in
  let types_and_proofs = map (\p. eq_type (concl p), p) pl in
  let minimal_wrt_universes =
    if exists (\T,(). is_universe_term T) types_and_proofs then
      find_smallest (\T,(). destruct_universe T ? big_U + 1) 
                    types_and_proofs 
    else types_and_proofs in
  let minimal_wrt_hyps = 
    find_smallest (\(),p. num_hyps p) minimal_wrt_universes in
  hd minimal_wrt_hyps
;;

let best_type_from_typing t =
  fst (best_typing t)
;;

let new_get_type p t = best_type_from_typing t ? get_type p t ;;  

let goal_types_one_of (l: term list) p =
  (let [t],() = destruct_equal (concl p) in member t l)
  ? false
;;

let add_single_typing p =
  let [t],() = destruct_equal (concl p) in
  add_to_proof_store t p
;;

% name ---> context, assumptions, conclusion, lemma instantiator.  %
let analyze_simple_lemma name =
  let l, body = explode_function (main_goal_of_theorem name) in
  let assumptions, ctxt = partition (is_no_id o fst) l in
  let ctxt_vars = map fst ctxt in
  ctxt,
  map snd assumptions,
  body,
  (let match_determined_vars = map dv (free_vars body) in
   let instantiation_computer =
     if set_equal match_determined_vars ctxt_vars
     then \p. terms_from_match body (concl p) ctxt_vars
     else \p. terms_from_match_using_context body (concl p) ctxt_vars
                                               ctxt (new_get_type p)
     in
   \p. CleanlyApplyLemma name (instantiation_computer p) p
  )
;;

let WithHypCleanup T p = 
  let n = num_hyps p in
  (T THEN (IfThen (\p. num_hyps p > n) (Attempt (ThinToEnd (n+1))))) p
;;

% def_typers handle equalities as well %
letref def_typers = []: (tok#tactic) list ;;


let make_true_term = make_equal_term make_int_term [make_integer_term 0] ;;
let is_true_term t = (t = make_true_term) ;;
let make_false_term = make_void_term ;;

let make_conjunction term_list =  
  if null term_list then make_true_term else 
  reverse_iterate_fun (\a b. make_product_term no_id a b) term_list 
;;

let ComputeEquandsInHypFor n =  
  ComputeHypUsing (\A. let l,T = destruct_equal A in  
                       make_equal_term A (map (make_tagged_term n) l)) 
;;

let SquashEqI p = 
( let (t.l), T = destruct_equal (concl p) in
  if is_squash_term T & is_axiom_term t then  
    (SetElementI THENL [Repeat EqI; Id]) p  else fail ) 
    ? failwith `SquashEqI` 
;;

let ProofAsTactic p' p =  
  let [t],A = destruct_equal (concl p) in  
  let Apply p = if equal_sequents p p' then Frontier p'  
                else failwith `ProofAsTactic` in
  let n = num_hyps p and n' = num_hyps p' in 
  let MaybeThinThen T =  
    if n'<n then Thinning (upto (n'+1) n) THEN T else T in
  let MaybeCumulativityThen T =  
    if is_universe_term A & not A = eq_type (concl p') then  
      Refine (cumulativity (destruct_universe (eq_type (concl p'))))  
      THEN T  
    else T in  
  MaybeThinThen (MaybeCumulativityThen Apply) p 
;;	

letrec all_distinct l =  if null l then true  else not member (hd l) (tl l)
& all_distinct (tl l) ;;

% member can't be a lambda abstraction (--- coding laziness).  Hashed proofs
in general (ie not just membership proofs) would be useful here --- see
SquashEqI section below.  %
let membership_lemma_to_eq_basher name =
  let ctxt,assums,mem,() = analyze_simple_lemma name in
  let ctxt_vars = map fst ctxt in
  if not all_distinct ctxt_vars then failwith
    `membership_lemma_to_eq_basher: quantified vars must be distinct.`;
  let z = id_avoiding_ids `z` ctxt_vars in
  let [t],T = destruct_equal mem in
  let assum = make_squash_term (make_conjunction assums) in
  let absd_mem = make_lambdas (ctxt_vars @ [z]) t in
  let type_for_absd_mem = implode_function (ctxt @ [no_id,assum]) T in
  let instantiation_computer inst p =
    if set_equal (map dv (free_vars mem)) ctxt_vars then
         terms_from_match mem inst ctxt_vars
    else terms_from_match_using_context mem inst ctxt_vars ctxt 
                                        (new_get_type p)  in
  let typing_pf_for_absd_mem = 
    refine_proof
     (make_sequent2 [] (make_equal_term type_for_absd_mem [absd_mem]))
     (Repeat (\p. let c = concl p in 
                  if is_lambda_term c then EqI p
                  if c=t then (OnLastHyp E THEN OnLastHyp RepeatAndE THEN
                               InstLemma name (map mvt ctxt_vars) THEN
                               Attempt Trivial) p
                  else Complete WeakAutotactic p))  in
  \p.(let [a;b], A = destruct_equal (concl p) in
      let insts = instantiation_computer (make_equal_term A [a]) p in
      let bds = first_order_match t b ctxt_vars in
      let insts' = 
        map (\x. assq x bds ? select (find_position x ctxt_vars) insts)
            ctxt_vars  in
      let a' = make_iterated_ap absd_mem  (insts @ [make_axiom_term]) in
      let b' = make_iterated_ap absd_mem (insts' @ [make_axiom_term]) in
      Assert (make_equal_term A [a';b']) THENL
      [RepeatApIUsingThen type_for_absd_mem 
         (Thinning (upto 1 (num_hyps p)) 
          THEN ReduceEquandicity THEN ProofAsTactic typing_pf_for_absd_mem)
       THEN Attempt SquashEqI
      ;OnLastHyp (ComputeHypEquandsFor (length ctxt + 1))
       THEN Attempt Eq
      ]
     ) p
;;

let TryCumulativity level p =
( let i = destruct_universe (eq_type (concl p)) in
  if level < i then Refine (cumulativity level) p
  else Id p
) ? Id p
;;

let def_typer_from_library name =
  (let lemma = membership_lemma_for_def name in
   let EqBasher = membership_lemma_to_eq_basher lemma in
   let (),(),body,T = analyze_simple_lemma lemma in
   let MemberBasher = 
     TryCumulativity (destruct_universe (eq_type body)) THEN T
     ? T   in
   \p. if 1 = length (fst (destruct_equal (concl p))) 
       then MemberBasher p
       else EqBasher p
  )
  ?
  let lemma = defining_lemma_for_def name in
  RepeatApIUsingThen (main_goal_of_theorem lemma) 
                     (Refine (def lemma no_id) THEN Eq)
;;  

let add_def_typer name =
  def_typers := update_alist name (def_typer_from_library name) def_typers
;;

let def_typer name = 
  assq name def_typers ? (add_def_typer name; assq name def_typers)
;;

let DefMemberI p =
( let (t.l),() = destruct_equal (concl p) in
  let name = name_of_def_instance t in
  if every l (\t. name = name_of_def_instance t)
  then def_typer name p
  else fail
) ? failwith `DefMemberI`
;;

% Assume that def args are always syntactically first order. %
let SimpleMemberI = 
  (WithHypCleanup DefMemberI) ELSE
  (\p. let (t.l),() = destruct_equal (concl p) in
       let k = abs_term_kind t in
       if memq k ``and implies`` then
         (EqI THENG OnLastHyp Thin) p
       if not null l & memq k ``all some some_where`` then
         (EqI THENL [Attempt ReduceEquandicity; Id]) p
       if not null l & k = `EQUAL` then
         (EqI THENL (Attempt ReduceEquandicity . map (K Id) (t.l))) p
       else EqI p)
;;

% not incremental %
let prove_and_add_typing p : proof =
  let pl,v = Attempt (Complete WeakAutotactic) p in
  let p' = v pl in
  add_single_typing p'; p'
;;

let subterms_may_be_simped t =
( is_def_instance t or 
  let k,() = abs_destruct_term t in
  memq k ``MINUS ADDITION SUBTRACTION MULTIPLICATION DIVISION MODULO 
           CONS UNION or INL INR and some PAIR all implies
           LAMBDA where some_where EQUAL LESS ATOMEQ INTEQ INTLESS``
) ? true
;;

% incremental.  Uses unique naming property (established in 
eqsimp_top_level) %
let add_typings p t T : proof =
  letrec f p =
    let t = first_equand (concl p) in
    snd (best_typing t)
    ?
    if not subterms_may_be_simped t then prove_and_add_typing p
    else
    ( let l = abs_subterms t % unique names assumed here % in
      let new_entry =
        refine_proof p
                     (SimpleMemberI THEN
                      If (goal_types_one_of l)
                         (\p. Attempt (ProofAsTactic (f p)) p)
                         (\p. Attempt (ProofAsTactic (prove_and_add_typing p)) p)
                     )   in
      (add_single_typing new_entry; new_entry)
    ) 
    ? prove_and_add_typing p    in
  f (change_concl_of_sequent p (make_equal_term T [t])) 
;;

let generate_typing p t T =
  initialize_proof_store ();
  add_typings p t T
;;

let update_typing_after_rewrite t t' =
( let T,p = best_typing t in
  add_typings p t' T
) ? failwith `update_typing_after_rewrite`
;;

let VarTyping p =
( let [t],T = destruct_equal (concl p) in
  let x = dv t in
  let T' = type_of_declaration 
             (find (\d. id_of_declaration d = x) (hyps p))  in
  if T=T' then Eq 
  if is_universe_term T then 
    Refine (cumulativity (destruct_universe T')) THEN Eq
  else failwith `VarTyping`
) p
;;

let ApplyTyping p =
  let t = first_equand (concl p) in
  if is_var_term t then VarTyping p
  else First (map ProofAsTactic (lookup_typings t)) p
;;

letref functionality_steps = []: (tok#(tok#tactic)) list ;;

let functionality_step_from_library name =
  let lemma_name = name ^ `_fnl` in
  let (),(),body,T = analyze_simple_lemma lemma_name in
  let abstract_and_tag_in_iff t =
    let a,b = destruct_iff t in 
    let f x = if abs_term_kind x = `some` then
                abstract_product_type_and_tag x
              if abs_term_kind x = `all` then
                abstract_function_type_and_tag x
              if abs_term_kind x = `some_where` then
                abstract_set_type_and_tag x
              else fail in
    make_iff_term (f a) (f b) in
  let MaybeAbstract = 
    if is_iff_term body then 
      Attempt (ReverseComputeConclUsing abstract_and_tag_in_iff)
    else Id in
  let WithCleanup =
    if not is_iff_term body then id
    if not member (abs_term_kind (fst (destruct_iff body))) 
                  ``some all some_where``
      then id
    else \T p.
         % an ugly hack to prevent unnecessary renaming % 
         let k,[A;[x],B] = 
           abs_destruct_term (fst (destruct_iff (concl p))) in
         (T THEN
            (\p. if memq (abs_term_kind (concl p)) ``all some some_where`` then
                   (Refine (function_intro big_U x) THENM ReduceConcl) p
                 if not is_membership_goal p then ReduceConcl p
                 if is_lambda_term (first_equand (concl p)) then EqI p
                 else Id p))
         p    in
  fst (destruct_eq_reln_ap body),
  WithCleanup (MaybeAbstract THEN T)
;;  
  
let add_functionality_step name =
  functionality_steps 
  := update_alist name (functionality_step_from_library name)
                  functionality_steps
;;

% must be consistent with analyze_term_for_rewriting %
let functionality_step name = 
  assq name functionality_steps 
  ? (add_functionality_step name; assq name functionality_steps)
;;


let Reflexivity p=
  let R,a,b = destruct_eq_reln_ap (concl p) in
  if not a=b then failwith `Reflexivity` ;
  if R = `equality` then ReduceEquandicity p
  if R = `iff` then 
    WithHypCleanup (RepeatFor 2 I THEN Attempt (OnLastHyp (\i. Refine (hyp i)))) p
  else failwith (`Reflexivity: unknown equiv: `^R)
;;

let EqRelnWfI p =
  let name,(),() = destruct_eq_reln_ap (first_equand (concl p)) in
  if name = `iff` then WithHypCleanup (RepeatFor 2 SimpleMemberI) p
  else SimpleMemberI p
;;

% Reduce >> aRb  to >> a=b in A %
let ReduceEqRelnApToEqualityThen T p =
( let R,a,b = destruct_eq_reln_ap (concl p) in
  SubstFor (make_equal_term (new_get_type p a) [a;b])
  THENL [T; Reflexivity; EqRelnWfI]
) p
;;

% returns a reln name and a rewrite justification of type tactic list ->
tactic. For now we assume that each abstract operator is associated with
unique eq reln, other than equality, which it respects.  Mixtures are not
handle yet; e.g., in simplifying A&B, both A and B must simplified wrt the
same relation (eq or iff).  % 
let apply_functionality reln_list abs_term_kind =
  if all ($= `equality`) reln_list then 
    `equality`, FilterThen SimpleMemberI is_equality_goal 
  else let eqreln, T = functionality_step abs_term_kind in
       eqreln, 
       (\Tlist. let adjusted_Tlist = 
                  map (\T,R. if R=`equality` then 
                               ReduceEqRelnApToEqualityThen T
                             else T)
                      (Tlist com reln_list) in
                FilterThen T (is_eq_reln_ap o concl) adjusted_Tlist)
;;

let SplitIff a =
  WithHypCleanup
  (\p. let t,t' = destruct_iff (concl p) in
       (Seq [make_iff_term t a; make_iff_term a t']
        THENL [Id; Id; \p. let n = num_hyps p in 
                           (E n THEN E (n-1) THEN Backchain) p])
       p)
;;

letref transitivity_table = []: (tok#(term->tactic)) list ;;

let transitivity_from_library name =
( let lemma_name = name ^ `_transitive`  in
  let ctxt,[A1;A2],B,() = analyze_simple_lemma lemma_name in
  let ids = map fst ctxt in
  let (),y,() = destruct_eq_reln_ap A2 in
  if length ids = length (free_vars B) + 1 then
    \a p. let bds = (dv y,a) . first_order_match B (concl p) ids in
          CleanlyApplyLemma lemma_name (map (\id. assq id bds) ids) p
  else
    \a p. let bds = extend_match_using_context
                     ((dv y,a) . first_order_match B (concl p) ids)
                     ctxt (new_get_type p) in
          CleanlyApplyLemma lemma_name (map (\id. assq id bds) ids) p
) ? if name = `iff` then SplitIff else failwith `transitivity_from_library`
;;  

let add_transitivity name =
  transitivity_table 
  := update_alist name (transitivity_from_library name)
                  transitivity_table
;;

let transitivity name = 
  assq name transitivity_table 
  ? (add_transitivity name; assq name transitivity_table)
;;

let TransitivityThen b T1 T2 p =
  let R = fst (destruct_eq_reln_ap (concl p)) in
  FilterThen (transitivity R b) (is_eq_reln_ap o concl) [T1;T2] p
;;

% returns a reln name and a rewrite justification of type
term -> tactic -> tactic -> tactic.%
let apply_transitivity R1 R2 b =
  if R1 = `identity` then R2, (\T1 T2. T2)
  if R2 = `identity` then R1, (\T1 T2. T1)
  if R1=`equality` & R2=`equality` then
    `equality`, (\T1 T2. SplitEq b THENL [T1;T2])
  if R1=`equality` then % reduce >> a R c to >> a=b in T and >> b R c %
  ( R2,
    \T1 T2 p.
    ( let n = num_hyps p in 
      let (),a,c = destruct_eq_reln_ap (concl p) in
      SubstFor (make_equal_term (new_get_type p a) [a;b])
      THENL [T1; T2; EqRelnWfI THEN Attempt (Thin (n+1))]
    ) p
  )
  if R2=`equality` then % reduce >> a R c to >> a R b and >> b=c in T %
  ( R1,
    \T1 T2 p.
    ( let n = num_hyps p in 
      let (),a,c = destruct_eq_reln_ap (concl p) in
      SubstFor (make_equal_term (new_get_type p c) [c;b])
      THENL [SwapEquands THEN T2; T1; EqRelnWfI THEN Attempt (Thin (n+1))]
    ) p
  )
  else R1, TransitivityThen b
;;  




%-------------------------------------------------------------------------

      Simplification by Direct Computation

--------------------------------------------------------------------------%
                                                                             

% t ---> t', names.  If t and t' are normalized, expanding exactly the
definitions named in names, the results must be equal as terms.  %
lettype dcsimp = term -> (term # (tok list)) ;;

letref unit_dcsimps = []: (tok#((tok#dcsimp) list)) list ;;

let add_dcsimp abs_term_kind dcsimp_name dcsimp =
  unit_dcsimps := 
    update_2d_alist abs_term_kind dcsimp_name dcsimp unit_dcsimps
;;

let add_simple_dcsimp name t1 t2 extra_defs =
  let ids = map dv (free_vars t1) in
  if not subset (free_vars t2) (free_vars t1) then 
    failwith `add_simple_dcsimp: too many free vars in rhs.` ;
  let defs = union (union (defs_in_term t1) (defs_in_term t2)) 
                   extra_defs in
  add_dcsimp (abs_term_kind t1) name
    (\t. let subst = first_order_match t1 t ids in
         substitute t2 (map (\x,t. mvt x, t) subst),
         defs)
  ; ()
;;

let add_patterned_dcsimp name t1 t2 defs_to_expand =
  let ids = map dv (free_vars t1) in
  if not subset (free_vars t2) (free_vars t1) then 
    failwith `add_simple_dcsimp: too many free vars in rhs.` ;
  add_dcsimp (abs_term_kind t1) name
    (\t. let subst = first_order_match t1 t ids in
         substitute t2 (map (\x,t. mvt x, t) subst),
         defs_to_expand)
  ; ()
;;

let get_unit_dcsimps abs_term_kind =
  map snd (assq abs_term_kind unit_dcsimps)
;;

let standard_dcsimp k t =
  failwith `standard_dcsimp`
;;

let unit_dcsimp t =
  let k = abs_term_kind t in
  let t,l =
    first_fun (get_unit_dcsimps k) t
    ? standard_dcsimp k t in
  reduce t, l
;;

let dcsimp_then (s1: dcsimp) (s2: dcsimp) t =
  let t',names = s1 t in
  let t'',names' = s2 t' in
  t'', union names names'
;;

letrec repeat_dcsimp s t =
  dcsimp_then s (repeat_dcsimp s) t
  ? t,[]
;;

let subdcsimp (s: dcsimp) t =
  let k, l = abs_destruct_term t in
  let ids, subterms = split l in
  let subterm_simps = map_trapping_failure s subterms in
  if some subterm_simps isl 
  then let new_subterms, defs = 
         split (map2 (\t x. sum_cases id (\(). t,[]) x)
                     subterms subterm_simps) in
       make_term k (ids com new_subterms)
       , accumulate union [] defs
  else fail
;;

let id_dcsimp : dcsimp = \t. t,[] ;;

let dcsimp_orelse (s1: dcsimp) s2 t = s1 t ? s2 t ;;

let try_dcsimp s = dcsimp_orelse s id_dcsimp ;;

letrec bottom_up_dcsimp t =
  (dcsimp_orelse (dcsimp_then (subdcsimp bottom_up_dcsimp) 
                              (try_dcsimp unit_dcsimp))
                 unit_dcsimp
  ) t
;;

let tag_for_def_expansion names t =  
  letref something_was_tagged = false in
  letrec f t =
    let t' = abs_map_on_subterms (\l s. l, f s) t in
    ( let name = name_of_def_instance t' in
      if memq name names then 
        (something_was_tagged := true ;
         make_tagged_term (1 + arity_of_def name) t')
      else t')
    ? t'  in
  let res = f t in
  if something_was_tagged then res else failwith `tag_for_def_expansion`
;;

let SemiNormalize1 names i = 
  Repeat (Compute1Using (tag_for_def_expansion names) i)
  THEN Reduce1 i
;;  

let SNorm names = OnConclAndHyps (SemiNormalize1 names) ;;

let DCSimp1 i p =
  let t = (sequent_type i p) in
  let t', names = repeat_dcsimp bottom_up_dcsimp t in
  Replace1 t' (OnLastHyp (SemiNormalize1 names)
               THEN SemiNormalize1 names 0 THEN Hypothesis)
           i p
;;

let DCSimp = OnConclAndUntaggedHyps DCSimp1 ;;



%-------------------------------------------------------------------------

      Simplification wrt Arbitrary Equivalence Relations

--------------------------------------------------------------------------%


% t |--> t', id, T where t and t' are typed, id names an equivalence
relation R, t is typed in context H and T proves H >> R(t,t').  Another
input might be the name of an eq reln which is an upper bound (wrt
refinement) for R.  %

% failure means no progress %
lettype eqsimp = proof -> term -> (term # (tok # tactic)) ;;

letref unit_eqsimps = []: (tok # ( (tok#eqsimp) list )) list ;;

let add_unit_eqsimp abs_term_kind eqsimp_name eqsimp =
  unit_eqsimps := 
    update_2d_alist abs_term_kind eqsimp_name eqsimp unit_eqsimps
;;

let add_simp = add_unit_eqsimp ;;

let conditions_satisfied p conds =
  (map (\c. if is_true_term c or is_atom_term c or is_int_term c then Id p
            else Trivial (change_concl_of_sequent p c))
       conds 
   ; true)
  ? false
;;

let eqsimp_then (s1: eqsimp) (s2: eqsimp) p t =     
  let t1, reln1, T1 = s1 p t in
  let t2, reln2, T2 = s2 p t1 in
  let reln, T = apply_transitivity reln1 reln2 t1 in
  t2, reln, T T1 T2
;;

let id_eqsimp (p:proof) (t:term) = t, `identity`, Id ;;

let eqsimp_orelse (s1: eqsimp) s2 p t = s1 p t ? s2 p t ;;

letrec repeat_eqsimp s p t =
  (eqsimp_orelse (eqsimp_then s (repeat_eqsimp s))
                 id_eqsimp
  ) p t
;;

let swap_equands_as_simp (p:proof) t =
  let [a;b],A = destruct_equal t in
  let t' = make_equal_term A [b;a] in
  update_typing_after_rewrite t t' ;
  t',
  `iff`, 
  RepeatFor 2 I THEN Try Eq
;;

let add_lemma_simp name =
  let ctxt, conditions, body, T = analyze_simple_lemma name in
  let vars = map fst ctxt in
  let reln_name, t, t' = destruct_eq_reln_ap body in
  if not all (\c. subset (free_vars c) (free_vars t)) conditions then
    failwith (`lemma_to_simp: conditions have too many variables: ` ^ name) ;
  if not subset (free_vars t') (free_vars t) then
    failwith (`lemma_to_simp: rewritten term has too many variables: ` ^ name) ;
  let lemma_simp p u =
    let subst = map (\x,t. mvt x, t) (first_order_match t u vars) in 
    if not conditions_satisfied p (map (\u. substitute u subst) conditions)
    then fail
    else substitute t' subst, reln_name, T in
  let simp = if is_equal_term t & reln_name = `iff` then
               (eqsimp_orelse lemma_simp 
                              (eqsimp_then swap_equands_as_simp lemma_simp))
             else lemma_simp  in
  add_unit_eqsimp (abs_term_kind t) name simp
;;

let add_simple_simp simp_name t t' conditions R T =
  if not all (\c. subset (free_vars c) (free_vars t)) conditions then
    failwith (`add_simple_simp: conditions have too many variables: ` ^ simp_name) ;
  if not subset (free_vars t') (free_vars t) then
    failwith (`add_simple_simp: rewritten term has too many variables: ` ^ simp_name) ;
  let vars = map dv (free_vars t) in
  add_unit_eqsimp (abs_term_kind t) simp_name
    (\ p u. let subst = map (\x,t. mvt x, t) (first_order_match t u vars) in 
            if not conditions_satisfied p (map (\u. substitute u subst) conditions)
            then fail
            else substitute t' subst, R, T)
;;


let get_unit_eqsimps abs_term_kind =
  map snd (assq abs_term_kind unit_eqsimps)
;;

let unit_eqsimp p t =
( let t',reln,T = 
    first_fun2 (get_unit_eqsimps (abs_term_kind t)) p t 
    ? first_fun2 (get_unit_eqsimps `VAR`) p t 
      % VAR simps apply to anything %  in
  update_typing_after_rewrite t t' ;
  t',reln,T
) ? failwith `unit_eqsimp`
;;

% removing the types from the contexts gives the result of abs_destruct_term %
let analyze_term_for_rewriting t =
  let k,l = abs_destruct_term t in
  k,
  ( if memq k ``all some some_where`` then 
      (let [[],A;[x],B] = l in [[x,A],B])
    if k=`LAMBDA` then
      (let [[x],b] = l in
       [ [x, best_type_from_typing t], b ])
    if k=`EQUAL` then map (\x,y. [],y) (tl l)
    if memq k ``ATOMEQ INTEQ INTLESS`` then
      (let [a;b;c;d] = map snd l in
       let A = if k = `ATOMEQ` then make_equal_term make_atom_term [a;b]
               if k = `INTEQ` then make_equal_term make_int_term [a;b]
               else make_less_term a b in
       let B = make_not_term A in
       [[],a; [],b; [no_id,A],c; [no_id,B],d])
    else
       map (\l,t. if every l is_no_id then [],t else fail) l
  )
  ? failwith `analyze_term_for_rewriting`
;;

% the simped_subterms correspond to the subterms of t given by
analyze_subterms.  (These may not be all the subterms of the result, 
so we need to do some work.) %
let assemble_simped_term t simped_subterms =
  let k,l = abs_destruct_term t in
  let new_operands =
    if memq k ``all some some_where`` then 
      (let [[],A;[x],B] = l in [[],A; [x], hd simped_subterms])
    if k=`EQUAL` then [hd l; [], first simped_subterms; 
                             [], second simped_subterms]
    else map fst l com simped_subterms in
  make_term k new_operands
;;

let remove_types_from_contexts l = map (\c,t. map fst c, t) l ;;

let subeqsimp s p t =
  if not subterms_may_be_simped t then 
    failwith `subeqsimp: subterms may not be simped` ;
  let k, subterms_etc = (analyze_term_for_rewriting t) in
  let subterm_simps = 
    map_trapping_failure (\c,t'. s (extend_sequent p c) t')
                         subterms_etc in  
  if every subterm_simps (\x. isr x or (let (),R,() = outl x in R = `identity`))
    then fail;
  let id_to_eq t = t, `equality`, ReduceEquandicity in
  let repaired_subterm_simps = 
    map2 (\(c,t) v. (sum_cases (\t',R,T. if R = `identity` then id_to_eq t
                                                           else t',R,T)
                               (\(). id_to_eq t) 
                               v))
         subterms_etc subterm_simps  in 
  let new_subterms,l = split repaired_subterm_simps in
  let subterm_rewrite_relns, subterm_rewrite_justifications =
    split l in
  let t' = assemble_simped_term t new_subterms in
  update_typing_after_rewrite t t' ;
  let reln,T = 
    apply_functionality subterm_rewrite_relns (abs_term_kind t) in
  t', reln, T subterm_rewrite_justifications
;;

let try_eqsimp s = eqsimp_orelse s id_eqsimp ;;

letrec bottom_up_eqsimp p t =
  (eqsimp_orelse (eqsimp_then (subeqsimp bottom_up_eqsimp) 
                              (try_eqsimp unit_eqsimp))
                 unit_eqsimp
  ) p t
;;

let guess_universe p t = make_universe_term 1 ;;

let eqsimp_top_level p t =
  let t = clean_up_term_for_simping (rename_to_avoid_sequent p t) in
  initial_typing_generated := false ;
  delayed_typing_generator := 
    (\(). generate_typing p t (guess_universe p t); ()) ;
  repeat_eqsimp bottom_up_eqsimp p t 
;;

let EqSimp1 i p =

  let t = (sequent_type i p) in
  % don't want to assume hyp i when simping it %
  let p' = if i=0 then p else hd (fst (Thin i p)) in 
  let t', reln, T = eqsimp_top_level p' t in
  let ApplyT = OnLastHyp Thin THEN T in

  let Justification =
    if reln = `equality` then
      Assert (make_equal_term (best_type_from_typing t) [t;t'])
      THENL [ApplyT
            ;Eq ELSE (\p. OnNthLastHyp 2 
                              (\i. let x = new_id p in
                                   TagHyp i x THEN ExplicitI (mvt x)
                                   THEN Attempt Eq) p)
            ]
    if reln = `iff` then
      Assert (make_iff_term t t')
      THENL [ApplyT
            ;\p. let n = num_hyps p in
                 (E n THEN ( (E (n+1) THEN Trivial) 
                             ELSE (E (n+2) THEN Trivial) )) p]
    if reln = `identity` then Hypothesis
    else failwith (`EqSimp1: unknown relation: ` ^ reln) in

  (Replace1 t' Justification i THEN Attempt ApplyTyping) p
;;

let EqSimp = OnConclAndUntaggedHyps EqSimp1 ;;

let Alternate A B = 
  letrec T1 p = (A THEN T2) p ? Attempt (B THEN T1) p 
  and    T2 p = (B THEN T1) p ? Attempt (A THEN T2) p in
  T1
;;

% Never fails (unlike DCSimp and EqSimp). %
letrec Simp1 i p =
  let n = if i=0 then 0 else num_hyps p in
  ((if i>0 then MoveToEnd i else Id)
   THEN Alternate (Progress (DCSimp1 n))
                  (Progress (EqSimp1 n)))
  p
;;

let Simp = OnConclAndUntaggedHyps Simp1 ;;

% name can be the name of an eq reln or a definition.  Decaches. %
let note_related_change name =
  transitivity_table := remove_alist_entry name transitivity_table ;
  functionality_steps := remove_alist_entry name functionality_steps ;
  def_typers := remove_alist_entry name def_typers ;
  def_arities := remove_alist_entry name def_arities ;
  ()
;;

let simp_init () =
  unit_eqsimps := [] ;
  unit_dcsimps := [] ;
  transitivity_table := [] ;
  functionality_steps := [] ;
  def_typers := [] ;
  def_arities := [] ;
  ()
;; 


%%
%***************************************************************************
                           Some particular simps.
***************************************************************************%

let [a;b;c;d] = map mvt ``a b c d`` in
let t = make_atomeq_term a b c d in
let cond = make_equal_term make_atom_term [a;b] in
add_simple_simp `atomeq_true` t c [cond] `equality`
                (Refine (atom_eq_computation 1 true) 
                 THEN Try (ReduceEquandicity ELSE Hypothesis)) ;
add_simple_simp `atomeq_false` t d [make_not_term cond] `equality`
                (Refine (atom_eq_computation 1 false) 
                 THEN Try (ReduceEquandicity ELSE Hypothesis)) 
;;

let [a;b;c;d] = map mvt ``a b c d`` in
let t = make_inteq_term a b c d in
let cond = make_equal_term make_int_term [a;b] in
add_simple_simp `inteq_true` t c [cond] `equality`
                (Refine (int_eq_computation 1 true) 
                 THEN Try (ReduceEquandicity ELSE Hypothesis)) ;
add_simple_simp `inteq_false` t d [make_not_term cond] `equality`
                (Refine (int_eq_computation 1 false) 
                 THEN Try (ReduceEquandicity ELSE Hypothesis)) 
;;

let [a;b;c;d] = map mvt ``a b c d`` in
let t = make_intless_term a b c d in
let cond = make_less_term a b in
add_simple_simp `intless_true` t c [cond] `equality`
                (Refine (int_less_computation 1 true) 
                 THEN Try (ReduceEquandicity ELSE Hypothesis)) ;
add_simple_simp `intless_false` t d [make_not_term cond] `equality`
                (Refine (int_less_computation 1 false) 
                 THEN Try (ReduceEquandicity ELSE Hypothesis)) 
;;

let is_trivial_prop t =
  t = make_false_term or t = make_true_term 
;;

add_simp `VAR` `not_simp` 
  (\p t. if not is_trivial_prop t & conditions_satisfied p [make_not_term t]
         then make_false_term, `iff`, 
              (I THEN Attempt Hypothesis THEN I
                 THENL [OnLastHyp (\i. Refine (void_elim i)); EqI] )
         else fail)
;;

add_simp `VAR` `true_simp` 
  (\p t. if not is_trivial_prop t & conditions_satisfied p [t]
         then make_true_term, `iff`, 
           (RepeatFor 2 I THEN Attempt Hypothesis THEN Try I)
         else fail)
;;

let ApplyPropSchema name_ext i p =
( let x = (id_of_hyp i p) in
  let lemma = abs_term_kind (h i p) ^ `_` ^ name_ext in
  if not memq lemma (library()) then failwith
    `ApplyPropSchema: `^lemma ;
  (AbstractConcl (mvt x) THEN Lemma lemma THENM ReduceConcl)
  THEN Attempt (Thin i)
  THEN Repeat (\p. if is_lambda_term (first_equand (concl p)) 
                   then EqI p else Id p)
) p
;;  

let ListInduction i p =
  if is_list_term (h i p) then (E i THEN Attempt (Thin i)) p
  else failwith `ListInduction`
;;

let Induction i = 
  ApplyPropSchema `ind` i ELSE ListInduction i
;;

let Unroll i = 
  ApplyPropSchema `unroll` i ELSE 
  If (\p. is_list_term (h i p)) (E i THENL [Id; OnLastHyp Thin]) Fail
;;

let is_declared x p =
  (find_declaration x p; true) ? false
;;

let BringAndThinDependingHyps x p =
  let hyps_to_thin = 
    map snd (filter (\A,i. member (mvt x) (free_vars (type_of_declaration A)))
                    (hyps p com upto 1 (num_hyps p))) in
  (BringDependingHyps x THEN Thinning hyps_to_thin) p
;;

let On x T p = 
( if is_declared x p then BringAndThinDependingHyps x THEN OnVar x T
  else OnVar x T
) p
;;

let EVar var = On var E ;;

let DestructEqUsing destructor T i p =
( let z,b = destruct_lambda destructor ? failwith `DestructEq: not a lambda` in
  let equands, T' = destruct_equal (h i p) in
  Assert (make_equal_term T (map (make_apply_term destructor) equands))
  THENL [ApI (make_function_term no_id T' T) THENL [EqI; Id]; OnLastHyp Reduce1]
) p
;;

let BringVar x =
  BringAndThinDependingHyps x THEN
  OnVar x (\i. BringHyp i THEN Thin i)
;;

let ThinVars l p =
  Thinning (map (C find_declaration p) l) p
;;

let ThinVar x = ThinVars [x] ;;

let AndThin T i = T i THEN Thin i ;;

let OnLast = OnLastHyp ;;

let AbsI p =
( if is_iff_term (concl p) then (I THENG OnLast Thin) THEN Try I
  else I ) p
;;

let RemoveJunkHyp i p =
  let T = h i p in
  if is_true_term T then Try (Thin i) p else fail
;;

% WeakAutotactic with I replaced by AbsI. %
let Auto =
    (Repeat
      ( Trivial
        ORELSE (Progress (OnEveryHyp RepeatAndE) THEN Try Trivial)
        ORELSE (UnSquash THEN Try Trivial)
        ORELSE WeakMember
        ORELSE BashArithGoal
        ORELSE (IfOnConcl is_canonical_type (AbsI THEN Try Trivial) Fail)
        ORELSE (\p. 
                let [t;t'],T = destruct_equal (concl p) in
                if is_universe_term T & simplify t = simplify t' then
                  (RepeatUntil is_arith_eq_goal WeakMemberI THEN Try Trivial) p
                else fail
               )
        ORELSE OnEveryHyp (Try o RemoveJunkHyp)
        ORELSE (\p. First (current_autotactic_additions ()) p)
      )
    )
;;

let Expand = SNorm ;;

let Expand1 = SemiNormalize1 ;;

let HypCases l i p =
( if is_function_term (h i p) then
    MoveToEnd i THEN OnLast (RepeatFunctionE l) THEN Thin (num_hyps p)
    THENS (OnLast CaseHyp)
  else CaseHyp i
) p
;;

let goal_member p = first_equand (concl p) ;;

let SomeE = RepeatProductE ;;

letref redef_enabled = false ;;
let enable_redef () = redef_enabled := true ;;
let disable_redef () = redef_enabled := false ;;

let MaybeRedef p = if redef_enabled then Redef p else Id p ;;


let compactly_print_node depth parent_hyps p =

  let print_term term =
    map (\x. print x; print ` `) 
    (remove_trailing_empty_line (term_to_toks term));
    () in
  letref hyp_printed = false in

  indent depth;
  map (\i,H. let x,A = destruct_declaration H in
             if member H parent_hyps then ()
             else (hyp_printed := true;
                   print (tok_of_int i); print `. `;
                   if not x=`NIL` then (print x; print `: `);
                   print_term A;
                   print `  `))
      (upto 1 (num_hyps p) com hyps p);
  if hyp_printed then (print_return_to_snapshot_file();
                       indent depth);
  print `>> `;
  print_term (concl p);
  print_return_to_snapshot_file();
  indent depth;
  if is_refined p
  then (print `BY ` ; 
        map (\x. print x; print ` `)
            (remove_trailing_empty_line 
               (rule_to_toks (refinement p)));
        ())
  else print `INCOMPLETE`;
  print_return_to_snapshot_file()
;;

letrec compactly_print_proof depth parent_hyps proof =
  compactly_print_node depth parent_hyps proof ;
  if is_refined proof then
    (map (compactly_print_proof (depth+1) (hyps proof)) (children proof);())
;;


let compact_mm proof =
  (open_snapshot_file ();
  (compactly_print_proof 0 [] proof);
  close_snapshot_file ());
  (IDTAC proof)
;;

