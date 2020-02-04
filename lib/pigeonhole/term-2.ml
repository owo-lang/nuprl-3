%
********************************************************************************
********************************************************************************
********************************************************************************

   term-2

********************************************************************************
********************************************************************************
********************************************************************************
%


%  Like tag_defined_term except that
   only the defined terms whose theorem name is in the supplied list 
   are tagged.
%
let tag_named_defined_term t name_list = 
   let a = head_of_application t  in  
   let n = arity_of_extraction a  in
   let m = arity_of_application t in
   if member_of_tok_list (destruct_term_of_theorem a) name_list & m = n
   then make_tagged_term (n+1) t
   else failwith `tag_defined_term`
;;


%  Apply the previous function to all subterms which are defined terms.
%
letrec tag_named_defined_terms name_list t =
   let t' = (map_on_subterms (tag_named_defined_terms name_list) t)  in
   (tag_named_defined_term t' name_list) ? t'
;;


let defs sentence =
   map (\x.x^`_`) (words sentence)
;;



% :term->bool.  -n is a redex exactly when n is -k for k a canonical
  natural number.
%

let is_redex t =
  
  let are_integers s t = is_integer_term s & is_integer_term t  in

  if is_apply_term t then is_lambda_term (fst (destruct_apply t))

  if is_spread_term t then is_pair_term (fst (destruct_spread t))

  if is_atom_eq_term t then 
    (let l,r,(),() = destruct_atomeq t in is_token_term l & is_token_term r)

  if is_int_eq_term t
    then (let l,r,(),() = destruct_inteq t in are_integers l r)

  if is_intless_term t 
    then (let l,r,(),() = destruct_intless t in are_integers l r)

  if is_decide_term t
    then (let e,(),() = destruct_decide t in  is_inl_term e or is_inr_term e)

  if is_integer_induction_term t then
    (let e,(),(),() = destruct_integer_induction t in is_integer_term e)

  if is_list_induction_term t then
    (let e,(),() 
       = destruct_list_induction t in is_nil_term e or is_cons_term e)

  if is_minus_term t then (destruct_integer (destruct_minus t) < 0
           ? false)

  if is_int_exp t & not is_natural_number_term t then
    (let [a;b] = list_subterms t  in
    are_integers a b & (is_modulo_term t or is_division_term t
              => not destruct_integer b = 0 | true))

  else false
;;


let tag_for_abs_sweep_reduce t =
   letrec Aux t =
      let t' = map_on_subterms Aux t   in
      if is_redex t' then make_tagged_term 1 t' else t'  in
   remove_illegal_tags (Aux t)
;;

let tag_for_top_level_compute t =
   if is_equal_term t then map_on_subterms (make_tagged_term 0) t
   else make_tagged_term 0 t
;;


   
