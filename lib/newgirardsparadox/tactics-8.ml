let has_two_principal_arguments t =
  member_of_tok_list (term_kind t)
    [`ATOMEQ`; `INTEQ`; `INTLESS` ; `MINUS`; `ADDITION`;
     `SUBTRACTION`; `MULTIPLICATION`; `DIVISION`; `MODULO`]
;;


letrec is_head_redex t =
  if not is_noncanonical_term t then false
  if is_redex t then true
  if has_two_principal_arguments t then
    (let a.b.t = subterms t in is_head_redex a or is_head_redex b)
  else is_head_redex (hd (subterms t))
;;

let tag_head_redex t =
  if is_head_redex t then make_tagged_term 1 t
  else failwith `tag_head_redex`
;;

let HeadReduceConcl =
  Repeat (ComputeConclUsing tag_head_redex)
;;

let HeadReduceHyp i =
  Repeat (ComputeHypUsing tag_head_redex i)
;;

let HeadReduceHyps hyp_list =
  iterate_fun 
    (\T T'. T THEN T') 
    (map HeadReduceHyp hyp_list) 
;;

let HeadReduce =
  HeadReduceConcl
  THEN
  ForEachHypFrom HeadReduceHyp 1
;;










% The "defined" elims and intros use global lists of arguments.
  The lists are accessed by the "get_..." functions, which are
  destructive.  Defined rules should fail with `no` if they
  find themselves to be inapplicable, in which case other rules
  will be tried, or with some other token, in which case no 
  other rules will be tried.
%

letref d_tactic_term_args = []: term list ;;

letref d_tactic_choice_args = []: tok list ;;

letref d_tactic_id_args = []: tok list ;;

letref d_tactic_hyp_num_arg = 0 ;;

let get_term_arg () =
  ( let res = hd d_tactic_term_args in
    (d_tactic_term_args := tl d_tactic_term_args ; res)
  ) ? failwith `need a term.`
;;

let get_choice_arg () =
  ( let res = hd d_tactic_choice_args in
    (d_tactic_choice_args := tl d_tactic_choice_args ; res)
  ) ? failwith `need a choice.`
;;

let get_id_arg () =
  ( let res = hd d_tactic_id_args in
    (d_tactic_id_args := tl d_tactic_id_args ;  res)
  ) ? failwith `need an id.`
;;


let hyp_num_arg () =
  d_tactic_hyp_num_arg
;;

let set_d_tactic_args i terms choices ids =
  d_tactic_term_args := terms ;
  d_tactic_choice_args := choices ;
  d_tactic_id_args := ids ;
  d_tactic_hyp_num_arg := i 
;;

let SomeDTactic Tactics p =
  letrec Aux Ts p = 
    hd Ts p 
    ?? [`no`] Aux (tl Ts) p    in
  Aux Tactics p ?? [`HD`] failwith `none applicable`
;;


letref DElim_list = [\p. Elim (hyp_num_arg ()) p]: tactic list ;;


let undo_DElim_definitions () =
  DElim_list := [\p. Elim (hyp_num_arg ()) p]
;;


let define_DElim (T: tactic) =
  DElim_list := T . DElim_list
;;


let CtdDElim i p =
  d_tactic_hyp_num_arg := i ;
  (HeadReduceHyp i THEN
   SomeDTactic DElim_list) p
;; 

let DElim i terms choices ids p =
  set_d_tactic_args i terms choices ids ;
  CtdDElim i p
;;


letref DIntro_list = [Intro]: tactic list ;;


let undo_DIntro_definitions () =
  DIntro_list := [Intro]
;;


let define_DIntro (T: tactic) =
  DIntro_list := T . DIntro_list
;;



let CtdDIntro p =
  (HeadReduceConcl THEN
   SomeDTactic DIntro_list) p
;; 


let DIntro terms choices ids p =
  set_d_tactic_args 0 terms choices ids ;
  CtdDIntro p
;;


ml_curried_infix `TRYTHENL` ;; 

let $TRYTHENL (tac1:tactic) (tac2l:tactic list) (g:proof) =
   let gl,p = tac1 g  in
   (  let gll,pl = split(map (\(tac2,g). tac2 g) tac2gl)
                  where tac2gl = combine(tac2l,gl) in
      flat gll  ,  (p o mapshape(map length gll)pl)
   )
   ?? [`combine`] gl, p
;;


% A DIntro or DElim may be applications of patterns.  To
  create a pattern, set the args to be arbitrary, (do this
  in a library object right before the pattern), and develop
  a proof of a statement of a theorem that uses atoms for 
  syntactic variables.  Get parameters using only the get functions,
  and only refer to hypothesis numbers via nth_last_hyp.
%
let ApplyPattern pattern_pf =
  letrec Aux pattern_pf =
    if is_refined pattern_pf then
      Refine (refinement pattern_pf) 
      TRYTHENL map Aux (children pattern_pf)
    else Idtac  in
  Aux pattern_pf
;;

let nth_last_hyp j p =
  number_of_hyps p - (j-1)
;;

let make_macro_recognizer name =
  \t. name = top_def_of_term t ? false
;;

let make_def_recognizer name arity =
  let name = name ^ `_` in
  \t. (name = destruct_term_of_theorem (head_of_application t)
       & arity = arity_of_application t) ? false
;;


let define_patterned_DIntro pattern_name recognizer =
  define_DIntro
  (\p.
    if recognizer (concl p)
    then ApplyPattern (proof_of_theorem pattern_name) p
    else failwith `no`
  )
;;

let define_patterned_DElim pattern_name recognizer =
  define_DElim
  (\p.
    if recognizer (type_of_hyp (hyp_num_arg ()) p)
    then ApplyPattern (hd (children (proof_of_theorem pattern_name))) p
    else failwith `no`
  )
;;






let PatternAllIntro p =
  if `NIL` = fst (destruct_function (concl p)) then fail ;
  ( (\p. Refine (function_intro big_U (get_id_arg ())) p)
    ORELSE Intro
  ) p
;;


let RepeatDElimFor n i terms choices ids =
  set_d_tactic_args i terms choices ids ;
  letrec Aux n i =
    if n=0 then Idtac
    else CtdDElim i THENS (Hypothesis ORELSE (\p. Try (Aux (n-1) (number_of_hyps p)) p))    in
  Aux n i
;;

let RepeatCtdDElimFor n i =
  letrec Aux n i =
    if n=0 then Idtac
    else CtdDElim i 
         THENS (Hypothesis ORELSE (\p. Try (Aux (n-1) (number_of_hyps p)) p))   in
  Aux n i
;;



let ReplaceHyp i t = 
  Assert t THEN Try Hypothesis THEN Thinning [i]
;;


let define_lemmad_DIntro lemma_name recognizer =
  let T = Lemma lemma_name  in
  define_DIntro
    (\p. if recognizer (concl p) 
          then T p
          else failwith `no`
    )
;;



let define_lemmad_DElim lemma_names (remove_p: bool) recognizer =
  let T p = 
    let i = hyp_num_arg ()  in
    ( Same (map (\name. LemmaFromHyps name [i] []) lemma_names)
      THENS (if remove_p then Thinning [i] else Idtac)  
    ) p     in
  define_DElim
    (\p. if recognizer (type_of_hyp (hyp_num_arg ()) p)
          then T p
          else failwith `no`
    )
;;



let ids = words ;; 

let sum = accumulate (\x y. x+y) 0 ;;

letrec nodes p = 1 + (sum (map nodes (children p)) ? 0) ;;
