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










let ids = words ;; 

let sum = accumulate (\x y. x+y) 0 ;;

letrec nodes p = 1 + (sum (map nodes (children p)) ? 0) ;;



letrec InductionOn n k p =                                                     
  (let x,A,() = destruct_function (concl p) in                                 
   if x = n then                                                               
     Intro                                                                     
     THENW NonNegInduction (number_of_hyps p + 1) k                            
   else                                                                        
     Intro THENW InductionOn n k                                               
  ) p                                                                          
  ?                                                                            
  Idtac p                                                                      
;;                                                                             
                                                                               

let OnVar v T =                                                                
  let TryHyps p = T (find_declaration v p) p in                                
  letrec BeatConcl p =                                                         
    ( Intro                                                                    
      THENW ( \p. let n = number_of_hyps p in                                  
                  if v = id_of_hyp n p then T n p                              
                  else BeatConcl p )                                           
    ) p in                                                                     
  TryHyps ORELSE BeatConcl                                                     
;;                                                                             
                                                                               

let CaseHyp i p =                                                              
  if is_union_term (type_of_hyp i p) then                                      
    (Elim i THEN Thinning [i]) p                                               
  else failwith `CaseHyp: hyp not and "or" term`                               
;;                                                                             
                                                                               


let ComputeEquands =                                                           
  ComputeConclUsing                                                            
  (\c. let l,T = destruct_equal c in                                           
       make_equal_term T (map (make_tagged_term 0) l)                          
  )                                                                            
;;                                                                             

let ComputeEquandsFor n =                                                      
  ComputeConclUsing                                                            
  (\c. let l,T = destruct_equal c in                                           
       make_equal_term T (map (make_tagged_term n) l)                          
  )                                                                            
;;                                                                             


let AbstractConcl instance p =                                                 
( let x = undeclared_id p `x` in                                               
  Assert                                                                       
    (make_apply_term                                                           
      (make_lambda_term x                                                      
        (replace_subterm instance (mvt x) (concl p)))                          
      instance)                                                                
  THENL                                                                        
  [Idtac                                                                       
  ;ApplyToLastHyp (ComputeHypUsing (make_tagged_term 1))                       
   THEN Hypothesis                                                             
  ]                                                                            
) p                                                                            
;;                                                                             


let ExplicitIntro t = Refine (explicit_intro t) ;;                             

let InductionLemma                                                             
  lemma_name parameter base instance p                                         
  =                                                                            
FastAp                                                                         
( AbstractConcl instance                                                       
  THEN                                                                         
  LemmaUsing lemma_name [parameter; base]                                      
) p
;;






let unfold t =
  let f.args = decompose_application t in
  (no_extraction_compute o make_application) 
    ( (extracted_term_of_theorem o destruct_term_of_theorem) f . args )
;;

let tag_for_unfold name t = 
  let name_ = name^`_`  in
  let k = arity_of_def name in
  letrec aux t =
    let t' = map_on_subterms aux t in
    let f.args = decompose_application t  in
    ( if destruct_term_of_theorem f = name_ & length args = k then
        let (),n = unfold t in make_tagged_term (n+1) t'
      else fail
    ) ? t'  in
  aux t
;;

let UnfoldInConcl name =
  ComputeConclUsing (tag_for_unfold name)
;;

let UnfoldInHyp name =
  ComputeHypUsing (tag_for_unfold name)
;;

letrec remove_tags t = 
  map_on_subterms remove_tags ((snd o destruct_tagged) t ? t)
;;

let fold_and_tag name t =
  let name_ = name ^ `_`  in
  let k = arity_of_def name in
  let ids = map new_id (replicate void_goal_proof k)  in
  let pattern, n = 
    fast_ap (unfold o make_application) (make_term_of_theorem_term name_ . map mvt ids) in
  let f = make_term_of_theorem_term name_ in 
  letrec aux t =
    ( let bindings = match pattern t ids  in
      let args = map (lookup bindings) ids  in
      let folded_term = make_application (f . args)   in
      (make_tagged_term (n+1) o map_on_subterms aux) folded_term
    )
    ? map_on_subterms aux t   in
  aux t
;;

let FoldInConcl name p =
  let t = fold_and_tag name (concl p) in
( Assert (remove_tags t)
  THENL [Idtac; OnLastHyp (\i. Refine (direct_computation_hyp i t))]
) p
;;

let FoldInHyp name i p =
  let t = fold_and_tag name (type_of_hyp i p) in
( Assert (remove_tags t)
  THENL [Refine (direct_computation t); Idtac]
) p
;;


let ExpandProduct i =
  letrec ProductElim i =
    ( \p.
      let product_id = (fst o destruct_product o (type_of_hyp i)) p in
      Refine (product_elim i `NIL` `NIL`) p
      ?
      Refine (product_elim i product_id `NIL`) p
      ?
      Refine (product_elim i (undeclared_id_using p product_id)  `NIL`) p
    )
    THEN Thinning [i]   in

  let SetElim i p=
    ( let set_id = (fst o destruct_set o (type_of_hyp i)) p in
      ( Refine (set_elim i big_U `NIL`) 
        ORELSE
        Refine (set_elim i big_U set_id)
      )
      THEN IfThenOnHyp i (\(),A. A = type_of_hyp i p)  (Thinning [i]) 
    ) p in
    
  ComputeHyp i
  THEN 
  IfOnHyp i (is_product_term o snd)
    (ProductElim i THEN Repeat (OnLastHyp ProductElim) THEN Try (OnLastHyp SetElim))
    (\p. failwith `ExpandProduct: not a product term.`)
;;




let MultiAbstractConcl instances p =
  let ids = map (\x. undeclared_id p `x`) instances   in
  let lambda_body = 
    accumulate  
      (\t (x,t'). replace_subterm t' (mvt x) t)
      (concl p)
      (ids com instances) in
  let t = make_application (make_lambdas ids lambda_body . instances) in
( Assert t
  THENL                                                                        
  [Idtac                                                                       
  ;ApplyToLastHyp (ComputeHypUsing (make_tagged_term (length instances)))
   THEN Hypothesis                                                             
  ]                                                                            
) p                                                                            
;;                                                                             




let is_le_term t =
  (is_less_term o destruct_not) t
  ? false
;;

let make_le_term a b =
  make_not_term (make_less_term a b)
;;

let swap_pair (x,y) = y,x ;;

let destruct_le =
  swap_pair o destruct_less o destruct_not
;;

let first_relnand t = 
  if is_equal_term t then (first o fst o destruct_equal) t 
  if is_less_term t then  (fst o destruct_less) t
  if is_le_term t then (fst o destruct_le) t
  else (second o rev o decompose_application) t
;;

let second_relnand t = 
  if is_equal_term t then (second o fst o destruct_equal) t 
  if is_less_term t then  (snd o destruct_less) t
  if is_le_term t then (snd o destruct_le) t
  else (first o rev o decompose_application) t
;;

let swap_equands t = 
  let [t';t''],T = destruct_equal t in
  (make_equal_term T [t'';t'])
;;

% Only for equality and defined relations. %
let swap_relnands t =
  swap_equands t
  ?
  (make_application o rev o (\(a.b.l). b.a.l) o rev o decompose_application) t
;;

let replace_first_relnand t t' =
  if is_equal_term t then (let [a;b],T = destruct_equal t in make_equal_term T [t';b])
  if is_less_term t then make_less_term t' (second_relnand t)
  if is_le_term t then make_le_term t' (second_relnand t)
  else (make_application o rev o (\(a.b.l). a.t'.l) o rev o decompose_application) t
;;

let replace_second_relnand t t' =
  if is_equal_term t then (let [a;b],T = destruct_equal t in make_equal_term T [a;t'])
  if is_less_term t then make_less_term (first_relnand t) t'
  if is_le_term t then make_le_term (first_relnand t) t'
  else (make_application o rev o (\(a.b.l). t'.b.l) o rev o decompose_application) t
;;

let replace_both_relnands t t' t'' =
  if is_equal_term t then (let [a;b],T = destruct_equal t in make_equal_term T [t';t''])
  if is_less_term t then make_less_term t' t''
  if is_le_term t then make_le_term t' t''
  else (make_application o rev o (\(a.b.l). t''.t'.l) o rev o decompose_application) t
;;

let SwapEquandsInConcl  =
  (\p. Assert (swap_equands (concl p)) p)
  THEN Try Trivial
;;

let SwapRelnandsInConcl =
  SwapEquandsInConcl
  ORELSE
  (\p.
    Lemma ( ((\x. x^`sym`) o destruct_term_of_theorem o head_of_application o concl) p ) p
  )
;;

% Only for equality and defined relations.  For defined relations, it is assumed
  that the instance of the relation is an application headed by a term_of, whose 
  name, when suffixed with `sym`, gives the name of a symmetry theorem. 
%
let SwapRelnandsInHyp i p =
  ( Assert (swap_relnands (type_of_hyp i p))
    THENL [SwapRelnandsInConcl; Idtac]
  )
  p
;;

let last_hyp_type = (type_of_declaration o last o hypotheses) ;;

abstype generic_arg = term + (int + int) + (tok + tok)
  with a_term = abs_generic_arg o inl
  and a_hyp = abs_generic_arg o inr o inl o inl
  and a_rev_hyp = abs_generic_arg o inr o inl o inr
  and a_lemma = abs_generic_arg o inr o inr o inl
  and a_rev_lemma = abs_generic_arg o inr o inr o inr
  and term_of_generic_arg x =
        (outl o rep_generic_arg) x ? failwith `term_of_generic_arg`
  and hyp_of_generic_arg x =
        (outl o outl o outr o rep_generic_arg) x ? failwith `hyp_of_generic_arg`
  and rev_hyp_of_generic_arg x =
        (outr o outl o outr o rep_generic_arg) x ? failwith `hyp_of_generic_arg`
  and lemma_of_generic_arg x =
        (outl o outr o outr o rep_generic_arg) x ? failwith `lemma_of_generic_arg`
  and rev_lemma_of_generic_arg x =
        (outr o outr o outr o rep_generic_arg) x ? failwith `rev_lemma_of_generic_arg`
;;

% For goals of the form: >> x R' z, when left_to_right_p is true (false),
this tactic attempts to use the named lemma to step forward (backward)
from the left (right) relnand.  (Interpolator left_to_right_p) should do
the following (modulo Autotactic):

H, xRy >> xR'z --> >> yR''z  if left_to_right_p
H, yRz >> xR'z --> >> xR''y  otherwise

It should not leave any subgoals whose proof requires the above indicated
hypotheses and does not follow by Trivial.
%
let RelnStep (Interpolator: bool->tactic) left_to_right_p (arg: generic_arg) =

  let ApplyLemma p =
    let lemma_name, revp = 
      lemma_of_generic_arg arg, false ? rev_lemma_of_generic_arg arg, true  in
    let pattern_container = main_goal_of_theorem lemma_name in
    let relnand_to_match = 
      if left_to_right_p then first_relnand (concl p) else second_relnand (concl p) in
    let instantiators =
      if revp & left_to_right_p or not revp & not left_to_right_p then 
        match_part_in_context second_relnand pattern_container relnand_to_match p [] 
      else match_part_in_context first_relnand pattern_container relnand_to_match p []  in
    (InstantiateLemma lemma_name instantiators 
     THENS  (if revp then OnLastHyp (\i. SwapRelnandsInHyp i THEN Thinning [i]) else Idtac)
    ) p      in

  let ApplyHyp p =
    let i, revp = 
      hyp_of_generic_arg arg, false ? rev_hyp_of_generic_arg arg, true  in
    let pattern_container = type_of_hyp i p in
    let relnand_to_match = 
      if left_to_right_p then first_relnand (concl p) else second_relnand (concl p) in
    let instantiators =
      if revp & left_to_right_p or not revp & not left_to_right_p then 
        match_part_in_context second_relnand pattern_container relnand_to_match p [] 
      else match_part_in_context first_relnand pattern_container relnand_to_match p []  in
    (InstantiateHyp i instantiators 
     THENS  (if revp then OnLastHyp (\i. SwapRelnandsInHyp i THEN Thinning [i]) else Idtac)
    ) p      in

  let ExplicitlyInterpolate p =
    let t = term_of_generic_arg arg in
    let step =
      if left_to_right_p then replace_second_relnand (concl p) t
      else replace_first_relnand (concl p) t    in
    Assert step p in

  (\p. ApplyLemma p ? ApplyHyp p ? ExplicitlyInterpolate p % ORELSE has a PROGRESS in it % )
  THENS
  (Interpolator left_to_right_p THEN (Trivial ORELSE OnLastHyp (\i. Thinning [i])))

;;



let BasicInterpolator left_to_right_p p =
  let t = last_hyp_type p  and  t' = concl p  in
  if is_equal_term t & (is_less_term t' or is_le_term t' or is_equal_term t') 
     or (is_le_term t or is_less_term t) & (is_le_term t' or is_less_term t')
    then
    ( if left_to_right_p then Assert (replace_first_relnand t' (second_relnand t)) p
      else Assert (replace_second_relnand t' (first_relnand t)) p
    )
  if is_equal_term t then 
    (if left_to_right_p then SubstFor t p else SubstFor (swap_equands t) p)
  else 
    LemmaUsing 
      ( ((\x. x^`trans`) o destruct_term_of_theorem o head_of_application o concl) p )
      [if left_to_right_p then second_relnand t else first_relnand t]
      p
;;

let RelnStepR = RelnStep BasicInterpolator true ;;

let RelnStepL = RelnStep BasicInterpolator false ;;

let remove_last_char = implode o rev o tl o rev o explode ;; 




                                                
let RepeatApplyIntro p =
  letrec Aux i p = 
    if i = 1 then Idtac p else (EqualityIntro THENL [Aux (i-1); Idtac]) p in
  Aux ( (length o decompose_application o first_equand o concl) p ) p
;;

% Only for equality and defined relations.  Assumes the name of the congruence
  lemma is the name of the operation suffixed with an underscore and the name
  of the relation.  Incomplete implementation (not all constructors recognized
  yet). %
let Congruence p = 
  if is_equal_term (concl p) then (Progress RepeatApplyIntro ORELSE EqualityIntro) p
  else 
    let reln_name_ = (destruct_term_of_theorem o head_of_application o concl) p   in
    let relnand = first_relnand (concl p)   in
    let opn_name_ =
      if is_apply_term relnand then
        ( (destruct_term_of_theorem o head_of_application) relnand
          ? `apply_` )
      if is_cons_term relnand then `cons_`
      if is_pair_term relnand then `pair_`
      else failwith `term constructor not recognized yet`   in
    let congruence_lemma_name = opn_name_ ^ (remove_last_char reln_name_) in
    Lemma congruence_lemma_name p
;;

