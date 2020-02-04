%-*- Tab-width: 2 -*-%

%  This file (and only this file) contains ML objects which have run-time 
dependencies on objects in Doug Howe's (monster-mega)-library. %


let concat_and_fail x y = failwith (concatl [y; `; `; x]) ;;

letrec is_canonical_atom_list t =
  is_nil_term t or is_cons_term t & is_token_term (first (subterms t)) 
  & is_canonical_atom_list (second (subterms t))
;; 

let is_canonical_mtype t =
( let a,b = destruct_pair t in is_canonical_atom_list a & is_token_term b)
? false
;; 

let destruct_canonical_list t =
  letrec aux t = 
    if is_nil_term t then [] 
    if is_cons_term t then
      (let a,b = destruct_cons t in a . aux b)
    else fail in
  aux t ? failwith `destruct_canonical_list`
;; 


% Return a list of nuprl atoms. %
let destruct_canonical_atom_list t =
  map (assert is_token_term) (destruct_canonical_list t)
;; 

letrec make_list elements = 
  if null elements then make_nil_term 
  else make_cons_term (hd elements) (make_list (tl elements))
;; 

let destruct_canonical_mtype t =
  let a,b = destruct_pair t in
  destruct_canonical_atom_list a, assert is_token_term b
  ? failwith `destruct_canonical_mtype`
;; 

letrec destruct_tuple t =
  (let a,b = destruct_pair t in a . destruct_tuple b)
  ? [t]
;; 

let make_tuple terms = reverse_iterate_fun make_pair_term terms ;;

let make_ext ext_name = instantiate_def `e` [mvt ext_name] ;; 

let make_ext_ap ext_name args = 
  make_ap (make_ext ext_name . args)
;; 


let destruct_inf t =
  destruct_pair (destruct_inl (compute t)) 
;;                        

let destruct_ine t =
  let [a;b;A] = destruct_tuple (destruct_inl (destruct_inr (compute t))) in
  a,b,A
;; 

let destruct_ini t =
  let [i;a;b] = destruct_tuple (destruct_inl (destruct_inr (destruct_inr (compute t)))) in
  i,a,b
;; 

let destruct_inn t =
  destruct_inr (destruct_inr (destruct_inr t)) 
;; 

let is_inf t = (destruct_inf t; true) ? false ;; 
let is_ine t = (destruct_ine t; true) ? false ;; 
let is_ini t = (destruct_ini t; true) ? false ;; 
let is_inn t = (destruct_inn t; true) ? false ;; 

let inf () = make_ext `inf` ;; 
let ine () = make_ext `ine` ;; 
let ini () = make_ext `ini` ;; 
let inn () = make_ext `inn` ;; 

let make_lifted_eq x y A = make_ext_ap `ine` [x; y; A] ;; 

let make_lifted_fun_ap f args = make_ext_ap `inf` [f; make_list args] ;; 

let make_lifted_i_pair i x y = make_ext_ap `ini` [i; x; y] ;; 

let make_lifted_int n = make_ext_ap `inn` [n] ;; 

let lookup_type type_env A =
  lookup type_env A 
  ? failwith `lookup_type: couldn't find ` ^ term_to_tok A
;; 

let lift_eos lift_term t expected_mtype type_env =
  assert (\t. destruct_term_of_theorem (head_of_application t) = `eos_`) t 
  ? failwith `NA` ;
  let [(); A; equands] = decompose_ap t in
  let x,y = destruct_pair equands in
  let mA = lookup_type type_env A in
  let t1,l1 = lift_term x mA and t2,l2 = lift_term y mA in
  make_lifted_eq t1 t2 mA, union l1 l2
;; 

letrec collect_ext_names terms =
  accumulate union [] 
    (map (\t. [destruct_term_of_theorem t] ? collect_ext_names (subterms t))
         terms)
;; 

let lookup_fun fun_env f =
  let same_fun =
    if is_term_of_theorem_term f then
      (\f'. hd (collect_ext_names [f']) = destruct_term_of_theorem f ? false)
  else $= f in
  snd (find (same_fun o fst) fun_env)
  ? failwith `lookup_fun: couldn't find ` ^ term_to_tok f
;;  

% 0-ary funaps handled by lift_curried_fun_ap %
let lift_normal_fun_ap lift_term t expected_mtype fun_env =
  assert (is_term_of_theorem_term o fst o destruct_apply) t ? failwith `NA` ;
  let f, t' = destruct_apply t in
  let args = destruct_tuple t' in
  let mf, arg_types, () = lookup_fun fun_env f in
  if not length arg_types = length args then 
    failwith concatl [`wrong number of args to mfun `; 
       term_to_tok mf; ` in `; term_to_tok t] ;
  let lifted_args, constant_lists = 
    split (map (uncurry lift_term) (args com arg_types)) in
  make_lifted_fun_ap mf lifted_args, accumulate union [] constant_lists
;; 

let lift_curried_fun_ap lift_term t expected_mtype fun_env =
  assert is_term_of_with_args t ? failwith `NA` ;
  let f.args = decompose_ap t in
  let mf, arg_types, () = lookup_fun fun_env f in
  if not length arg_types = length args then 
    failwith concatl [`wrong number of args to mfun `; 
       term_to_tok mf; ` in `; term_to_tok t] ;
  let lifted_args, constant_lists = 
    split (map (uncurry lift_term) (args com arg_types)) in
  make_lifted_fun_ap mf lifted_args, accumulate union [] constant_lists
;; 


let lift_i_pair lift_term t expected_mtype =
  failwith `NA`
;; 

let lift_int lift_term t expected_mtype =
  assert is_integer_term t ? failwith `NA` ; 
  make_lifted_int t, []
;; 
  

let lift_misc lift_term t expected_mtype type_env fun_env =
  failwith `NA`
;; 

let lift_constant lift_term t expected_mtype fun_env =
( let mf, arg_types, () = lookup_fun fun_env t in
  if not length arg_types = 0 then fail
  else make_lifted_fun_ap mf [], []
) ?
( let constant = make_token_term (term_to_tok t) in
  make_lifted_fun_ap constant [], [constant, expected_mtype, t]
)
;; 

% Compute the lifted term and the new atoms required for the lift.
The new atoms are nuprl triples consisting of the atom token, the token
for its mtype, and the term that is the atom's value.
%
letrec (lift_term t expected_mtype type_env fun_env): term # ((term#term#term) list) =
  letrec aux t expected_mtype =
    ( lift_misc aux t expected_mtype type_env fun_env 
      ?? [`NA`]
      ( lift_eos aux t expected_mtype type_env
        ?? [`NA`]
        ( lift_normal_fun_ap aux t expected_mtype fun_env
          ?? [`NA`]
          ( lift_curried_fun_ap aux t expected_mtype fun_env
            ?? [`NA`]
            ( lift_i_pair aux t expected_mtype fun_env
              ?? [`NA`]
              ( lift_int aux t expected_mtype)))))
    ) ? lift_constant aux t expected_mtype fun_env  in
  aux t expected_mtype
;; 

let Term0_injections =
  map make_term_of_theorem_term ``inf_ ine_ ini_ inn_``
;; 

let mdef_of_mfun mfun = mfun ^ `__m` ;; 

let destruct_squash t =
  assert is_squash_term t ; (snd o snd o destruct_set) t 
;; 

% for an mterm with unexpanded injections %
let add_mdef t =
  let f . args = decompose_ap t in
  if f = inf () then 
    ( ( let name = mdef_of_mfun (destruct_token (hd args)) in 
        name, permute_args_for_def_instantiation name 
                (destruct_canonical_list (second args))
      )
      ? 
      ( if is_nil_term (second args) then `constant`, [hd args] else fail )
      ? `inf`, args
    )
  if f = ine () then `ine`, args
  if f = ini () then (let [i;x;y] = args in `ini`, [y;i;x])
  if f = inn () then `inn`, args
  if f = mvt `alpha` & null args then `a`, []
  if is_token_term f & null args then `tok`, [mvt (destruct_token f)]
  if f = make_term_of_theorem_term `term_val_` then `term_val`, args
  if is_squash_term t then `squash`, [destruct_squash t]
  else fail
;;

let add_mdefs t = add_display_form add_mdef t ;; 

let is_injection t = is_inl_term t or is_inr_term t ;; 

let fold_and_tag_inf t =
  let f,args = destruct_pair (destruct_inl t) in
  make_tagged_term 0 (make_ext_ap `inf` [f;args])
;;                        

let fold_and_tag_ine t =
  let [a;b;A] = destruct_tuple (destruct_inl (destruct_inr t)) in
  make_tagged_term 0 (make_ext_ap `ine` [a;b;A])
;; 

let fold_and_tag_ini t =
  let [i;a;b] = destruct_tuple (destruct_inl (destruct_inr (destruct_inr t))) in
  make_tagged_term 0 (make_ext_ap `ini` [i;a;b])
;; 

let fold_and_tag_inn t =
  let n = destruct_inr (destruct_inr (destruct_inr t)) in
  make_tagged_term 2 (make_ext_ap `inn` [assert ($not o is_injection) n])
;; 

letrec fold_and_tag_term_injections t =
  map_on_subterms fold_and_tag_term_injections 
    (fold_and_tag_inn t ? (fold_and_tag_ini t ? (fold_and_tag_ine t 
      ? (fold_and_tag_inf t ? t))))
;; 

let FoldTermInjectionsInConcl =
  ReverseComputeConclUsing fold_and_tag_term_injections
;; 

let FoldTermInjectionsInHyp i =
  ReverseComputeHypUsing fold_and_tag_term_injections i
;; 


let ElideConcl = 
  ComputeConclUsing (\t. instantiate_trivial_def `elide` t)
;; 

let ElideHyp = 
  ComputeHypUsing (\t. instantiate_trivial_def `elide` t)
;; 

let RepeatAndI = RepeatUntil ($not o is_and_term o concl) I ;; 

% For efficiency. %
let make_ugly_conjunction terms = 
  reverse_iterate_fun (\x y. make_product_term `NIL` x y) terms
;; 

% Conjoin the indicated hyps and thin them, adding the conjunction
as a new (last) hyp. 
%
let CombineHyps hypnos p =
( let conjuncts =
    map (\i. let x,A = destruct_declaration (select i (hyps p)) in
             if not x=`NIL` then failwith `CombineHyps` else A) 
        (rev hypnos)  in
  Assert (make_ugly_conjunction conjuncts) THENL
  [OnHyps RepeatAndE hypnos THEN RepeatAndI THEN Trivial
  ;Thinning hypnos
  ]
) p
;; 

let marking_fun () = make_ext `mark` ;; 

% Use the lib object "mark_" to put a marker token on a term. %
let make_marked_term mark t =
  make_ext_ap `mark` [make_token_term mark; t]
;;

let mark_of_marked_term t = 
  ( let [a;b;c] = decompose_ap t in 
    assert ($= (marking_fun ())) a ; destruct_token b
  ) ? failwith `mark_of_marked_term`
;; 

let term_of_marked_term t = 
  ( let [a;b;c] = decompose_ap t in 
    assert ($= (marking_fun ())) a ; c
  ) ? failwith `mark_of_marked_term`
;; 


let is_marked_term t = (mark_of_marked_term t ; true) ? false ;;

let has_marking mark t = (mark_of_marked_term t = mark) ? false ;; 

let tag_for_unmarking = make_tagged_term 4 ;; 



let MarkHyp mark =
  ReverseComputeHypUsing (tag_for_unmarking o make_marked_term mark)
;; 

let UnmarkHyp i = 
  IfOnHyp (is_marked_term o snd) (ComputeHypUsing tag_for_unmarking i) Fail i
;; 

let find_first_position P l =
  letrec aux i l = if P (hd l) then i else aux (i+1) (tl l) in
  aux 1 l ? failwith `find_first_position`
;; 

let find_marked_hyp mark p = 
  find_first_position (has_marking mark o type_of_declaration) (hyps p)
  ? failwith `find_marked_hyp: no hyp has mark " ` ^ mark ^ ` ".`  
;; 

let type_of_marked_hyp mark p = 
  term_of_marked_term (h (find_marked_hyp mark p) p) 
;; 

let OnMarkedHyp mark (T: int->tactic) p =
  let i = find_marked_hyp mark p in
  (UnmarkHyp i THEN T i) p
;; 


let MakeLiftStore p =
( CombineHyps (map (C find_marked_hyp p) ``env_store subenv_store term_store``)
  THEN OnLastHyp (\i. MarkHyp `lift_store` i THEN ElideHyp i)
) p
;; 

let ExpandLiftStore = OnMarkedHyp `lift_store` RepeatAndE ;; 

let ExpandEnvStore = 
  OnMarkedHyp `env_store` RepeatAndE
  ORELSE (ExpandLiftStore THEN OnMarkedHyp `env_store` RepeatAndE)
;;

let ExpandSubenvStore = 
  OnMarkedHyp `subenv_store` RepeatAndE
  ORELSE (ExpandLiftStore THEN OnMarkedHyp `subenv_store` RepeatAndE)
;;

let ExpandTermStore = 
  OnMarkedHyp `term_store` RepeatAndE
  ORELSE (ExpandLiftStore THEN OnMarkedHyp `term_store` RepeatAndE)
;;


let hyp_types p = map type_of_declaration (hyps p) ;; 

let is_term_val t =
  (let [val;();()] = decompose_ap t in `term_val_` = destruct_term_of_theorem val)
  ? false
;; 

let term_of_term_val t =
  if is_term_val t then last (decompose_ap t) else failwith `term_of_term_val`
;; 

% Assumes meta-terms use the injections. %
let meta_term_occurs_maximally mt t =
  letrec aux t =
    if mt = t then fail
    if member (hd (decompose_ap t)) Term0_injections then ()
    else (map aux (subterms t); ()) in
  (aux t; false) ? true
;; 

let UpdateTermStore obsolete_terms new_hyps =
  let really_obsolete_terms p =
    let evald_terms = 
      collect term_of_term_val ((destruct_squash (concl p) ? concl p) . hyp_types p) in
    filter ($not o C member evald_terms) obsolete_terms in
  let thinned_term_store p =
    let term_store = 
      destruct_conjunction (type_of_marked_hyp `term_store` p) in
    filter (\T. not exists (C meta_term_occurs_maximally T) (really_obsolete_terms p)) 
           term_store in
  let AssertNewTermStore p = 
    Assert (make_ugly_conjunction (new_hyps @ thinned_term_store p)) p  in
  let ThinJunk p = Thinning (map (C find_position (hyp_types p)) new_hyps) p in
  Try ExpandLiftStore THEN
  AssertNewTermStore THENL 
  [ExpandTermStore THEN RepeatAndI THEN Trivial
  ;OnMarkedHyp `term_store` Thin THEN OnLastHyp (MarkHyp `term_store`) THEN ThinJunk
  ]
;; 

let is_trivial_lifted_term t =
  (let [a;b;c] = decompose_ap t in a = inf () & is_nil_term c)
  ? false
;; 

let lift_hyps hyps type_env fun_env: ((int#term) list) # ((term#term#term) list) =
  let beat_hyp (i, H) =
    let x,A = destruct_declaration H in
    if not x=`NIL` then fail ;
    let lifted_A, constants = lift_term A (make_token_term `Prop`) type_env fun_env in
    (i, assert ($not o is_trivial_lifted_term) lifted_A), constants in
  let lifted_hyps, constants = 
    split (collect beat_hyp (upto 1 (length hyps) com hyps)) in
  lifted_hyps, accumulate union [] constants
;; 



let make_constant_list env constants =
  make_list (map (\a,A,v. make_ext_ap `make_constant` [env; a; A; v]) constants)
;; 

let alpha () = instantiate_def `a` [] ;; 


let Define id term type p =
( let id = hd (new_ids_from_ids [id] p) in
  let membership_assertion = make_equal_term type [term] in
  let assertion = 
    % id:type. id=term in type => concl %
    make_function_term id type 
      (make_function_term `NIL` (make_equal_term type [mvt id; term]) (concl p)) in
  Seq [membership_assertion; assertion]
  THENL [Id; I THENW I THEN IfThenOnConcl ($= (concl p)) (Thin (number_of_hyps p + 1)); 
         OnLastHyp (EOn term) THENS OnLastHyp E THEN Trivial]
) p
;; 

% Leftmost-reduce until t is an n-tuple, and return a list of the components %
letrec expand_tuple n t = 
  if n<2 then [t]
  else let a,b = destruct_pair (fast_ap compute t) in a . expand_tuple (n-1) b
;; 

% Expand a list as far as possible. %
letrec expand_list t =
  (let a,b = destruct_cons (fast_ap compute t) in a . expand_list b)
  ? []
;; 

let dissect_tenv tenv = 
  map ((\[mA;A;()]. A, open_eval mA true []) o expand_tuple 3) (expand_list tenv) 
;;  

let dissect_fenv fenv = 
  let ev t = open_eval t true [] in
  let beat_tuple [mf;mt;f;()] =
    f, ev mf, (let x,y = destruct_pair (ev mt) in expand_list x, y) in
  map (beat_tuple o expand_tuple 4) (expand_list fenv) 
;; 

% Compute from the env and from the initial envs an a-list mapping
types to mtypes, an a-list mapping functions to (mfun, mtype domain, 
mtype co-domain)'s, and a list of all contained object-level ext names.
%
let dissect_env env =
  let tenv = 
    dissect_tenv (extracted_term_of_theorem `g0_`) 
    @ dissect_tenv (make_projection 2 1 env) in
  let fenv = 
    dissect_fenv (extracted_term_of_theorem `d0_`) 
    @ dissect_fenv (make_projection 2 2 env) in
  let types_and_funs = map fst tenv @ map fst fenv in
  let ext_names = collect_ext_names types_and_funs in
  tenv, fenv, ext_names
;; 

let dissect_envs envs = 
  accumulate 
    (\(x,y,z) env. let x',y',z' = dissect_env env in 
                   union x' x, union y' y, union z' z) 
    ([],[],[]) envs
;; 


let ConsistentEnvs = 
  (IfThenOnConcl (is_nil_term o snd o destruct_cons o last o decompose_ap) EvalConcl)
  ORELSE
  (\p. First (current_ConsistentEnvs_additions ()) p)
;; 

let ConstantTypings constant_exts =
  IfThenOnConcl (\p. `Constant` = ext_name (destruct_list (eq_type p)))
    ( RepeatUntil ($not o is_list_term o eq_type o concl) MemberI THENW MemberI
      THEN (\p. if not is_membership_goal p then EvalConcl p
                if ext_name (eq_type (concl p)) = `tos` ? false then 
                  EvalConclExcept constant_exts p
                else Id p
           )  
    )
;; 

let SetUpMainEnv constants envs constant_exts p =
( let a = alpha () in
  let env_list = make_list envs in
  let appended_env_list = make_ext_ap `append_env_list` [env_list] in
  let constant_list = make_constant_list appended_env_list constants in
  let main_env = 
    substitute main_env_template [mvt `l`, env_list; mvt `cl`, constant_list] in
  let assertion = 
    substitute env_hyp_template [mvt `l`, env_list; mvt `cl`, constant_list] in
  Assert assertion 
  THENO (RepeatAndI THEN If is_membership_goal (Try (ConstantTypings constant_exts))
                                               (Try ConsistentEnvs))
  THENS Define (dv a) main_env (make_ext `Env`) 
  THENS ( let n = number_of_hyps p in 
          CombineHyps [n+1; n+3] THEN OnLastHyp (MarkHyp `env_store`)
        )
) p
;; 

% Compute the main env. variable, the main env, the env list, and the constant list. %
let get_env_store p =
  let env_store = 
    type_of_marked_hyp `env_store` p
    ? term_of_marked_term
        (find ($= `env_store` o mark_of_marked_term)
              (destruct_conjunction (type_of_marked_hyp `lift_store` p))) in
  let conjuncts = destruct_conjunction env_store in
  let [var; main_env] = equands (hd conjuncts) in
  let [envs] = equands (second conjuncts) in
  let [constants] = equands (fourth conjuncts) in
  [var; main_env; envs; constants]
;; 

% not very accurate %
let is_lifted_sequent p = 
  (find_marked_hyp `lift_store` p; true) ? false 
;; 

let main_env_var = hd o get_env_store ;; 
let main_env = second o get_env_store ;; 
let env_list = third o get_env_store ;; 
let constant_list = fourth o get_env_store ;; 

let SetUpSubenvAssertions envs p =
( let [main_env_var; (); env_list; constant_list] = get_env_store p in
  Assert (make_ugly_conjunction (map (\a. substitute subenv_hyp_template [mvt `a1`, a; mvt `a2`, main_env_var])
                                envs))  
  THENL [ExpandEnvStore
         THEN InstLemma `subenv_of_append_list_lemma` [main_env_var; env_list; constant_list]
         THENS OnLastHyp (EvalHypOnly (defs `all_elements`))
         THEN Try Trivial
        ;OnLastHyp (MarkHyp `subenv_store`)
        ]
) p
;; 


let SetUpTermWfAssertions lifted_hyps lifted_concl constant_exts p =
( let main_env_var . main_env . () = get_env_store p in 
  let inst t = substitute term_hyp_template [mvt `alpha`, main_env_var; mvt `t`, t] in
  let BeatWf = LemmaUsing `wf_term_eval_lemma` [main_env] THEN Try Trivial
               THEN EvalConclExcept constant_exts in
  let BeatMType = LemmaUsing `term_mtype_eval_lemma` [main_env] THEN Try Trivial
                  THEN EvalConclExcept constant_exts in
  Assert (make_ugly_conjunction (map inst (lifted_concl . lifted_hyps))) THENL
  [ExpandEnvStore THEN RepeatAndI
   THENM IfOnConcl ($not o is_equal_term) BeatWf BeatMType
  ;OnLastHyp (MarkHyp `term_store`) THEN MakeLiftStore
  ]
) p
;; 

let OnMarkedHyps marks Tac = Every (map (\mark. OnMarkedHyp mark Tac) marks) ;; 

let EvalToEqConclFirst constant_exts i =
  EvalConclExcept constant_exts THEN 
  (Trivial ORELSE EvalHypExcept constant_exts i THEN Try Trivial)
;; 


let EvalToEqHypFirst constant_exts i =
  EvalHypExcept constant_exts i THEN 
  (Trivial ORELSE EvalConclExcept constant_exts THEN Try Trivial)
;; 

let SetUpLiftedHyps lifted_hyps constant_exts p =
( let main_env_var . main_env . () = get_env_store p in 
  let Beat = LemmaUsing `term_val_eval_lemma_1` [main_env] THEN Try Trivial
             THEN OnLastHyp (EvalToEqConclFirst constant_exts) in
  let DoHyp (i,lifted_term) = 
    Assert (add_mdefs (substitute lift_template [mvt `alpha`, main_env_var; mvt `t`, lifted_term]))
    THENL [ExpandTermStore THEN ExpandEnvStore THEN Beat; Thin i] in
  Same (map DoHyp (rev lifted_hyps))
) p
;; 

let SetUpLiftedConcl lifted_concl constant_exts p =
( let main_env_var . main_env . () = get_env_store p in 
  let concl_val = 
    substitute lift_template [mvt `alpha`, main_env_var; mvt `t`, lifted_concl] in
  let Beat = ExpandEnvStore THEN ExpandTermStore THEN
             InstLemma `term_val_eval_lemma_2` [main_env_var; main_env; lifted_concl] 
             THEN Try Trivial THEN OnLastHyp (EvalToEqHypFirst constant_exts) in
  if is_squash_term (concl p) then 
    Assert (add_mdefs (make_squash_term concl_val)) THENS (SquashI THEN OnLastHyp SquashE THEN Beat)
  else Assert (add_mdefs concl_val) THENS Beat
) p
;; 




let SquashLiftedConcl p =
  if is_squash_term (concl p) & is_term_val (destruct_squash (concl p)) then Id p
  if not is_term_val (concl p) then failwith `SquashLiftedConcl`
  else 
  ( let main_env_var . main_env . () = get_env_store p in 
    let t = term_of_term_val (concl p) in
    InstLemma `triv_term_truth_2` [main_env_var; main_env; t]
    THEN IfThenOnConcl is_decide_term (EvalConcl THEN I)
    THENO (ExpandEnvStore THEN ExpandTermStore THEN Try Trivial THEN (SquashI THEN Hypothesis))
    THENS (OnLastHyp BackThruHyp THEN OnLastHyp Thin THEN ComputeConclUsing add_mdefs)
  ) p
;; 


let LiftUsing envs =
  let Lift p =
  ( let type_env, fun_env, ext_names = dissect_envs envs in
    let lifted_hyps, l1 = lift_hyps (hyps p) type_env fun_env in
    let lifted_concl, l2 = 
      lift_term (destruct_squash (concl p) ? (concl p)) (make_token_term `Prop`) type_env fun_env in
    let constant_exts = % should thin these out %
      union ext_names
       (collect_ext_names (concl p . map (\i,(). type_of_hyp i p) lifted_hyps)) in
    Same
    [SetUpMainEnv (union l1 l2) envs constant_exts
    ;SetUpSubenvAssertions envs
    ;SetUpTermWfAssertions (map snd lifted_hyps) lifted_concl constant_exts
    ;SetUpLiftedHyps lifted_hyps constant_exts
    ;SetUpLiftedConcl lifted_concl constant_exts
    ]
  ) p in
  Lift THENM Try SquashLiftedConcl
;; 


% Uses the theorem `special_ap_`, whose ext is "\f x. f(x)" %
let abstract_and_block term P p =
  let x = undeclared_id p `x` in
  let subterm = find_in_term P term in
  make_ap
    [make_term_of_theorem_term `special_ap_`
    ;make_lambda_term x (replace_subterm subterm (mvt x) term)
    ;subterm
    ]
;; 

let AbstractAndBlockConcl P p =
  ReverseComputeConclUsing 
    (\t'. make_tagged_term 4 (abstract_and_block t' P p))
    p
;; 

let AbstractAndBlockHyp P i p =
  ReverseComputeHypUsing 
    (\t'. make_tagged_term 4 (abstract_and_block t' P p))
    i
    p
;; 

let UnblockAndUnabstractConcl =
  ComputeConclUsing (make_tagged_term 4)
;; 

let UnblockAndUnabstractHyp i =
  ComputeHypUsing (make_tagged_term 4) i
;; 

let EvalSubtermOfConcl exceptions_constant_p exceptions P =
  AbstractAndBlockConcl P
  THEN
  (exceptions_constant_p  
    => EvalConclExcept (`special_ap_` . exceptions)
    |  EvalConclOnly (remove_if ($= `special_ap_`) exceptions) ) 
  THEN
  UnblockAndUnabstractConcl
;; 

let EvalSubtermOfHyp exceptions_constant_p exceptions P i =
  AbstractAndBlockHyp P i
  THEN
  (exceptions_constant_p  
    => EvalHypExcept (`special_ap_` . exceptions) i
    |  EvalHypOnly (remove_if ($= `special_ap_`) exceptions) i) 
  THEN
  UnblockAndUnabstractHyp i
;; 

let EvalSubtermAux i exceptions_constant_p exceptions P =
  i=0 => EvalSubtermOfConcl exceptions_constant_p exceptions P
      |  EvalSubtermOfHyp exceptions_constant_p exceptions P i
;; 

let EvalExceptAux i l =
  i=0 => EvalConclExcept l | EvalHypExcept l i
;; 

let EvalOnlyAux i l =
  i=0 => EvalConclOnly l | EvalHypOnly l i
;; 


let is_canonical_meta_term t =
  is_inr_term t or is_inl_term t or 
  member (head_of_application t) Term0_injections
;; 

let is_term_fun_redex name_ t =
( let l = decompose_ap t in
  destruct_term_of_theorem (hd l) = name_
  & is_canonical_meta_term (last l)
) ? false
;; 

let termrec_fun_internals_to_beat =
  map append_underscore 
  ( ``all_elements wf_fun_ap@ map vals_in_mtypes@ com term_list_val``
    @ ``hd tl wf_eq_ap@ wf_i_pair@ Term0_cases inf ine ini inn``
    @ ``list_rec_1``
  )
;; 

let is_length_redex t =
( let [a;b] = decompose_ap t in
  destruct_term_of_theorem a = `length_` & is_canonical_term b
) ? false
;; 

let is_term_list_val_redex t =
( let [a;b;c;d] = decompose_ap t in
  destruct_term_of_theorem a = `term_list_val_` & is_canonical_term d
) ? false
;; 


let is_lookup_redex t =
( let l = decompose_ap t in 
  is_token_term (last l) & 
  member (destruct_term_of_theorem (hd l))
  ( ``type_atom_ mtype_ type_atom_val_ fun_atom_ type_atom_val_i_ mfun_val_`` )
) ? false
;; 

let is_term_mtype_redex t =
  letrec aux u = 
    is_canonical_meta_term u & 
    (is_inf u & is_token_term (fst (destruct_inf u)) 
     or is_ini u & (let i,x,y = destruct_ini u in aux x)
     or is_ine u or is_inn u) in
  let l = decompose_ap t in
  (destruct_term_of_theorem (hd l) = `term_mtype_` ? false)
  & aux (last l) 
;; 


let SimplifyTermPredicatesAux i envs p =
( let (),(), ext_constants = dissect_envs envs in
  (Repeat o First o map Progress)
  [ EvalOnlyAux i []
  ; EvalSubtermAux i true [] is_term_mtype_redex
  ; EvalSubtermAux i true [] is_length_redex
  ; EvalSubtermAux i true ext_constants is_lookup_redex
  ; EvalSubtermAux i false ``term_list_val_ list_rec_1_`` is_term_list_val_redex
  ; EvalSubtermAux i true ext_constants (is_term_fun_redex `term_type_`)
  ; UnrollRecOccAux i (is_term_fun_redex `term_val_`)
    THEN EvalOnlyAux i termrec_fun_internals_to_beat
  ; UnrollRecOccAux i (is_term_fun_redex `wf_term@_`)
    THEN EvalOnlyAux i termrec_fun_internals_to_beat
  ]
) p
;; 


let SimpConclTermPreds = SimplifyTermPredicatesAux 0 ;; 
let SimpHypTermPreds envs i = SimplifyTermPredicatesAux i envs ;;

let move_val_through_fun_aps t =
  let [term_val;env;term] = decompose_ap t in
  if not term_val = make_ext `term_val` then fail ;
  let term_val t = make_ext_ap `term_val` [env;t] in
  let mfun_val t = make_ext_ap `mfun_val` [env;t] in
  letrec aux t = 
    ( let [inf;f;args_blob] = decompose_ap t in
      let args = destruct_canonical_list args_blob in
      if null args then mfun_val f 
      else make_apply_term (mfun_val f) (make_tuple (map aux args))
    ) ? term_val t in
  aux term
;; 

% implemented only for fun-aps %
let ComputeTermVal t T i =
  if i = 0 then 
    SubstFor (make_equal_term T [t; move_val_through_fun_aps t])
  else
    SubstForInHyp (make_equal_term T [t; move_val_through_fun_aps t]) i
;; 


let mttt = make_term_of_theorem_term ;;

let is_var_term_in_mtype t =
  (let [a;b;c;d] = decompose_ap t in a = mttt `term_in_mtype_` & is_var_term c)
  ? false
;; 

let is_unfolded_term_in_mtype t =
  (let [f;();val;()] = decompose_ap t in 
   let x,y = destruct_pair val in
   f = mttt `val_member_` & ext_name x = `term_mtype` & ext_name y = `term_val`
  )
  ? false
;; 

let is_wf_var_term t =
  (let [a;b;c] = decompose_ap t in a = mttt `wf_term@_` & is_var_term c)
  ? false
;; 

let ThinDuplHyps p =
  letrec aux i leftward_hyps remaining_hyps =
    (let (i,H).l = remaining_hyps in
     let x,A = destruct_declaration H in
     if x=`NIL` & member A leftward_hyps then i . aux (i+1) (A . leftward_hyps) l
     else aux (i+1) (A . leftward_hyps) l
    )
    ? [] in
  Thinning (aux 1 [] (upto 1 (number_of_hyps p) com hyps p)) p
;; 


let LemmaToRewrite EqProver p =
( let [t],T = destruct_equal (concl p) in
  let env = snd (destruct_apply T) in
  let env_exts = collect_ext_names [env] in
  let ApplyRewriteLemma =
    First (map Lemma ``rewrite_from_1eqn rewrite_from_2eqn rewrite_from_3eqn``)
    THENM SquashI THENM Repeat CanonicalI in
  let NormalizeSubst =
    EvalConclExcept (defs `wf_term@ env_append eq_term_val` @ env_exts) in
  let Simplify =
    UnfoldInConcl `eq_term_val` THEN SimpConclTermPreds [env] 
    THEN OnLastHyp (SimpHypTermPreds [env]) THEN OnLastHyp RepeatAndE
    THEN Repeat CanonicalI THEN Try Trivial in
  let ThinJunk p =
  ( let junk_p H = 
      let x,A = destruct_declaration H in
      x=`NIL` & not (is_unfolded_term_in_mtype A or is_wf_var_term A 
                      or (ext_name A = `cst_envs` ? false)) in
    Thinning (collect (\i,H. assert junk_p H; i) 
                      (upto 1 (number_of_hyps p) com hyps p)) 
    THEN ThinDuplHyps
  ) p           in
  let AdjustHyps =
    OnEveryHyp (\i p. if `val_member` = ext_name (h i p) then 
                      Try (FoldInHyp ``term_in_mtype`` i) p else Id p) 
    THEN OnEveryHyp (\i. Try (FLemma `term_in_mtype_char` [i] 
                         THENS OnLastHyp (SimpHypTermPreds [env]))) in
  ApplyRewriteLemma 
  THENM (NormalizeSubst THEN I 
         THENM (Simplify THEN ThinJunk THENM AdjustHyps
                THEN IfThenOnConcl (\t. `eos` = ext_name t ? false) EqProver))
) p
;; 

let is_rewrite_membership_goal p =
  (mttt `Rewrite_` = fst (destruct_apply (eq_type (concl p))))
  ? false
;; 

let WithFailurePrefix message T p = T p ?\id failwith (message^`; `^id) ;; 

let type_from_sequent i p = 
  if i=0 then concl p 
  else select i (hyp_types p)
;; 

let is_rewrite_type t = 
  (let [a;b] = decompose_ap t in `Rewrite_` = destruct_term_of_theorem a)
  ? false
;; 

let ext_name_ t = destruct_term_of_theorem (head_of_application t) ;; 

let ext_name_of_member_ p = 
( let [t],T = destruct_equal (concl p) in
  ext_name_ t
) ? failwith `ext_name_of_member_`
;; 

let is_binary_equality t = 
  (let [();()],() = destruct_equal t in true) ? false
;; 

let is_def name arity t = 
  let h.l = decompose_application t in
  length l = arity & (name ^ `_`) = destruct_term_of_theorem h
;; 

let is_mtac_type T = 
  is_def `Rewrite` 1 T or is_def `Complete` 1 T
;; 

let env_of_mtac_type T =
  assert is_mtac_type T ;
  snd (destruct_apply T)
;; 

let is_mtac_membership p = 
( let T = eq_type (concl p) in
  is_mtac_type T
) ? false 
;; 

let DecrementULevel i p =
( let j = destruct_universe (eq_type (concl p)) in
  Refine (cumulativity (j-i))
) p ? failwith `DecrementULevel`
;; 
  
let SubstInEqType t t' A p =
( SubstConclType (replace_subterm t t' (eq_type (concl p))) THENL 
  [DecrementULevel 1 THEN SubstFor (make_equal_term A [t;t'])
  ;Id
  ]
) p
;; 


let MTacMember p =
( if not is_mtac_membership p then fail ;
  let in_lift = is_lifted_sequent p in
  let env_var . env . () = 
    in_lift => get_env_store p | [make_nil_term; make_nil_term] in
	let ShrinkEnv p = 
	(	if not is_mtac_membership p then fail ;
		let [t],T = destruct_equal (concl p) in
    if not env_var = env_of_mtac_type T then fail ;
    let T' = get_type p t in
    % only for Rewrite so far %
		LemmaUsing `Rewrite_mono` [env_of_mtac_type T']
	) p in		
  let Expand p =
  ( if in_lift 
    then ExpandEnvStore THEN ExpandSubenvStore THEN OnMarkedHyp `term_store` ElideHyp
    else Id
  ) p in
  let Simple p = 
    If is_mtac_membership
      (RepeatApIUsing (main_goal_of_theorem (ext_name_of_member_ p)))
      Fail
      p in
  let Poly p = 
    If is_mtac_membership
      (Lemma (ext_name_of_member_ p ^ `_`))
      Fail
      p  in
  let SubstType p = 
    if is_mtac_membership p & in_lift & is_subterm env (first_equand (concl p)) 
    then SubstInEqType env_var env (make_ext `Env`) p
    else fail in
  let Subenv p =
    if not in_lift or not `subenv` = ext_name (concl p) then fail ; 
    if is_subterm env (concl p) 
    then SubstFor (make_equal_term (make_ext `Env`) [env; env_var]) p
    else Lemma `subenv_refl` p in  
  Expand THEN 
  Repeat (ShrinkEnv ORELSE Simple ORELSE Poly ORELSE SubstType ORELSE Subenv ORELSE Trivial) 
) p
;; 

let AddMDefsAux i p = 
( if i=0 then Assert (add_mdefs (concl p)) THEN Try Hypothesis
  else Assert (add_mdefs (h i p)) THEN Try Hypothesis THEN Try (Thin i)
) p
;; 

let FailWith message : tactic = \p. failwith message ;; 

% Depends on InstLemma's numbering + ordering of subgoals. %
let RewriteAux f i p =
( let env_var . real_env . () = get_env_store p in
  let f' = substitute f [env_var, real_env] in
  let T = type_from_sequent i p in
  let t = term_of_term_val (destruct_squash T ? T) in
  let f'_ap = make_apply_term f' t in
  let n = number_of_hyps p in
  let UseLemmaConclusion =
    % if s(y) = f'(t) .   &   &   & (val(,t) <=> val(,y)) >>   % 
    OnLastHyp (EvalSubtermOfHyp true [] ($= f'_ap)) THEN
    OnLastHyp (\i. FoldTermInjectionsInHyp i THEN CHThen RepeatAndE i) THEN
    OnLastHyp (IfThenOnHyp (is_true_term o snd) (FailWith `rewrite failed`)) THEN
    (if i=0 then OnLastHyp E THEN Try Trivial
            else OnNthLastHyp 2 E THEN Try (SquashI THEN Trivial)
    ) THEN
    OnLastHyp (\j. AddMDefsAux (i=0 => 0 | j)) THEN
    Thinning [n+4; n+5] % the <=> branches % THEN
    (if 0<i then Thin i else Id) THEN
    (\p. UpdateTermStore [t] 
           (firstn 3 (i=0 => rev (hyp_types p) | tl (rev (hyp_types p)))) p
    ) THEN
    MakeLiftStore THEN
	  (i=0 => Id | Try Unhide)  in
  SquashLiftedConcl THEN
  ( InstLemma `rewrite_ap_lemma` [env_var; f'; t] THENS
    UseLemmaConclusion THENL
    [% >>  in Env % % proved by InstLemma %
     % >> f' in Rewrite() % MTacMember
    ;% >> t in Term0 % ExpandTermStore THEN Trivial
    ;% >> (wf(,t)) % ExpandTermStore THEN (Trivial ORELSE (SquashI THEN Trivial))
    ;% >> mtype(,t)="Prop" % ExpandTermStore THEN Trivial
    ;Id
    ] 
  )
) p
;; 


let ApplyCompleteTac f p =
( let env_var . real_env . () = get_env_store p in
  let f' = substitute f [env_var, real_env] in
  let hyps = collect term_of_term_val (hyp_types p) in
  SquashLiftedConcl THEN
  LemmaUsing `complete_ap_lemma` [f'; make_list hyps] THEN
  IfThenOnConcl is_decide_term (EvalConcl THEN I) THEN
  Try Trivial THEN CC THEN
  IfOnConcl (\c. is_def `Complete` 1 (eq_type c) ? false) 
    MTacMember
    ( ExpandTermStore THEN
      IfThen ($not o is_membership_goal) (Repeat (HeadReduceConcl THEN Try SimpleI)) THEN
      Try Trivial 
    )
) p
;; 


% Immune to hypothesis reordering. %
let OnHypTypes (T: int -> tactic) hypnums p =
	let types = map (C h p) hypnums in
	let T' hyp_term p =	T (find_position hyp_term (hyp_types p)) p in	
  Same (map T' types) p
;;  

let lifted_hyps p =
	filter (\i. is_term_val (h i p)) (upto 1 (number_of_hyps p))
;; 

let ApplyAuxEverywhereOnLiftedSequent Aux p =
(	OnHypTypes Aux (lifted_hyps p)
  THENS Aux 0
) p
;; 

let RewriteConcl f = RewriteAux f 0 
and RewriteHyp  = RewriteAux 
and Rewrite f = ApplyAuxEverywhereOnLiftedSequent (RewriteAux f) ;;
