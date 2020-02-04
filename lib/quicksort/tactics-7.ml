

let Unsetify p =
  ChainHypTactics
    (map
      (\i. Try (SetElim i))
      (rev (upto 1 (number_of_hyps p)))
    )
    p
;;


let UnSquash p =
  ChainHypTactics
    (map
      (\i. Try (SquashElim i))
      (rev (upto 1 (number_of_hyps p)))
    )
    p
;;



let Autotactic =
    (Repeat
      ( Trivial
        ORELSE Repeat Intro
        ORELSE UnSquash
        ORELSE Member
        ORELSE (\p. 
                let [t;t'],T = destruct_equal (concl p) in
                if is_universe_term T & simplify t = simplify t' then
                  (RepeatUntil is_arith_goal MemberIntro) p
                else fail
               )
        ORELSE (IfOnConcl
                  (\c. is_less_term c or is_union_term c or is_void_term c
                        or (is_equal_term c & is_int_term (snd (destruct_equal c)))
                        or exists is_arith_exp (fst (destruct_equal c)))
                  (Try SetElementIntro THENW (Try (Unsetify THEN Arith)))
                  Fail
               )
      )
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


let set_strong () = set_auto_tactic `refine (tactic \`StrongAutotactic\`)` ;;

let set () = set_auto_tactic `refine (tactic \`Autotactic\`)` ;;

let unset () = set_auto_tactic `Idtac` ;;

set () ;;



let Properties terms =
  let Aux t p =
    let n = number_of_hyps p   in
    let type = get_type p t in
    ChainHypTactics
      [Seq [make_equal_term type [t]] 
      ;ExposeProperties (n+1)
      ;Thinning [n+1]
      ]
      p     in
  ChainHypTactics (map Aux terms)
;;


% atom_eq not handled yet %
let DecisionTermCases terms_and_types =
  let Aux (t,T) =
    let [a;b;t1;t2] = subterms t  in
    let true_case, false_case =
      if is_int_eq_term t then 
        let u = make_equal_term make_int_term [a;b]  in
        u, make_not_term u
      else % assume int_less %
        let u = make_less_term a b in
        u, make_not_term u      in
    ChainHypTactics
      [Cases [true_case; false_case]
      ;ApplyToLastHyp 
        (\i. IfOnHyp i 
            (\x,H. H=true_case)
            (  Seq [make_equal_term T [t; t1]]
              THENL [ReduceDecisionTerm 1 true; Idtac] )
            (  Seq [make_equal_term T [t; t2]]
              THENL [ReduceDecisionTerm 1 false; Idtac] )
        )
      ]     in
  ChainHypTactics (map Aux terms_and_types)
;;



let CaseLemma name terms =
  ChainHypTactics
    [InstantiateLemma name terms
    ;ApplyToLastHyp (\i. Refine (union_elim i `NIL` `NIL`))
    ;ApplyToNthLastHyp 2 (\i. Thinning [i])
    ]
;;





let make_ext_application thm_name args =
  iterate_fun make_apply_term (make_term_of_theorem_term thm_name . args)
;;


let n_ids n = map (\i. `x`^(tok_of_int i)) (upto 1 n)
;;

let add_prl_escapes tok =
  iterate_fun
    concat
    (map (\ch.  if ch = `<` then `\\<`
            if ch = `>` then `\\>`
            if ch = `\\` then `\\\\`
            else ch )
        (explode tok))
;;



let types_to_formal_descriptors l =
  map (\x,A. add_prl_escapes
              (if x=`NIL` then term_to_tok A else x^`: `^(term_to_tok A)))
      l
;;



% x1:A1->...->xarity:Aarity->B  |--->  [x1,A1;...;xarity,Aarity].
  If the arity argument is negative then it is taken instead to be maximal.
%
let function_type_to_arg_types type arity =
  let domains = fst (explode_function type) ? []  in
  let max_arity = length domains   in
  if arity < 0 then domains
  if arity > max_arity then failwith `function_types_to_arg_types: arity too large.`
  else firstn arity domains
;;


let concat_using_commas (l: tok list) =
  let l = iterate_fun append (map (\x. (explode x)@[`,`]) l)  in
  implode (firstn (length l - 1) l) 
;;


let make_formal_arg_string formals descriptors =
  concat_using_commas (map (\x,d. `<`^x^`:`^d^`>`) (formals com descriptors))
;;


let create_ext_application_def def_name lib_position display_name thm_name arity =
  if arity=0 then create_def def_name lib_position display_name
                    (make_term_of_theorem_term thm_name)
  else
    let arg_types = function_type_to_arg_types (main_goal_of_theorem thm_name) arity in
    let n = length arg_types   in
    let formals = n_ids n   in
    let arg_string = make_formal_arg_string formals (types_to_formal_descriptors arg_types)   in
    create_def def_name lib_position (display_name^`(`^arg_string^`)`)
      (make_ext_application thm_name (map make_var_term formals))
;;



let types_to_universalizer types =
  letrec aux types t =
    if null types then t
    else  let (x,A).rest = types in
        make_all_term x A (aux rest t)      in
  aux types
;;

let is_true_term t =
  is_int_term t or is_atom_term t or 
  (let [t'],T = destruct_equal t in is_int_term T & is_natural_number_term t')  
  ?
  false
;;


let types_and_where_to_product types where_term =
  if null types then failwith `types_and_where_to_product: need types` ;
  letrec aux types =
    if length types = 1 then
      let [x,A] = types in 
        if is_true_term where_term then A
        else make_some_where_term x A where_term
    else
      let (x,A).rest = types in make_some_term x A (aux rest)     in
  aux types
;;


letref projector_separator = `.` ;;

let create_module_projector_def def_name lib_position projector_name projector_ext_thm_name module_type =
  create_def 
    def_name 
    lib_position
    ( (make_formal_arg_string [`z`] (types_to_formal_descriptors [`NIL`, module_type]))
      ^ projector_separator ^ projector_name
    )
    (make_ext_application projector_ext_thm_name [make_var_term `z`])
;;

let Tactic tok p = Refine (tactic tok) p ;;

let create_and_prove_thm name lib_position goal Tactic =
  create_theorem name lib_position (let pl,v = Tactic (make_sequent [] [] goal) in v pl)
;;


let define_projector_redex names =
  define_redex
    (\t. (  let f,a = destruct_apply t  in
            member (destruct_term_of_theorem f) names  &  is_pair_term a
         ) ? false
    )
;;


let make_sequence lbracket rbracket separator members =
  let exploded_separator = explode separator  in
  letrec build_char_list members = 
    if null members then explode rbracket
    if length members = 1 then explode (hd members) @ explode rbracket
    else let h.t = members in explode h @ exploded_separator @ build_char_list t    in
  implode (explode lbracket @ build_char_list members)
;;



let make_ml_tok x = `\``^x^`\`` ;;

let make_ml_tok_list l =
  make_sequence `[` `]` `;` (map make_ml_tok l)
;;



let make_ml_function_application (f: tok) (args: tok list) = 
  accumulate (\acc arg. acc ^ ` (` ^ arg ^ `)`)
             f
             args
;;

let make_ml_top_level_let lhs rhs =
  `let ` ^ lhs ^ ` = ` ^ rhs ^ ` ;; `
;;



let create_module_arg_names =
`(name: tok)
 (lib_position: tok)
 (parameter_types: (tok#term) list)
 (component_types: (tok#term) list)
 (projector_names: tok list)
 (typical_element_name: tok)
 (level: int)
 (where_term: term)`
;;


let concat_tok_list l =
  implode (accumulate append [] (map explode l))
;;


let create_module 
    (name: tok)
    (lib_position: tok)
    (parameter_types: (tok#term) list)
    (component_types: (tok#term) list)
    (projector_names: tok list)
    (typical_element_name: tok)
    (level: int)
    (where_term: term)   =
  let parameter_names = map fst parameter_types and component_names = map fst component_types in
  let universalizer = types_to_universalizer parameter_types  in
  let m = length parameter_types  and  n = length component_types   in
  let name_ = name^`_`    in
  let projector_def_names = map (\x. name^`_`^x) projector_names in
  let projector_ext_thm_names = map (\x. x^`_`) projector_def_names  in
  let projector_type_thm_names = map (\x. x^`__`) projector_def_names  in
  if exists (\x. x=`NIL`) parameter_names then
    failwith `create_module: parameter names must be non-NIL.` ;
  if not n = length projector_names then
    failwith `create_module: wrong number of projector names.` ;      
  letref lib_position = lib_position  in
  let update_lib_position ob_name = lib_position := `after `^ob_name   in
  let subst_into_ith_component i terms =
    substitute  (snd (select i component_types))
                (map make_var_term (firstn (i-1) component_names)  com terms)  in
  let p = make_var_term typical_element_name   in

  % Create the thm and def pair that form the definition of the module type-term. %  
  let thm_goal = universalizer (make_universe_term level)  in
  let T =
    Refine (explicit_intro (make_lambdas parameter_names
                             (types_and_where_to_product component_types where_term)))
    THEN Tactic `Autotactic`   in
  create_and_prove_thm name_ lib_position thm_goal T ;
  update_lib_position name_ ;
  create_ext_application_def name lib_position name name_ m ;
  update_lib_position name ;

  % Create the thm and def pairs that form the definitions of the projector terms %
  let type = instantiate_def name (map make_var_term parameter_names)  in
  let extended_universalizer = types_to_universalizer (parameter_types @ [typical_element_name, type])  in
  let new_ids p = map (\(). undeclared_id p `p`) (upto 1 n)   in
  letrec create_remaining_projectors i =
    if n<i then ()
    else
      let ext_thm_name = (select i projector_ext_thm_names) in
      create_and_prove_thm ext_thm_name lib_position make_object_term
        (Refine (explicit_intro (make_lambda_term typical_element_name (make_projection n i p)))
         THEN Refine (object_equality_member make_nil_term)) ;
      update_lib_position ext_thm_name ;
      create_module_projector_def (select i projector_def_names) lib_position (select i projector_names)
        ext_thm_name type ;
      update_lib_position (select i projector_def_names) ;
      let p_projections_so_far =
        map (\def. instantiate_def def [p])
            (firstn (i-1) projector_def_names) in
      let projection_type = subst_into_ith_component i p_projections_so_far in
      let type_thm_goal =
        extended_universalizer
          (make_equal_term projection_type [instantiate_def (select i projector_def_names) [p]])  in
      let ProveTypeThm =
        ExpandDefsInConcl [select i projector_ext_thm_names] THEN Tactic `Autotactic`    in
      create_and_prove_thm (select i projector_type_thm_names) lib_position type_thm_goal ProveTypeThm ;
      update_lib_position (select i projector_type_thm_names) ;
      create_remaining_projectors (i+1)   in
  create_remaining_projectors 1 ;

  % Create a theorem which gives the hidden properties of the module, if any. %
  (if not is_true_term where_term then
    let properties_thm_name = name_^`properties` in
    let p_projections =
      map (\def. instantiate_def def [p])
         projector_def_names in 
    let properties_thm_goal =
      extended_universalizer
        (make_squash_term (substitute where_term
                            (map (make_var_term o fst) component_types  com  p_projections)))  in
    let PropertiesTheoremTactic =
      RepeatFor (m+1) Intro
      THENW (ApplyToLastHyp (\i p. ExplodeTaggedProduct i (new_ids p) p)
             THEN OnLastHyp SetElim
             THEN ExpandDefsInConcl projector_ext_thm_names
             THEN ReduceConcl
             THEN SquashIntro)
      THEN Autotactic            in
    create_and_prove_thm properties_thm_name lib_position properties_thm_goal PropertiesTheoremTactic ;
    update_lib_position properties_thm_name
    ; 
    ()
  ) ;

  % Create an ML object which will: add to the redex environment recognizers for projector/tuple pairs;
     
  %
  create_ml_object (`add_`^name_^`tactics`) lib_position 
    (concat_tok_list
      [make_ml_function_application
        `define_projector_redex` [make_ml_tok_list projector_ext_thm_names]
      ;` ;; `
      ;make_ml_function_application
        `define_AbsElim`
        [make_ml_function_application
          `ExplodeModule` [make_ml_tok name_; make_ml_tok_list projector_def_names]
        ]
      ;` ;;`
      ]
    )
  ;
  ()
;;


% The argument should be a term which is a module instance. (e.g. a member of Group). %
let ModuleProperties t p =
  let T = get_type p t ? failwith `ModuleProperties: could not guess type of ` ^ term_to_tok t  in
  let l = decompose_application T in
  ( let module_name_ = destruct_term_of_theorem (hd l)  in
    InstantiateLemma (module_name_^`properties`) (tl l @ [t]) p
  )
  ? failwith `ModuleProperties: type not a module type`
;;



let name_of_defined_term t =
  destruct_term_of_theorem (head_of_application t)
;;


let ExplodeModule module_name_ projector_def_names i p =
  if not module_name_ = name_of_defined_term (type_of_hyp i p) then fail ;
  let x = id_of_hyp i p in
  if `NIL` = x then failwith `ExplodeModule: type must have tag.` ;
  let projections = map (\def. instantiate_def def [mvt x]) projector_def_names in
  let projection_typings = map (\proj. make_equal_term (get_type p proj) [proj]) projections  in
  ( Seq projection_typings
    THENS Try ( InstantiateLemma (module_name_ ^ `properties`) (tl (decompose_application (type_of_hyp i p)))
                THENS OnLastHyp (\i. IfThenOnHyp i (\x,H. is_set_term H) (SetElim i))
              )
  )
  p
;;


letref AbsElim_list = []: (int->tactic) list ;;


let undo_AbsElim_definitions () =
  AbsElim_list := []
;;


let define_AbsElim (T: int->tactic) =
  AbsElim_list := T . AbsElim_list
;;


let AbsElim i p =
  Some (map (\T. T i) AbsElim_list) p
;; 



% ˆx1. ˆx2. ... ˆxn. t   ---> [x1; x2; ... xn], t
  If the arity argument is negative then it is taken instead to be maximal.
%
letrec destruct_multi_lambda t n =
  if n=0 or not is_lambda_term t then
    [],t
  else
    let x,t' = destruct_lambda t in
    let vars,t'' = destruct_multi_lambda t' (n - 1)   in
    (x.vars),t''
;;


% Gross hack. %
let get_type_assuming assums pf t =
  let p = last (fst (Refine (let vars,types = split assums in seq types vars) pf))  in
  get_type p t
;;


let get_lambda_type t lambda_var_types p =
  let vars,body = destruct_multi_lambda t (length lambda_var_types) in
  implode_function
    (vars com lambda_var_types)
    (get_type_assuming (vars com lambda_var_types) p body)
;;

let make_in_term t T = 
  make_equal_term T [t]
;;



let pretty_up_mono_result_term t =
  let fix_not t =
    ( let t' = destruct_not t in
      if is_less_term t' then
        (let a,b = destruct_less t' in instantiate_def `le` [b;a])
      else make_not_term t'
    ) 
    ? t     in
  if is_and_term t then let a,b = destruct_and t in make_and_term (fix_not a) (fix_not b)
  else fix_not t
;;


let Mono i op j p =
  let n = number_of_hyps p in
  ( Refine (monotonicity op i j)
    THEN
    \p.
      let n' = number_of_hyps p   in
      ( Seq (map (pretty_up_mono_result_term  o (\i. type_of_hyp i p)) (upto (n+1) n'))
        THEN (Hypothesis ORELSE Thinning (upto (n+1) n'))
  
      ) p
    
  ) p
;;




let MonoWithL t op i p =
  let n = number_of_hyps p  in
  ( Seq [t]
    THENL [Idtac; Mono (n+1) op i THEN Thinning [n+1]]
  ) p
;;

let MonoWithR i op t p =
  let n = number_of_hyps p  in
  ( Seq [t]
    THENL [Idtac; Mono i op (n+1) THEN Thinning [n+1]]
  ) p
;;


% For compatability with older libraries. %
let RemoveHypRedices = ReduceHyp ;;
let RemoveConclRedices = ReduceConcl ;;
let RemoveRedices = Reduce ;;



let BringHyp i p = 
  let x,H = destruct_hyp i p  in
  ( Seq [make_function_term x H (concl p)] 
    THENL [Thinning [i]
        ;if x=`NIL` then OnLastHyp Elim else OnLastHyp (\i. ElimOn i (mvt x))
        ]
    THEN Try Trivial
  ) p
;;

let BringHypThen i T p =
  let n = number_of_hyps p  in
  (BringHyp i THEN IfThen (\p'. number_of_hyps p' < n) T) p
;;

let BringHyps hyps = RepeatHypTactic BringHyp (rev hyps) ;;

let BringHypsThen hyps T p =
  let n = number_of_hyps p  in
  (BringHyps hyps THEN IfThen (\p'. number_of_hyps p' < n) T) p
;;



% function_type should be the type of the head of the application sequence. %
let ApIntroUsing function_type p =  
  let revd_args = rev (tl (decompose_application (first_equand (concl p)))) in
  if null revd_args then failwith `ApIntroUsing: no application.` ;
  letrec build_using_types revd_args =
    if length revd_args = 1 then [function_type]
    else let l = build_using_types (tl revd_args) in
         let x,A,B = destruct_function (compute (hd l)) in
         (substitute B [mvt x, (hd revd_args)]) . l in
  letrec Aux using_types p =
    if null using_types then Idtac p
    else 
      ( Refine (function_equality_apply (hd using_types))
        THENL [Aux (tl using_types); Idtac]
      ) p   in
  Aux (build_using_types revd_args) p
;;


let big_U_term = make_universe_term big_U ;;

let tag_equands tags t =
  let equands,T = destruct_equal t  in
  make_equal_term T (map (\t,i. make_tagged_term i t) (equands com tags))
;;


% All argument lists must have the same length.
  >> B(a_bar)  BY MultiSubst z_bar B b_bar T_bar [z_bar means z1,...,zn]
    >> a1=b1 in T1
    ...
    >> an=bn in Tn
    >> B(b_bar)
    z1:T1,...,zn:Tn >> B in U17
%
let MultiSubst z_bar B b_bar T_bar p =

  let bindings = match B (concl p) z_bar  in
  let a_bar = map (lookup bindings) z_bar in
  let B_of_b_bar = substitute B (map mvt z_bar  com  b_bar) in

  ( SubstConcl B_of_b_bar
    THEN
    IfThenOnConcl (\c. not c = B_of_b_bar)
      ( % Prove B(a_bar) = B(b_bar) by asserting
          (\ z_bar. B(z_bar)) (a_bar) = (\ z_bar. B(z_bar)) (b_bar) %
        Assert (let f = make_lambdas z_bar B in
                make_equal_term big_U_term
                  [iterate_fun make_apply_term (f.a_bar); iterate_fun make_apply_term (f.b_bar)]
               )
        THENL
        [ % Prove assertion by introing using T_bar, leaving the a_bar = b_bar equalities %
          ApIntroUsing (implode_function (z_bar com T_bar) big_U_term)
        ; % Use assertion by computing it to B(a_bar) = B(b_bar) %
          OnLastHyp (ComputeHypUsing (let n = length z_bar in tag_equands [n;n]))
          THEN Refine equality
        ]
      )
  ) p
;;




let matches pattern instance ids =
  (match pattern instance ids; true) ? false
;;



let RewriteConclWithLemmasOver (name_and_over_id_list: (tok#tok) list) over_term p =
(  let over_ids = map snd name_and_over_id_list   in
   let over_vars = map mvt over_ids in
   let over_bindings = match over_term (concl p) over_ids   in
   let n=number_of_hyps p in
   let replacements_with_types, lemma_instantiators =
      split
         (map (\name, over_id.
               let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
               let instance = lookup over_bindings over_id  in
               let instantiation_terms = 
                  map (lookup (match e instance ids)) ids      in
               let subst_list = (map (\x. make_var_term x) ids) com instantiation_terms  in
               (substitute e' subst_list , substitute T subst_list)
               , InstantiateLemma name instantiation_terms
              )
              name_and_over_id_list
         )        in
   let replacements, types = split replacements_with_types  in
   ChainHypTactics lemma_instantiators
   THENS (MultiSubst over_ids over_term replacements types 
          THEN IfThenOnConcl (\c. matches over_term c over_ids) (ThinToEnd (n+1))
         )
)  p
;;



let RewriteConclWithLemmas names p =
   letrec aux remaining_names partial_over_term collected_names_and_ids =
      if null remaining_names then partial_over_term, collected_names_and_ids
      else 
        (let over_id = undeclared_id p `z`   in
         let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem (hd names))  in
         let newer_over_term = 
            replace_subterm
               (get_contained_instance partial_over_term e ids)
               (make_var_term over_id)
               partial_over_term         in
         aux remaining_names newer_over_term ((hd names, over_id).collected_names_and_ids)
        )
        ? aux (tl remaining_names) partial_over_term collected_names_and_ids     in
   let over_term, names_and_ids = aux names (concl p) []  in       
   RewriteConclWithLemmasOver names_and_ids over_term p
;;


