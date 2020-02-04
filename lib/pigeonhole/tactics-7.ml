
let Unsetify p =
   ChainHypTactics
      (map
         (\i. Try (SetElim i))
         (rev (upto 1 (number_of_hyps p)))
      )
      p
;;




let Autotactic =
      (Repeat
         (  Trivial
            ORELSE Member
            ORELSE Arith
            ORELSE (IfThenOnConcl (\c. exists is_arith_exp (fst (destruct_equal c)))
                                  SetElementIntro)
            ORELSE Intro
            ORELSE Unsetify
         )
      )
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
   map   (\x,A. add_prl_escapes
                  (if x=`NIL` then term_to_tok A else x^`: `^(term_to_tok A)))
         l
;;

let firstn n l =
   if n<0 then failwith `firstn: n must be nonnegative.` ;
   letrec aux n l = if n=0 then [] else hd l . aux (n-1) (tl l)   in
   aux n l ? failwith `firstn: n too large.`
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


let types_and_where_to_product types where_term =
   if null types then failwith `types_and_where_to_product: need types` ;
   letrec aux types =
      if length types = 1 then
         let [x,A] = types in make_some_where_term x A where_term
      else
         let (x,A).rest = types in make_some_term x A (aux rest)     in
   aux types
;;


let create_module_projector_def def_name lib_position projector_name thm_name number_of_parameters =
   let n = number_of_parameters  in
   let arg_types = function_type_to_arg_types (main_goal_of_theorem thm_name) (n+1) in
   let formals = n_ids (n+1)  in
   create_def def_name lib_position
      (`{` ^ (make_formal_arg_string (firstn n formals) (types_to_formal_descriptors (firstn n arg_types)))
           ^ `}` ^ projector_name ^ `(`
           ^ (make_formal_arg_string [last formals] (types_to_formal_descriptors [last arg_types]))
           ^ `)` )
      (make_ext_application thm_name (map make_var_term formals))
;;

let Tactic tok p = Refine (tactic tok) p ;;

let create_and_prove_thm name lib_position goal Tactic =
   create_theorem name lib_position (let pl,v = Tactic (make_sequent [] [] goal) in v pl)
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



letref moose=make_nil_term;;

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
   let projector_def_names = map (\x. x^`_`^name) projector_names in
   let projector_thm_names = map (\x. x^`_`) projector_def_names  in
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

   % Create the thm and def pair that form the definition of the data type term. %  
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
      else  let p_projections_so_far =
               map (\def. instantiate_def def (map make_var_term parameter_names @ [p]))
                   (firstn (i-1) projector_def_names) in
            let pi_range = subst_into_ith_component i p_projections_so_far in
            let thm_goal = extended_universalizer pi_range  in
            let T =
               Refine (explicit_intro (make_lambdas (parameter_names @ [typical_element_name])
                                                    (make_projection n i p)))
               THEN RepeatFor (m+1) MemberIntro
               THENW (ApplyToLastHyp (\i p. ExplodeTaggedProduct i (new_ids p) p)
                      THEN ExpandDefsInConcl (firstn (i-1) projector_thm_names)
                      THEN ReduceConcl)
               THEN Autotactic            in
            create_and_prove_thm (select i projector_thm_names) lib_position thm_goal T ;
            update_lib_position (select i projector_thm_names) ;
            create_module_projector_def (select i projector_def_names) lib_position (select i projector_names)
            (select i projector_thm_names) m ;
            update_lib_position (select i projector_def_names) ;
            create_remaining_projectors (i+1)   in
   create_remaining_projectors 1 ;

   % Create two utility theorems characterizing the data type. %
   let properties_thm_name = name_^`properties` 
   and projection_lemma_name = name_^`projection_lemma` in 
   let p_projections =
      map (\def. instantiate_def def (map make_var_term parameter_names @ [p]))
          projector_def_names in 
   let properties_thm_goal =
      extended_universalizer (make_squash_term (substitute where_term
                                                           (map (make_var_term o fst) component_types
                                                            com p_projections)))  
   and projection_lemma_goal =
      extended_universalizer (make_equal_term type [p; reverse_iterate_fun make_pair_term p_projections])   in
   let PropertiesTheoremTactic =
      Idtac
   and ProjectionLemmaTactic =
      Idtac    in 
   create_and_prove_thm properties_thm_name lib_position properties_thm_goal PropertiesTheoremTactic ;
   update_lib_position properties_thm_name ;
   create_and_prove_thm projection_lemma_name lib_position projection_lemma_goal ProjectionLemmaTactic ;
   update_lib_position projection_lemma_name 

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



