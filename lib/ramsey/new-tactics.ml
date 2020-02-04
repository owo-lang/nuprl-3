letrec BackchainWith Tactic =

  let AtomizeConcl =
    REPEAT (IfOnConcl (\c. is_function_term c or is_and_term c)
                      (I THENG OnLastHyp RepeatAndE)
                      Fail) in

  letrec Aux (history: (term#term) list) =
    let AuxAux = 
      ApplyToAHyp 
      (\i p. (let A = h i p and C = concl p in
              if member (C,A) history then Fail 
              else BackThruHyp i THENM Aux ((C,A) . history)
             ) p)  in
    Try Hypothesis THEN 
    (AuxAux ORELSE (Progress AtomizeConcl THENW AuxAux)
            ORELSE Tactic)  in

  OnEveryHyp RepeatAndE THEN Aux []
;;

let Backchain = BackchainWith Fail ;;

let Contradiction = 
  Assert make_void_term THENL
  [Try Backchain;OnLastHyp E]
;;

let EOnThin Eterm n = EOn Eterm n THEN Thin n ;;

let EThin n = E n THEN Thin n ;;
					     
let ThinDependingHyps id p =
  Thinning (depending_hyp_nums p (find_declaration id p)) p
;;

let RepeatExt = Repeat (Ext THEN WeakAutotactic) ;;

let OrCases = Complete (ILeft THEN WeakAutotactic)
               ORELSE Complete (IRight THEN WeakAutotactic) ;;

let MonoFromHyps op p =
( let hlist = upto 1 (number_of_hyps p) in
  let l = filter (\x. is_less_term (h x p) or is_function_term (h x p)) hlist in
  let tries = flat (map(\y. map (\x.x,y) l) l) in
  letrec ap ll =
    if ll = [] then Fail
    else let f = fst (hd ll) and s = snd (hd ll) in
      if (f = s) then ap(tl ll)
    else Complete (Mono (fst (hd ll)) op (snd (hd ll)) THEN Autotactic) ORELSE ap (tl ll)
  in ap tries
) p ;;

% Finite Set Theory -- General Tactics %

letref FS_autotactic_additions = []: (tok#tactic) list ;;

let add_to_FS_autotactic name tac =
  FS_autotactic_additions := update_named_list name tac FS_autotactic_additions;
  ()
;;

let current_FS_autotactic_additions () = map snd FS_autotactic_additions ;;

let FS_autotactic =
  (\p. First (current_FS_autotactic_additions ()) p)
;;

let FSTactic = FS_autotactic ;;

let Equals x p =
(  let eqlist = filter is_equal_term (map type_of_declaration (hyps p)) in
   let add1 = filter (\y.(first_equand y = x)) eqlist in
   let add2 = filter (\y.(second_equand y = x)) eqlist in
       remove_prior_duplicates ((map second_equand add1) @ (map first_equand add2))
)  ;;

letrec trans_eq eq_list try_list p =
  if try_list = [] then eq_list
  else
    let x = hd try_list in
    if not (member x eq_list) then
      let new_try_list = remove_prior_duplicates (tl try_list @ (Equals x p)) in
      let new_eq_list = x.eq_list in
      trans_eq new_eq_list new_try_list p
    else trans_eq eq_list (tl try_list) p
;;

let EqContradiction p = 
( let l = filter is_equal_term (map type_of_declaration (hyps p)) in
  let sl = map swap_equands l in
  letrec do_assert l =
    if l = [] then Id
    else Assert (hd l) THEN do_assert (tl l) in
      do_assert sl THENO Trivial THEN Contradiction
) p ;;

let delete l x = filter (\y. not (x = y)) l ;;

let FSEqMember p =
(  let f, x = destruct_apply (concl p) in
   letrec do_ap l =
     if l = [] then Fail
     else Complete (SubstFor (make_equal_term (get_type p x) [x;hd l] )
       THEN Autotactic) ORELSE do_ap (tl l) in
         do_ap (delete (trans_eq [] [x] p) x)
) p ;;

let destruct_tri_ap t =
  let a,b = destruct_apply t in
  let c,d = destruct_apply a in
  let e,f = destruct_apply c in
  e,f,d,b
;;

let tri_1 t = fst t;;
let tri_2 t = fst (snd t);;
let tri_3 t = fst (snd (snd t));;
let tri_4 t = snd (snd (snd t));;

let FSAddCharGoal p = 
( let f,A,s,x = destruct_tri_ap (concl p) in
  let f1,A1,s1,x1 = destruct_tri_ap s in
  if not `fs_add` = term_to_tok f1
    then Fail
    else Decide (make_equal_term (get_type p x1) [x1;x]) THEN
      Try Trivial THENM Try (Lemma `fs_add_char`) THENM
       (Complete (ILeft THEN WeakAutotactic) ORELSE IRight)
) p ;;

let FSDelCharGoal p =
	      ( let f,A,s,x = destruct_tri_ap (concl p) in
  let f1,A1,s1,x1 = destruct_tri_ap s in
  if not `fs_del` = term_to_tok f1
    then Fail
    else Lemma `fs_del_char` THEN TRY Trivial THEN I  THENL
       [I THEN Try (COMPLETE (EqContradiction THEN WeakAutotactic)); Try Trivial]   
) p ;;

let FSUnionCharGoal p = 
( let f,A,s,x = destruct_tri_ap (concl p) in
  let f1,A1,s1,x1 = destruct_tri_ap s in
  if not `fs_union` = term_to_tok f1
    then Fail
    else Lemma `fs_union_char` THENM Try OrByHyp
) p ;;

let FSHypDel p =
( let f,A,s,x  = destruct_tri_ap (concl p) in
  let l = rev (upto 1 (number_of_hyps p) com (map type_of_declaration (hyps p))) in
  let lf = filter (\y.(`fmember` = term_to_tok (head_of_application (snd y)))) l in
  let eq_membs = trans_eq [] [x] p ? [x] in
  let leqx = filter (\y.(member ((tri_4 o snd) y) eq_membs))
                    (map (\y.(fst y,(destruct_tri_ap o snd) y)) lf)  in
  let leqs = filter (\y.(s = (tri_3 o  snd) y & `fs_del` = term_to_tok ((tri_1 o snd) y)))
                  (collect (\y.(fst y,(destruct_tri_ap o tri_3 o snd) y)) leqx) in 
  let n  = fst (hd leqs) in  HypChar `fs_del_char` n 
) p ;;

let FSHypAdd p =
( let f,A,s,x  = destruct_tri_ap (concl p) in
  let l = rev (upto 1 (number_of_hyps p) com (map type_of_declaration (hyps p))) in
  let lf = filter (\y.(`fmember` = term_to_tok (head_of_application (snd y)))) l in
  let eq_membs = trans_eq [] [x] p ? [x] in
  let leqx = filter (\y.(member ((tri_4 o snd) y) eq_membs))
                    (map (\y.(fst y,(destruct_tri_ap o snd) y)) lf)  in
  let leqs = filter (\y.(`fs_add` = term_to_tok ((tri_1 o snd) y)))
                    (collect (\y.(fst y,(destruct_tri_ap o tri_3 o snd) y)) leqx) in 
  let ha = hd leqs in
  if member (tri_4 (snd ha)) eq_membs then Fail
  else  HypChar `fs_add_char` (fst ha) THENS OnLastHyp EThin THENS Try (Complete 
    (EqContradiction THEN WeakAutotactic))
) p ;;

let FSEqUnion p =
( let f,A,s,x  = destruct_tri_ap (concl p) in
  let l = rev (upto 1 (number_of_hyps p) com (map type_of_declaration (hyps p))) in
  let lf = filter (\y.(`fs_eq` = term_to_tok (head_of_application (snd y)))) l in
  let n = fst (hd lf) in
  FLemma `eq_union_char` [n] THEN Try Trivial THEN Thin n THENS OnLastHyp (EOnThin x) 
  THENS OnLastHyp EThin THEN Try (Complete OrCases)
) p ;;

let UnfoldAndElim t p =
( let l = rev (upto 1 (number_of_hyps p) com (map type_of_declaration (hyps p))) in
  let lf = filter (\y.(t = term_to_tok (head_of_application (snd y)))) l in
  letrec RecE rl =
    if rl = [] then Id
    else EThin (fst (hd rl)) THEN RecE (tl rl) in
      RecE lf
) p ;;

let FSHypSubset p =
( let f,A,s,x  = destruct_tri_ap (concl p) in
  let l = rev (upto 1 (number_of_hyps p) com (map type_of_declaration (hyps p))) in
  let lf = filter (\y.(`fsubset` = term_to_tok (head_of_application (snd y)))) l in
  letrec Instantiate rl =
    if rl = [] then Id
    else EOnThin x (fst (hd rl)) THEN Instantiate (tl rl) in
      Instantiate lf
) p;; 


%add_to_FS_autotactic `FSHypSubset` (IfOnConcl (\c. (ext_name c) =
`fmember`) (UnfoldAndElim `fs_eq` THEN FSHypSubset) Fail) ;;%

add_to_FS_autotactic `FSUnionCharGoal` (IfOnConcl (\c. (ext_name c) =
`fmember`) FSUnionCharGoal Fail) ;;

add_to_FS_autotactic `FSEqUnion` (IfOnConcl (\c. (ext_name c) =
`fmember`) FSEqUnion Fail) ;;

add_to_FS_autotactic `FSSet1` (IfOnConcl (\c. (ext_name c) =
`members`) SetElementI Fail) ;;

add_to_FS_autotactic `FSSet2` (IfOnConcl (\c. (ext_name (snd (destruct_equal c))) = 
`members`) SetElementI Fail) ;;

add_to_FS_autotactic `FSEqMember` (IfOnConcl (\c. (ext_name c) =
`fmember`) FSEqMember Fail) ;;
 
add_to_FS_autotactic `FSHypAdd` (IfOnConcl (\c. (ext_name c) =
`fmember`) FSHypAdd Fail) ;;

add_to_FS_autotactic `FSHypDel` (IfOnConcl (\c. (ext_name c) =
`fmember`) FSHypDel Fail) ;;

add_to_FS_autotactic `FSDelCharGoal` (IfOnConcl (\c. (ext_name c) =
`fmember`) FSDelCharGoal Fail) ;;

add_to_FS_autotactic `FSAddCharGoal` (IfOnConcl (\c. (ext_name c) =
`fmember`) FSAddCharGoal Fail) ;;

add_to_FS_autotactic `FSTrivial` Trivial ;;
