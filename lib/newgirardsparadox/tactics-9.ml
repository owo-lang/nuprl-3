
let TrivialInclusion i =
  Refine equality 
  ORELSE
  ( ComputeHypType i THEN ComputeConclType 
    THEN Try (Refine equality)
    THEN ( Refine (cumulativity 1) )
    THEN Refine equality
  )
;;


let EqualityIntro p =

  let (t.rest),T = destruct_equal (concl p)  in

  if is_lambda_term t then
         (Refine (function_equality_lambda big_U `nil`)
    ORELSE
    Refine (function_equality_lambda big_U
      (undeclared_id_using p (fst (destruct_lambda t))))
         ) p

  if is_apply_term t then
    (let b,a = destruct_apply t  in
      (\ p.
        (let using = (compute (get_type p b)) in
        let x,A,B = destruct_function using in
        let T' = if x=`NIL` then B 
              else substitute B [make_var_term x,a] in
          if T'=T then
          Refine  (function_equality_apply using)
          if is_universe_term T' & is_universe_term T then
          Refine (cumulativity (destruct_universe T'))
          THEN
          Refine  (function_equality_apply using)
          else  Seq [make_equal_term T' (t.rest)]
            THENL
            [Refine (function_equality_apply using)
            ;FastAp (OnLastHyp TrivialInclusion)
            ]
        ) p
      )
      ORELSE
      (\p. Refine (function_equality_apply
                (make_function_term `nil` (compute (get_type p a)) T))
              p)
     ) p


  if is_universe_term t then Refine universe_equality p

  if is_function_term t then
         (Refine (function_equality `nil`) 
    ORELSE
    Refine (function_equality 
        (undeclared_id_using p (fst (destruct_function t))))
         ) p


  else failwith `EqualityIntro`

;;



let NonReducingMemberIntro =

  Refine equality

  ORELSE

( (\ p .
       (let (t.tl),T = destruct_equal (concl p)  in
  if not (null (filter (\x. not term_kind x = term_kind t) tl))  
  then fail 
  ;

  if is_canonical_term t then
  ComputeConclType THEN EqualityIntro

  if is_noncanonical_term t then EqualityIntro

  if is_term_of_theorem_term t then
    (   (if destruct_term_of_theorem t = `Type_` then
          Refine (lemma `Type__` `nil`)
         else
          Refine (def (destruct_term_of_theorem t) `nil`)
        )
        THEN
        OnLastHyp TrivialInclusion
    )

  if is_var_term t then
    FastAp (TrivialInclusion (find_declaration (destruct_var t) p))

  else fail

       )
       p )
)
;;

let Because = ref `because` ;;

letref postponed_membership_goals = []: proof list ;;

let DealWithMembershipGoal p =
  if not is_membership_goal p then fail
  else (postponed_membership_goals := p . postponed_membership_goals; Because p)
;;

let Autotactic =
    (Repeat
      ( Trivial
        ORELSE Repeat (\p. if (top_def_of_term (concl p); true) ? false
                            then (if (member (top_def_of_term (concl p))
                                             ([`imp`;`all`;`all2`;`all3`;`all4`;`uall`;`uall2`]))
                                  then Intro p else fail )
                            else (if is_function_term (concl p) then Intro p else fail)
                      )
        ORELSE DealWithMembershipGoal
      )
    )
;;

let ExplicitIntro t = Refine (explicit_intro t) ;; 
