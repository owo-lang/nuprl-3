% false <=> occurs nonce, true <=> once, failure o.w. %

let id = \x.x ;; 

let occurs_once x t =
  letrec aux t = % iff x occurs exactly once %
    if is_var_term t then destruct_var t = x
    else let n = length (filter id (map aux (subterms t))) in
         if n=0 then false if n=1 then true else fail in
  aux t ? failwith `more than 1 occurrence`
;; 


letrec optimize t =
  ( let f,a = destruct_apply t in
    let x,b = destruct_lambda f in
    if occurs_once x b then optimize (substitute b [mvt x, a])
    else optimize b
  )
  ? map_on_subterms optimize t
;; 

letrec expand_term t = 
  if is_function_term t then 
    make_token_term `<type>`
  if is_term_of_theorem_term t then 
    expand_term (extracted_term_of_theorem (destruct_term_of_theorem t))
  else map_on_subterms expand_term t
;; 


letrec number_of_subterms t =
  1 + accumulate (\x y. x+y) 0 (map number_of_subterms (subterms t)) 
;; 