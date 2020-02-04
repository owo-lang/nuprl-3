% This file contains patches to the Nuprl 2.0 tactic collection.  The file
should be loaded with the ML function overwriting_load.
%

% tactics-1.  The third-last line used to be n>0&n'>0.
let tag_toward_equality t t' =
  letref something_tagged = false in
  letrec aux t t' =
    if t = t' then t,t'
    if same_def t t' then 
      map2_on_def_subterms aux t t' 
    if both head_normal_mod_defs t t' & term_kind t = term_kind t' then 
      map2_on_subterms aux t t' 
    else
      let n,n' = topmost_tags_toward_equality t t' in
      something_tagged := n>0 or n'>0 ;
      tag_if_pos n t, tag_if_pos n' t' in
  assert (\(). something_tagged) (aux t t') 
;;
