%-------------------------------------------------------------------------------+
|  Supply.ml:            ML-functions for general use in PRL                    |
+-------------------------------------------------------------------------------%


   let INT   = make_int_term     ;;
   let NIL   = make_nil_term     ;;
   let VOID  = make_void_term    ;;
   let mvar  = make_var_term     ;;
   let imp   = mvar `=>`         ;;
   let andl  = mvar `&l`         ;;
   let andr  = mvar `&r`         ;;
   let zero  = make_natural_number_term 0;;
   let one   = make_natural_number_term 1;;
   let U1    = make_universe_term 1;;
   let U2    = make_universe_term 2;;


   let cat tok no                =  tok^(tok_of_int no);;

   letrec is_member element list =
      (let hd.tl = list in (element = hd) or (is_member element tl) ) ? false ;;

   letrec cut_from no list       = 
      if no = 0 then [] else (hd list).(cut_from (no-1) (tl list));;

   letrec cut_first no list      =  if no = 1 then list else (cut_first (no-1)(tl list));;

   let ids declist               =  map id_of_declaration declist ;; 

   let is_alpha_convertible s t  =  s=t;;

   letrec list n obj             = if n = 0 then [] else obj.(list (n-1) obj);;

   letrec intlist base no        = if no = 0 then [] else base.(intlist (base+1)(no-1));;

   let first_exp proof           = hd (fst (destruct_equal (conclusion proof)));;

   let ordered_equality no proof =
      let [u;v],type = destruct_equal (conclusion proof)
      in
         if no = 1 then u,v,type else v,u,type
   ;;
   
   let new tok proof             =
      letrec newid tok no idlist =
         let id = cat tok no in if is_member id idlist  then newid tok (no+1) idlist  else id
      in
        let idlist = ids (hypotheses proof)
        in
          if is_member tok idlist  then newid tok 0 idlist  else tok
   ;;
%  ****************************** END HELPFUNCTIONS *********************************%



%  *************************** TYPE INFORMATION FUNCTIONS **************************** %
  

  let hyp_info var proof =
   letrec check no declist =
      let id,type = destruct_declaration (hd declist)  in
         if var = id   then  no,type   else  check (no+1) (tl declist)
   in
      check 1 (hypotheses proof)
  ;;
 
  let typed exp decl =
   let id,term = destruct_declaration decl
   in
      if is_var_term exp
      then if id = (destruct_var exp)  then term  else fail
      else if is_equal_term term
            then (let L,type = destruct_equal term  in
                    if (is_member exp L) then type  else fail
                 )
           if is_less_term term
            then (let l,r = destruct_less term  in
                    if (exp = l) or (exp = r) then make_int_term else fail
                 )
           else fail
  ;;

  letrec checkhyps exp hyplist = (typed exp (hd hyplist)) ? (checkhyps exp (tl hyplist));;


  letrec typeof exp proof special_type_information =
   let exp_kind = term_kind exp
   in
      if exp_kind = `NATURAL-NUMBER` 
      then INT
      else (special_type_information exp proof)
           ?
           (checkhyps exp (hypotheses proof))
           ?
           (let type_of term = typeof term proof special_type_information
            in
            if exp_kind = `PAIR` 
            then (let a,b  = destruct_pair exp in
                     make_product_term `NIL` (type_of a) (type_of b)
                 )
            if exp_kind = `APPLY`
            then (let f,x = destruct_apply exp  in
                     let A_B,A = (type_of f),(type_of x)  in
                        let id,A1,B = destruct_function A_B in
                           if A = A1 then B else failwith `wrong argumenttype`
                 )
            if exp_kind = `CONS`
            then make_list_term (type_of (fst (destruct_cons exp)))

            else failwith `type not found`
           )
  ;;

  let type_of exp proof = typeof exp proof (\exp.\proof.fail) ;;
%************************** END TYPE INFORMATION FUNCTIONS ****************************%


   let find_instance_using_typing_of var elim_list inst_list proof =    % to be extended %
      letrec find_type_of T inst_list elim_list =
         let (xi,Ai).rest_elim   = elim_list
         and ai.rest_inst        = inst_list
         in
            if T = Ai then type_of ai proof  else find_type_of T rest_inst rest_elim
      in
         find_type_of (mvar var) inst_list elim_list 
   ;;

   let instance_for x match_list elim_list inst_list t s proof =
      letrec find_match_in match_list var    =
         let (xi,ai).rest_match = match_list in
            if var = xi then ai else find_match_in rest_match var

      and ask_for_help var t1 t2       = fail                        % TO BE EXTENDED%
      in
         (find_match_in match_list x)
         ?
         (find_instance_using_typing_of x elim_list inst_list proof)
         ?
         (ask_for_help x t s)
   ;;

   let build_instantiation_list_from twolist t s proof =
      letrec build_from match_list elim_list =
         if null elim_list
            then []
            else let (xi,Ai).rest_elim = elim_list in
                   let inst_list       = build_from match_list rest_elim in
                     (if xi = `NIL` then imp
                      if xi = `&l`  then andl
                      if xi = `&r`  then andr
                      else instance_for xi match_list rest_elim inst_list t s proof
                     ).inst_list
      in
         let match_list, elim_list = twolist in build_from match_list elim_list
   ;;

%to be extended to permutation of equalities/ all_quantifiers etc.%

   let match_subterms t s proof     =
      let insert2 twolist element   =  let L1,L2 = twolist in L1,(element.L2) in
      let s_structure               =  term_kind s
      in
         letrec match_s_using meta_vars term =
            (if term_kind term = s_structure
                then ( (match term s meta_vars) 
                       ? 
                       (if s_structure = `EQUAL`
                         then let [a;b],T = destruct_equal term in
                                 match (make_equal_term T [b;a]) s meta_vars
                         else let [a],T = destruct_equal term in
                                 match (make_equal_term T [a;a]) s meta_vars
                     ) ),[] 
                else fail
            )
            ?
            (let x,T,t1 = destruct_function term  in
               insert2 (match_s_using (if x=`NIL` then meta_vars else x.meta_vars) t1) (x,T)
            )
            ?
            (let x,B,B1 = destruct_product term   in
               if x = `NIL`
                  then ( ( insert2 (match_s_using meta_vars B)(`&l`,NIL) )
                         ?
                         ( insert2 (match_s_using meta_vars B1)(`&r`,NIL) )
                       )
                  else failwith `NO MATCH`
            )
         in
            build_instantiation_list_from (match_s_using [] t) t s proof
   ;;

%  ************************************************************************************   %