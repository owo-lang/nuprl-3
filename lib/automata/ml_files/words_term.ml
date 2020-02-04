
%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  words.ml          PRL_extensions for strings                                             |
|                                                                                           |
|  Rules, tactics  and supplement functions corresponding to the PRL-library "automata"     |
|                                                                                           |
+-------------------------------------------------------------------------------------------%













%  I. Term constructors, predicates and destructors
   ------------------------------------------------
%



%  Ia:   Constructors
   ------------------
%

   let make_symbols_term         = instantiate_def `symbols` [];;
   let make_words_term           = instantiate_def `words` [];;
   let make_noteps_term w        = instantiate_def `noteps` [w];;
   let make_eps_term             = instantiate_def `eps` [];;
   let make_cons_term a l        = make_cons_term a l ;;
   let make_concat_term u v      = instantiate_def `concat` [u;v];;
   let make_sym_term a           = instantiate_def `sym` [a];;
   let make_anticons_term w a    = instantiate_def `anticons` [w;a];;
   let make_rev_term w           = instantiate_def `rev` [w];;
   let make_iter_term w i        = instantiate_def `iter` [w;i];;
   let make_hd_term w            = instantiate_def `hd` [w];;
   let make_tl_term w            = instantiate_def `tl` [w];;
   let make_lg_term w            = instantiate_def `lg` [w];;
   let make_cutprefix_term w i   = instantiate_def `cutprefix` [w;i];;
   let make_select_term w i      = instantiate_def `select` [w;i];;
   let make_cutsuffix_term w i   = instantiate_def `cutsuffix` [w;i];;
   let make_range_term w l r     = instantiate_def `range` [w;l;r];;

   let symbols       = make_symbols_term;;
   let words         = make_words_term;;
   let eps           = make_eps_term;;

   
   %  additional constructors which are useful in rules and tactics
   %

      let make_equal_word_term w_list     =  make_equal_term words   w_list ;;
      let make_equal_symbols_term w_list  =  make_equal_term symbols w_list ;;




%  Ib:   Destructors
   -----------------
%


   let destruct_noteps t      =
      let a,symb,t1 = destruct_some t  in
         let l,word,t2 = destruct_some t1  in
            let [w;al],type = destruct_equal t2  in
               w
   ;;

   let destruct_cons t        = destruct_cons t ;;

   let destruct_concat t      = let var,tb,tu = destruct_list_induction t  in  var,tb  ;;

   let destruct_sym t         = fst (destruct_cons t) ;;

   let destruct_anticons t    =
      let w,a1 = destruct_concat t in w,(destruct_sym a1) ;;

   let destruct_rev t         = let var,tb,tu = destruct_list_induction t  in  var  ;;

   let destruct_iter t        = 
      let i,td,tb,tu = destruct_integer_induction t  in
         let word,hyp = destruct_concat (snd (destruct_bound_id tu)) in
            word, i
   ;;

   let destruct_hd t          = let var,tb,tu = destruct_list_induction t  in  var  ;;

   let destruct_tl t          = let var,tb,tu = destruct_list_induction t  in  var  ;;

   let destruct_lg t          = let var,tb,tu = destruct_list_induction t  in  var  ;;

   let destruct_cutprefix t   = let i,td,word,tu = destruct_integer_induction t  in word,i ;;

   let destruct_select t      = 
      let w,i_1 = destruct_cutprefix (destruct_hd t) in  w,(fst (destruct_subtraction i_1));;

   let destruct_cutsuffix t   =
      let i,td,tb,tu = destruct_integer_induction t  in 
         let hyp,sym = destruct_concat (snd (destruct_bound_id tu)) in
            let word,var   = destruct_select (destruct_sym sym) in
               word,i
   ;;

   let destruct_range t       =
      let w1,l = destruct_cutprefix t  in
         let w,r = destruct_cutsuffix w1  in
            w, l, r
   ;;



   % additional destructors
   %

   let destruct_equal_word t  =
      let w_list,type = destruct_equal t in if type = words then w_list else fail ;;





%  Ic:   Predicates
   -------------
%

   let is_symbols_term t   = is_int_term t ;;

   let is_words_term t     = (is_list_term t) & (destruct_list t = INT)   ;;

   let is_eps_term   t     = is_nil_term t ;;

   let is_noteps_term t    = (let w = destruct_noteps t in t = make_noteps_term w) ? false;;
    
   let is_cons_term        = is_cons_term;;

   let is_concat_term   t  =
      (is_list_induction_term t) 
    & (let var,tb,tu = destruct_list_induction t    in
         let [hd;tl;tlcon], tu_term = destruct_bound_id tu  in
            tu_term = make_cons_term (mvar hd) (mvar tlcon)
      )
   ;;

   let is_sym_term t       = (is_cons_term t) & (snd (destruct_cons t) = eps) ;;

   let is_anticons_term t  =
      (is_concat_term t) & (is_sym_term (snd (destruct_concat t)));;

   let is_rev_term t       =
      (is_list_induction_term t) 
    & (let var,tb,tu_term = destruct_list_induction t  in
         let [hd;tl;tlrev], tu = destruct_bound_id tu_term  in
            (tu = make_anticons_term (mvar tlrev ) (mvar hd) ) & (tb = eps)
      )
   ;;

   let is_iter_term t      =
      (let w,i = destruct_iter t in  (make_iter_term w i) = t ) ? false ;;

   let is_hd_term t        =
      (is_list_induction_term t) 
    & (let var,tb,tu = destruct_list_induction t    in
         let [hd;tl;tlt], tu_term = destruct_bound_id tu    in
            tu_term = (mvar hd)
      )
   ;;

   let is_tl_term t        = 
      (is_list_induction_term t) 
    & (let var,tb,tu = destruct_list_induction t    in
         let [hd;tl;tlt], tu_term = destruct_bound_id tu    in
            tu_term = mvar tl
      )
   ;;

   let is_lg_term t        = 
      (is_list_induction_term t) 
    & (let var,tb,tu = destruct_list_induction t    in
         let [hd;tl;tllg], tu_term = destruct_bound_id tu   in
            tu_term = make_addition_term (mvar tllg) one
      )
   ;;

   let is_cutprefix_term t =
      (let w,i = destruct_cutprefix t in  (make_cutprefix_term w i) = t ) ? false ;;

   let is_select_term t    = (is_hd_term t) & (is_cutprefix_term (destruct_hd t));;

   let is_cutsuffix_term t =
      (let w,i = destruct_cutsuffix t in  (make_cutsuffix_term w i) = t ) ? false ;;
   
   let is_range_term t     = 
      (is_cutprefix_term t) & (is_cutsuffix_term (fst(destruct_cutprefix t))) ;;



   % additional predicates
   %

   let is_equal_word_term t= (is_equal_term t) & (snd (destruct_equal t) = words) ;;

%-----------------------------------------------------------------------------------------%

