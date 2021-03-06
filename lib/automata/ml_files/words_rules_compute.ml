
%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  words.ml          PRL_extensions for strings                                             |
|                                                                                           |
|  Rules, tactics  and supplement functions corresponding to the PRL-library "automata"     |
|                                                                                           |
+-------------------------------------------------------------------------------------------%




%  II.   RULES 
   -----------
%


%  IId:  Computation                         
   -----------------    
%



   %           ---  Again, helpfunctions first  -----
   %

      let ordered_exp_list no proof          =
         let [u;v],type = destruct_equal (conclusion proof) in 
            if no=1 then [u;v] else [v;u]
      ;;

   %              ---------------------------------
   %




   let eps_concat_left no        = List_computation no;;

   let eps_concat_right no proof =
     (let [w1;w] = ordered_exp_list no proof in
         let v = fst (destruct_concat w1)    in
                   Seq [make_equal_word_term [v;w] ]
            THENL [ IDTAC; THEOREM1 `eps2` [v] THEN Equal ]
     ) proof
   ;;

   let sym_concat no             =
      let sym_concat_help proof  =                             %  >> a.(nil v) = w in words
                                                                     >> a.v = w in words  %
        (let [av;w] = destruct_equal_word (conclusion proof)   in
            let a,nilv = destruct_cons av in
               let av1 = make_cons_term a (make_tagged_term 1 nilv)  in
                  Direct_computation (make_equal_word_term [av1;w])
        ) proof
      in
         List_computation no THEN sym_concat_help
   ;;

   let cons_concat no proof=
      (let [auv;w] = ordered_exp_list no proof  in 
         let au,v = destruct_concat auv in
            let a,u = destruct_cons au
            in
               Seq [make_equal_word_term [make_cons_term a (make_concat_term u v);w]]
               THENL [IDTAC; Compute_equal no 1 THEN Equal]
      ) proof
   ;;

   let con_assoz no proof  = 
     (let [uvz;w] = ordered_exp_list no proof   in
         let uv,z = destruct_concat uvz   in
            let u,v = destruct_concat uv  in
               let uvz1 = make_concat_term u (make_concat_term v z)  in
                         Seq [make_equal_word_term [uvz1;w]]
                  THENL [IDTAC; THEOREM1 `conassoz` [u;v;z] THENL [Thin_last;Thin_last;Thin_last;Equal] ]
     ) proof
   ;;




   let eps_rev no             = List_computation no;;

   let sym_rev no             =
      let sym_rev_help proof =                                    %  >> nil v = w in words
                                                                      >> nil v = w in words %
        (let [nilrev_v;w] = destruct_equal_word (conclusion proof)   in
            let nilrev,v = destruct_concat nilrev_v      in
               let nilrev1 = make_concat_term (make_tagged_term 1 nilrev) v   in
                  Direct_computation (make_equal_word_term [nilrev1; w])
        ) proof
      in
         List_computation no THEN sym_rev_help THEN eps_concat_left 1
   ;;

   let cons_rev no proof   =
      (let [aurev;w] = ordered_exp_list no proof   in 
          let a,u = destruct_cons (destruct_rev aurev) 
            in
               Seq   [make_equal_word_term [make_anticons_term (make_rev_term u) a ;w]]
               THENL [IDTAC; List_computation no THEN Equal]
      ) proof
   ;;
 

   let rev_con no proof    =
     (let [uvrev;w] = ordered_exp_list no proof in
         let u,v = destruct_concat (destruct_rev uvrev)  in
            let vu = make_concat_term (make_rev_term v) (make_rev_term u)  in
                      Seq [make_equal_word_term [vu;w] ]
               THENL [IDTAC; THEOREM1 `revcon` [u;v] THENL [Thin_last; Thin_last; Equal] ]
     ) proof
   ;;

   let anticons_rev no proof  =
      (let [uarev;w] = ordered_exp_list no proof   in
         let u,a = destruct_anticons (destruct_rev uarev)   in
            let aurev = make_cons_term a (make_rev_term u)  
            in
                 Seq [ make_equal_word_term [aurev;w] 
                     ; make_equal_word_term [u]
                     ; make_equal_symbols_term [a]
                     ; make_equal_word_term [uarev;aurev] 
                     ]
               THENL [ IDTAC; IDTAC; IDTAC
                     ; rev_con no 
                       THENL
                       [ Compute_term 4 THEN wintro 
                         THENL [ Equal; eps_concat_left 1 THEN wintro THEN Equal]
                       ; Equal
                       ; wintro THEN Equal
                       ]
                     ; Equal
                     ]
     ) proof
   ;;

   let doublerev no proof     =
     (let [urevrev;w] = ordered_exp_list no proof  in
         let u = destruct_rev (destruct_rev urevrev)  in
                   Seq [make_equal_word_term [u;w] ]
            THENL [IDTAC; THEOREM1 `doublerev` [u] THEN Equal]
     ) proof
   ;;    




   let iter_down no           = Int_computation no `DOWN`;; 

   let iter_base no           = Int_computation no `BASE` THENL [IDTAC; Int_number] ;;

   let iter_up no proof       = 
      (let [ui;w] = ordered_exp_list no proof in   
          let u,i = destruct_iter ui 
            in
               Seq  [make_equal_word_term 
                      [make_concat_term u (make_iter_term u (make_subtraction_term i one));w] 
                    ]
               THENL [IDTAC; Int_computation no `UP` THENL [ Equal; Thin_last]]
      ) proof
   ;;
 
   let iter_1 no              =
      let iter_help proof     =                                   % >> v (v0) = w in words
                                                                     >> v  = w in words   %
        (let [v_v0;w] = destruct_equal_word (conclusion proof) in
            let v,v0 = destruct_concat v_v0     in
               let tag_v = make_concat_term  v (make_tagged_term 2 v0)  in
                        Direct_computation (make_equal_word_term [tag_v; w])
                  THEN (eps_concat_right 1)
        ) proof
      in
         iter_up no  THENL [iter_help ; Arith THEN Int_number]
   ;;





   let hd_up   no             = List_computation no;;

   let tl_base no             = List_computation no;;

   let tl_up   no             = List_computation no;;





   let lg_base    no          = List_computation no;;

   let lg_up no proof         =
      (let [lgau;w] = ordered_exp_list no proof in 
          let a,u = destruct_cons (destruct_lg lgau) 
            in
               Seq   [ make_equal_term INT [make_addition_term (make_lg_term u) one ;w]]
               THENL [ IDTAC; List_computation no THEN Equal]
      ) proof
   ;;
 
   let lg_1 no                =
      let lg_help proof       =                                   % >>||+1 = x in int
                                                                     >> 1 = x in int     %
         (let [v_1;x] = destruct_equal_int (conclusion proof)  in
            let   zero_1  = make_addition_term zero one
            and   lgeps_1 = make_addition_term (make_lg_term eps) one
            in
               Seq   [make_equal_int_term [one;x];
                      make_equal_int_term [zero_1;one];
                      make_equal_int_term [lgeps_1;zero_1] ]
               THENL [ IDTAC
                     ; Arith THENL [ Int_add THEN Int_number; Int_number]
                     ; Int_add THENL [lg_base 1 THEN Int_number; Int_number]
                     ; Equal
                     ]
         ) proof
      in 
         lg_up no  THEN lg_help
   ;;
   
   let lg_concat no proof     = 
      (let [lguv;x] = ordered_exp_list no proof in
         let u,v = destruct_concat (destruct_lg lguv) in
            let lgu_v = make_addition_term (make_lg_term u) (make_lg_term v)
            in
                     THEOREM1 `lgconcat` [u;v]
               THENL [ IDTAC
                     ; IDTAC
                     ; Seq [make_equal_int_term [lgu_v;x] ] THENL [Thin_last; Equal]
                     ]
      ) proof
   ;;

   let lg_anti no proof       =
      (let [lgua;x] = ordered_exp_list no proof in
         let u,a = destruct_anticons (destruct_lg lgua) in
            let lgu_a = make_addition_term (make_lg_term u) one
            in
                     THEOREM1 `lganti` [u;a]
               THENL [ IDTAC
                     ; IDTAC
                     ; Seq [make_equal_int_term [lgu_a;x] ] THENL [Thin_last; Equal]
                     ]
      ) proof
   ;;

   let lg_rev no proof        =
      (let [lgurev;x] = ordered_exp_list no proof in
         let u = destruct_rev (destruct_lg lgurev) in
            let lgu = make_lg_term u
            in
                     THEOREM1 `lgrev` [u]
               THENL [IDTAC; Seq [make_equal_int_term [lgu;x]] THENL [Thin_last; Equal] ]
      ) proof
   ;;

   let lg_tl no proof         = 
      (let [lgtl;x] = ordered_exp_list no proof in
         let u = destruct_tl (destruct_lg lgtl) in
            let lgu_1 = make_subtraction_term (make_lg_term u) one
            in
                     THEOREM1 `lgtl` [u;imp]
               THENL [ IDTAC
                     ; IDTAC
                     ; Seq [make_equal_int_term [lgu_1;x] ] THENL [Thin_last; Equal]
                     ]
      ) proof
   ;;





   let pre_base no            = Int_computation no `BASE` THENL [IDTAC; Int_number];;

   let pre_up no proof        = 
      (let [ui;w] = ordered_exp_list no proof   in 
          let u,i = destruct_cutprefix ui 
            in
               Seq   [ make_equal_word_term [make_tl_term (make_cutprefix_term u (make_subtraction_term i one)) ;w]]
               THENL [ IDTAC; Int_computation no `UP` THENL [Equal; Thin_last]]
      ) proof
   ;;
 
   let pre_down no proof      = 
      (let [ui;w] = ordered_exp_list no proof   in 
          let u,i = destruct_cutprefix ui 
            in
               Seq   [ make_equal_word_term [make_cutprefix_term u (make_addition_term i one) ;w]]
               THENL [ IDTAC; Int_computation no `DOWN` THENL [Equal;Thin_last]]
      ) proof
   ;;

   let pre_tl no proof        =
      (let [tlvpre;w] = ordered_exp_list no proof in
         let v,k = destruct_cutprefix (destruct_tl tlvpre) in
            let tlv_pre  = make_cutprefix_term (make_tl_term v) k
            in
                      THEOREM1 `pretl` [v;k]
               THENL [IDTAC;   IDTAC;         Seq [make_equal_word_term [tlv_pre;w]] 
                                       THENL [Thin_last; Equal] ]
      ) proof
   ;;

   let pre_top no proof       =
      (let [vpre;w] = ordered_exp_list no proof in
         let v,k = destruct_cutprefix vpre
         in
                   Seq [make_equal_word_term [eps;w]]
            THEN   THEOREM1 `pre3` [v]
            THENL [IDTAC; Equal]
      ) proof
   ;;

   let lg_pre no proof        = IDTAC proof;;


   
   let sel_1 no proof         =
      (let [vsel;b] = ordered_exp_list no proof in
         let v,k = destruct_select vsel   in
            let   hdv = make_hd_term v
            in
                   Seq [make_equal_symbols_term [hdv;b]  ]
            THENL [IDTAC; THEOREM1 `sel1` [v] THENL [Thin_last; Equal] ]
      ) proof
   ;;

   let sel_cons no            = IDTAC;;



   let lg_suf no              = IDTAC;;
   
   let suf_down no            = Int_computation no `DOWN`;;

   let suf_base no            = Int_computation no `BASE` THENL [IDTAC; Int_number];;

   let suf_up no proof        = 
      (let [ui;w] = ordered_exp_list no proof   in 
          let u,i = destruct_cutsuffix ui 
            in
               Seq   [ make_equal_word_term 
                        [make_anticons_term 
                           (make_cutsuffix_term u (make_subtraction_term i one)) 
                           (make_select_term u i) 
                     ; w]]
               THENL [ IDTAC; Int_computation no `UP` THENL [Equal;Thin_last]]
      ) proof
   ;;
 
   let suf_top no proof       =
      (let [vsuf;w] = ordered_exp_list no proof in
         let v,k = destruct_cutsuffix vsuf
         in
            Seq [make_equal_word_term [v;w]] THEN  THEOREM1 `suf3` [v] THEN Equal
      ) proof
   ;;

   


   let lg_range no               = IDTAC;;

   let range_suf no              = pre_base no;;

   let suf_range no              = IDTAC;;

   let range_pre no              = IDTAC;;

   let pre_range no              = IDTAC;;

   let range_extend_left no      = IDTAC;;

   let range_split_left no       = IDTAC;;

   let range_extend_right no     = IDTAC;;

   let range_split_right no      = IDTAC;;

   let range_eps no              = IDTAC;;

   let range_top no              = IDTAC;;

   let range_concat no           = IDTAC;;

   


   % ------------------------  Combined into one tactic: wreduce  ------------------------ %

   let wreduce no proof           =
     (let [vred;w] = ordered_exp_list no proof
      in
         if is_concat_term vred then 
          (let l,r = destruct_concat vred
           in
            if is_eps_term l        then eps_concat_left no
            if is_eps_term r        then eps_concat_right no
            if is_sym_term l        then sym_concat no
            if is_cons_term l       then cons_concat no
            if is_concat_term l     then con_assoz no
            else FAILTAC
          )
         if is_rev_term vred then 
          (let v = destruct_rev vred
           in
            if is_eps_term v        then eps_rev no
            if is_sym_term v        then sym_rev no
            if is_anticons_term v   then anticons_rev no
            if is_cons_term v       then cons_rev no
            if is_concat_term v     then rev_con no
            if is_rev_term v        then doublerev no
            else FAILTAC
          ) 
         if is_lg_term vred then 
          (let v = destruct_lg vred
           in
            if is_eps_term v        then lg_base no
            if is_sym_term v        then lg_1 no
            if is_anticons_term v   then lg_anti no
            if is_cons_term v       then lg_up no
            if is_concat_term v     then lg_concat no
            if is_rev_term v        then lg_rev no
            if is_tl_term v         then lg_tl no
            if is_range_term v      then lg_range no
            if is_cutsuffix_term v  then lg_suf no
            if is_cutprefix_term v  then lg_pre no
            else FAILTAC
          ) 
         else FAILTAC
     ) proof
   ;;
%  ----------------------------------------------------------------------------------------- %




