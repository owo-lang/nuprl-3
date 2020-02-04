
%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  words_rules_1.ml        PRL_extensions for strings                                       |
|                                                                                           |
+-------------------------------------------------------------------------------------------%






%  II.   RULES 
   -----------
%
   %              ---   start with some helpfunctions  ---     
   %
      let word_equality_induction proof   =
         refine (list_equality_induction `nil` NIL words 
                  (new `hd` proof)(new `tl` proof)(new `tl_hyp` proof)
                ) proof
      ;;
      let word_integer_induction pf       =
         refine (integer_equality_induction `nil` NIL (new `k` pf) (new `indhyp` pf)) pf;;

   %                 -------------------------------           %



%  IIa:  Formation   
   ---------------   
%

   let symbol_equality        = refine integer_equality;;
   let sequal                 = symbol_equality;;  

   let word_equality          = refine list_equality THEN symbol_equality;;
   let wequal                 = word_equality;;

   let noteps_equality proof  = 
      (refine (product_equality (new `hd` proof))
       THENL 
       [ sequal
       ; refine (product_equality (new `tl` proof))
         THENL 
         [ wequal
         ; refine equal_equality 
           THENL [wequal; ThinLast 2; refine list_equality_cons THEN Equal]
       ] ]     
      ) proof
   ;;
   let noteps                 = noteps_equality;;
            



%  IIb:  Introduction                        
   ------------------   
%

   let word_equality_eps      = refine (list_equality_nil 1) THEN symbol_equality;;
   let weps                   = word_equality_eps;;

   let word_equality_cons     = refine list_equality_cons;;
   let wcons                  = word_equality_cons;;

   let word_equality_concat   =
      word_equality_induction THENL [IDTAC; IDTAC; wcons THEN Equal];;
   let wconcat                = word_equality_concat;;

   let word_equality_symbols  =  wcons THENL [IDTAC; weps];;
   let wsym                   =  word_equality_symbols;;

   let word_equality_anticons =  wconcat THENL [ IDTAC; wsym];;
   let wanti                  =  word_equality_anticons;;

   let word_equality_rev      =
      word_equality_induction THENL [IDTAC; weps; wanti THEN Equal ];;
   let wrev                   = word_equality_rev;;

   let word_equality_iter     = 
      word_integer_induction THENL [IDTAC;weps;weps; wconcat THENL [ThinLast 3;Equal] ];;
   let witer                  = word_equality_iter;;

   let word_equality_hd       = 
      word_equality_induction THENL [IDTAC; Int_number ; Equal];;
   let whd                    = word_equality_hd;;

   let word_equality_tl       = word_equality_induction THENL [IDTAC; weps; Equal];;
   let wtl                    = word_equality_tl;;

   let word_equality_lg       =
      word_equality_induction THENL [IDTAC;Int_number; Int_add THENL [Equal;Int_number] ];;
   let wlg                    = word_equality_lg;;

   let word_equality_cutprefix= 
      word_integer_induction  THENL [IDTAC; Equal; IDTAC; wtl THEN Equal];;
   let wpre                   = word_equality_cutprefix;;

   let word_equality_select   = 
         whd THEN wpre THENL [Int_sub THENL [ IDTAC; Int_number]; IDTAC];;
   let wselect                = word_equality_select;;

   let word_equality_cutsuffix= 
      word_integer_induction
      THENL 
      [IDTAC; weps; weps;wconcat THENL [Equal; wsym THEN wselect THENL [Equal;ThinLast 3] ]]
   ;;
   let wsuf                   = word_equality_cutsuffix;;

   let word_equality_range    = wpre THENL [ IDTAC; wsuf];;
   let wrange                 = word_equality_range;;



   %  ----------  Now everything together by one rule-name  -------------  %

   let word_introduction_rule proof = 
     (let t.rest, type = destruct_equal (conclusion proof)
      in
         if is_symbols_term t    then symbol_equality
         if is_words_term  t     then word_equality
         if is_noteps_term t     then noteps_equality
         if is_eps_term t        then word_equality_eps
         if is_anticons_term t   then word_equality_anticons
         if is_concat_term t     then word_equality_concat
         if is_sym_term t        then word_equality_symbols
         if is_cons_term t       then word_equality_cons
         if is_rev_term t        then word_equality_rev
         if is_iter_term t       then word_equality_iter 
         if is_select_term t     then word_equality_select
         if is_hd_term t         then word_equality_hd
         if is_tl_term t         then word_equality_tl
         if is_lg_term t         then word_equality_lg
         if is_range_term t      then word_equality_range
         if is_cutprefix_term t  then word_equality_cutprefix
         if is_cutsuffix_term t  then word_equality_cutsuffix
         else FAILTAC
      ) proof
   ;;
   let wintro = word_introduction_rule;;






%  IIc:  Elimination  
   ----------------- 
%



   let word_elim hyp proof       = 
      refine (list_elim hyp (new `tl_hyp` proof)(new `hd` proof)(new `tl` proof)) proof;;


   let word_elim_tail hyp  proof = 
    (let id,T  =  id_of_declaration (select hyp (hypotheses proof)) , (conclusion proof)
     and last  =  length (hypotheses proof)
     and words_U10 =  make_function_term `nil` words (make_universe_term 10)
     in
       let w,P        = (mvar id) , (make_lambda_term id T)             
       in
         Seq   [ make_equal_term words_U10 [P] ]
         THENL 
         [ refine (function_equality_lambda 1 (new `u` proof) ) THENL [IDTAC; wequal]  
         ; THEOREM1 `ind_principle` [ P; imp; w]
           THENL 
           [ Last_hyp
           ; and_intro 
             THENL 
             [ Compute 1 THEN Thin_last
             ; All_intro sequal
               THEN  All_intro wequal
               THEN  imp_intro 10
               THENL 
               [ Hyp_compute (last+4) 1 THEN Compute 1 THEN Thinning [last+1]
               ; refine (function_equality_apply words_U10) THEN Equal
             ] ]
           ; Equal
           ; Hyp_compute (last+2) 1 THEN Hyp (last+2)
         ] ]
    ) proof
   ;;


   let word_elim_lg hyp  proof   = 
    (let id,T  =  id_of_declaration (select hyp (hypotheses proof)) , (conclusion proof) in
     let last  =  length (hypotheses proof) in
     let words_U10 =  make_function_term `nil` words (make_universe_term 10) in
     let compute_in_hyp no proof =
         (let v,type,AB = destruct_all (type_of_declaration (select no (hypotheses proof)))
          in
            let A,B = destruct_imp AB
            in 
               Hyp_computation no (make_all_term v type (make_imp_term A (make_tagged_term 1 B)))
         ) proof
     in
       let w,P        = (mvar id) , (make_lambda_term id T)             
       in
         Seq [ make_equal_term words_U10 [P] ]
         THENL 
         [ refine (function_equality_lambda 1 (new `u` proof) ) THENL [ IDTAC; wequal] 
         ; THEOREM1 `ind_principle1` [ P ; imp ; w ]
           THENL 
           [ Last_hyp
           ; and_intro 
             THENL 
             [ Compute 1 THEN Thin_last
             ; int_all_intro
               THEN  imp_intro 1
               THENL [ imp_intro 10
                       THENL
                       [ All_intro wequal
                         THEN imp_intro 1
                         THENL 
                         [ Compute 1 THEN Thinning [last+1] THEN compute_in_hyp (last+3)
                         ; Ui_equality THENL [refine integer_equality ; wlg THEN Equal; Equal]
                         ]
                       ; all_equality
                         THENL
                         [ wequal
                         ; imp_equality
                           THENL
                           [membership; refine (function_equality_apply words_U10) THEN Equal]
                       ] ] 
                     ; refine less_equality THENL [Int_number; Equal]
            ]        ]
          ; Equal
          ; Hyp_compute (last+2) 1 THEN Hyp (last+2)
        ] ]
    ) proof
   ;;

%  -------------------------------------------------------------------------------------  %

