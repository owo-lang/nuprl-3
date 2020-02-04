
%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  sets.ml        PRL_extensions for the type SETS                                          |
|                                                                                           |
+-------------------------------------------------------------------------------------------%



%  I. Term constructors, predicates and destructors
   ------------------------------------------------
%



%  Ia:   Constructors
   ------------------
%

   let make_SETS_term            =  instantiate_def `sets` [];;
   let make_carrier_term S       =  instantiate_def `carrier` [S];;
   let make_pred_term S          =  instantiate_def `pred` [S];;
   let make_setdef_term x A B    =  instantiate_def `setdef` [x;A;B];;
   let make_singleton_term x A   =  instantiate_def `singleton` [x;A];;
   let make_inset_term x S       =  instantiate_def `inset` [x;S];;
   let make_set_conversion S     =  instantiate_def `setconversion` [S];;
   let make_powerset_term A      =  instantiate_def `powerset` [A];;

   let SETS                      =  make_SETS_term;;

%  Ib:   Destructors
   -----------------
%

   let destruct_carrier term     = let t,a,b,S = destruct_where2 term in S;;

   let destruct_pred term        = let t,a,b,S = destruct_where2 term in S;;

   let destruct_setdef term      = term,term,term;;      % !!!!!!!!%
   let destruct_singleton term   = term,term;;           % !!!!!!!!%

   let destruct_inset term       = let p,x = destruct_apply term in x,(destruct_pred p);;

   let destruct_set_conversion term = let t,a,b,S = destruct_where2 term in S;;

   let destruct_powerset term    = 
      let [carrierS;A], U1 = destruct_equal (snd (snd (destruct_set term))) in A;;


%  Ic:   Predicates
   -------------
%

   let is_SETS_term t            = t = SETS;;

   let is_carrier_term t         = (t = make_carrier_term (destruct_carrier t) ) ? false;;

   let is_setdef_term t          = 
      (let x,A,B = destruct_setdef t in t = make_setdef_term x A B) ? false;;

   let is_singleton_term t          = 
      (let x,A = destruct_singleton t in t = make_singleton_term x A) ? false;;

   let is_pred_term t            = (t = make_pred_term (destruct_pred t) ) ? false;;

   let is_inset_term t           =
      (is_apply_term t) & (is_pred_term (fst (destruct_apply t)));;

   let is_set_conversion t       = 
      (t = make_set_conversion (destruct_set_conversion t) ) ? false;;

   let is_powerset_term t        = (t = make_powerset_term (destruct_powerset t) ) ? false;;

%-----------------------------------------------------------------------------------------%




%  II.   RULES 
   -----------
%


%  IIa:  Formation   
   ---------------
%
   %  ---   start with some helpfunctions  ---  %
      
      let SETS_spread proof      =
         (refine  (product_equality_spread `nil` NIL SETS 
                                           (new `carrier` proof) (new `pred` proof)
                  )
         ) proof
      ;;

      let Scarrier            = SETS_spread THENL [IDTAC; Cumulativity THEN Equal] ;;

   %  ---------------------------------------------------------------------------   %


   let SETS_equality proof    =
      (     refine (product_equality (new `carrier` proof))
       THENL [UiUjtac; FuncUitac THENL [Cumulativity THEN Equal; UiUjtac] ]
      ) proof
   ;;
   let SETSeq        = SETS_equality;;


   let SETS_equality_conversion proof     =
      (let carrier, pred   = (new `carrier` proof), (new `pred` proof)
       in
               refine (product_equality_spread `nil` NIL SETS carrier pred)
         THENL [ IDTAC
               ; Cumulativity
                 THEN  refine (set_formation (new `x` proof))
                 THENL [ Equal
                       ; refine (function_equality_apply 
                                       (make_function_term `nil` (mvar carrier) U1))
                         THEN Equal
                       ;
                       ]
               ]
      ) proof
   ;;
   let Sconversion   = SETS_equality_conversion;;


   let SETS_equality_power proof    =
      (      refine (set_formation (new `S` proof))
       THENL [ SETSeq
             ; Ui_equality THENL [UiUjtac; Scarrier THEN Equal; IDTAC]
             ]
      ) proof
   ;;
   let Spower        = SETS_equality_power;;


   %  SETS_equality_inset is defined after SETS_equality_pred in the Introduction section %




%  IIb:  Introduction                        
   ------------------
%
   let SETS_equality_pair        =
            tup2_equality 2 
      THENL [ IDTAC; IDTAC; FuncUitac THENL [Cumulativity THEN Equal; UiUjtac]] 
   ;;
   let Spair                     = SETS_equality_pair;;


   let SETS_power_element proof  =
      (let term_list,type = destruct_equal (conclusion proof)
       in
         let S, A = (hd term_list), destruct_powerset type
         in
            Seq [ make_equal_term SETS term_list
                ; make_equal_term U1 [make_carrier_term S; A]
                ]
            THENL [ IDTAC
                  ; IDTAC
                  ;        refine (set_equality_element 2 (new `S` proof))
                   THENL [Equal;Equal; Ui_equality THENL [UiUjtac;Scarrier THEN Equal;Equal] ]
                  ]
      ) proof
   ;;
   let Spowerel                  = SETS_power_element;;


   let SETS_conversion_element proof = 
      (IDTAC               % Eliminate S and consruct over term%
      ) proof
   ;;
   let Sconvel                   = SETS_conversion_element;;


   let SETS_equality_carrier     = Scarrier;;


   let SETS_equality_pred proof  =
      (let over = make_function_term `nil` (make_carrier_term (mvar `xxp`)) U1
       in
             refine (product_equality_spread `xxp` over SETS 
                                             (new `carrier` proof)(new `pred` proof) )
       THENL [IDTAC; Compute_equal_function_left 1 THEN Equal]
      ) proof
   ;;
   let Spred                     = SETS_equality_pred;;



   let SETS_equality_inset proof =
      (let S = destruct_pred (fst (destruct_apply (first_exp proof)))
       in
         Cumulativity 
         THEN
         refine (function_equality_apply (make_function_term `nil` (make_carrier_term S) U1))
         THENL [Spred; IDTAC]
      ) proof
   ;;
   let Sinset                    = SETS_equality_inset;;


   %  ----------  Now everything together by one rule-name  -------------  %

   let Sintro proof  = IDTAC proof;;




%  IIc:  Elimination
   -----------------
%

   let SETS_elim hyp proof       =
      (refine (product_elim hyp (new `carrier` proof)(new `pred` proof))) proof
   ;;

   let conversion_elim hyp proof =
      ( IDTAC
      ) proof
   ;;

   
   let powerset_elim hyp proof   =                                      % INCOMPLETE %
      (let l = length (hypotheses proof)
       in
               refine (set_elim hyp 2 (new `S` proof))
         THENL [ Ui_equality THENL [UiUjtac; Scarrier THEN Equal; IDTAC]
               ; SETS_elim (l+1)
               ]
      ) proof
   ;;




%  III:  Miscellaneous  functions and tactics 
   ------------------------------------------
%


   let sets_all_intro = AllIntro 2 SETSeq;;

   let conversion_all_intro = All_intro (Sconversion THEN Equal);;

% ------------------------------------------------------------------------ %



