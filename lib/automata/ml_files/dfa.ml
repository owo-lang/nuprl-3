%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  dfa.ml         PRL_extensions for FINITE AUTOMATA                                        |
|                                                                                           |
+-------------------------------------------------------------------------------------------%


%  I. Constructors, destructors & predicates
   -----------------------------------------
%

%  Ia: Constructors
   ----------------
%
   
   let make_states_term          = instantiate_def `states` [];;
   let make_dfa_term             = instantiate_def `dfa` [];;   
   let make_aut_term Q d q0 F    = make_tup4_term Q d q0 F;;
   let make_star_term del        = instantiate_def `delstar` [del];;
   let make_accept_term M        = instantiate_def `accept` [M];;
   let make_accepted_term w M    = instantiate_def `accepted` [w;M];;

   let states                    = make_states_term;;
   let dfa                       = make_dfa_term;;


   % Additional functions
   %
      let make_table_type_term Q    =                             % ({Q}#SYMBOLS) -> {Q} %
         let Q_set = make_finset_term Q  in
            make_function_term `nil` (make_product_term `nil` Q_set symbols) Q_set;;

      let make_transition_function_term table   = table;;



%  Ib: Destructors
   ---------------
%

   let destruct_aut t            = destruct_tup4 t ;;

   let destruct_star t           = snd (destruct_trk t);;

   let destruct_accept t         = 
      let t,a,b,c,d,M = destruct_where4 (snd (snd (destruct_set t))) in M ;;

   let destruct_accepted t       =
      let dstar_in_F,a,b,c,d,M = destruct_where4 t in
         let w = snd (snd (destruct_apply2 (fst (destruct_inset dstar_in_F))))
         in
            w,M
   ;;


   % Additional functions
   %
      let destruct_table_type t     =
         let (),(Q_sym,Q_set) = destruct_function t in destruct_finset Q_set;;

      let destruct_transition_function t = t;;




%  Ic: Predicates
   --------------
%

   let is_states_term t          = (t = states);;

   let is_dfa_term t             = (t = dfa);;

   let is_aut_term t             = is_tup4_term t;;

   let is_star_term t            = 
      (is_trk_term t) & (is_id_function_term (fst (destruct_trk t)));;
      
   let is_accepted_term t        =
      (let w,M = destruct_accepted t in  t = make_accepted_term w M) ? false
   ;;

   let is_accept_term t          =
      (is_set_term t) & (let w,(T,s) = destruct_set t  in (T = words) & (is_accepted_term s))
   ;;




%  II. RULES                                       (* unfinished)
   ---------
%

%  IIa: Formation
   --------------
%

   %  Helpfunction: dfa_parts_intro

      H, Q:STATES, H' >> (({Q}#SYMBOLS)->{Q}) # {Q} # P({Q}) in Ui    (i>1)
   %

      let dfa_parts_intro proof =
        (let [term], Ui = destruct_equal (conclusion proof) 
         and Cum        = Cumulativity THEN Equal
         in
            let Q_set = fst (snd (destruct_product (snd (snd (destruct_product term)))))
            in
                     Seq [make_equal_term U1 [Q_set] ]
               THENL [ finset_equality_conversion THEN Equal
                     ;       ProdUitac 
                       THENL [ FuncUitac THENL [ ProdUitac THENL [Cum;sequal]; Cum]
                             ; ProdUitac THENL [ Cum; Spower THEN Equal ]
                             ]
                     ]
        ) proof
      ;;
   % --------------------------------------------------------------------------%    


   let state_intro         = finset_intro;;

   let state_set_intro     = finset_equality_conversion;;

   let dfa_intro           = Intro THENL [ state_intro; dfa_parts_intro];;

   let accepted_intro proof=     
      (let w,M = destruct_accepted (first_exp proof)
       in
               THEOREM1 `acceptedtype` [M;w]
         THENL [IDTAC; IDTAC; Cumulativity THEN Equal]
      ) proof
   ;;

   let accept_intro proof  = 
      (       refine (set_formation (new `w` proof))
       THENL [wequal; accepted_intro THENL [ IDTAC ; Equal] ]
      ) proof
   ;;



%  IIb:  Introduction
   ------------------
%
                  

   let dfa_equality              =
      tup4_equality 2 THENL [IDTAC; IDTAC; IDTAC; IDTAC; dfa_parts_intro]
   ;;

   let dfa_equality_spread proof = IDTAC;;

   let star_intro                = THEOREM `delstartype`;;

   let accept_equality proof     = 
      ( refine (set_equality_element 1 (new `w` proof)) THENL [IDTAC; IDTAC; accepted_intro]
      ) proof
   ;;

   let delstar_equality_apply proof    =        %trkid_equality_apply%
      (let Qset = snd (destruct_equal (conclusion proof))
       in
         apply2_equality (make_trktype_term Qset Qset) 1
         THENL [trkid_intro; IDTAC; IDTAC]
      ) proof
   ;;


%  IIc:  Elimination
   -----------------
%

   let dfa_elim hyp proof     = 
      (let Q,d,q0,F  = (new `Q` proof),(new `d` proof),(new `q0` proof),(new `F` proof) in
       let T3,T2     = (new `T3` proof),(new `T2` proof) in
       let l         = length (hypotheses proof) in
       let M         = mvar (id_of_declaration (select hyp (hypotheses proof))) in
       let Prodtac   = refine product_equality_pair_independent in
       let Prod1 pf  = (refine (product_equality_pair 2 (new `Q1` pf))) pf 
       in
        let Q1,d1    = (mvar Q),(mvar d)
        in
          let Qdq0F  = make_aut_term  Q1 d1 (mvar q0) (mvar F)
          and QdT2   = make_tup3_term Q1 d1 (mvar T2)
          and QT3    = make_tup2_term Q1 (mvar T3)
          in
                  refine (product_elim hyp   Q  T3)
            THEN  refine (product_elim (l+2) d  T2)
            THEN  refine (product_elim (l+5) q0 F)
            THEN  Seq [ make_equal_term dfa [Qdq0F ; QdT2  ]
                      ; make_equal_term dfa [QdT2  ; QT3   ]
                      ; make_equal_term dfa [Qdq0F ; M] 
                      ]
            THENL [Prod1 THENL [Equal; Prodtac THEN Equal; dfa_parts_intro]
                  ;Prod1 THENL [Equal; Equal; dfa_parts_intro]
                  ;Equal
                  ;Thinning [l+2; l+3; l+5; l+6; l+9; l+10; l+11]
                  ]
      ) proof
   ;;


   let accept_elim hyp proof  = 
      (        refine (set_elim hyp 1 (new `s` proof))
        THENL [accepted_intro THENL [IDTAC; Equal] ; IDTAC]
      ) proof
   ;;


%  IId:  Computation
   -----------------
%

   let star_reduction_eps no  = if no = 1 then Compute_term 5 else Compute_snd_term 5;;

   let star_reduction_anticons no proof   =
      (let dstarqwa,q1,Qset = ordered_equality no proof
       in
         let dstar,q,wa = destruct_apply2 dstarqwa
         and Q          = destruct_finset Qset
         in
            let d,(w,a) = destruct_star dstar, (destruct_anticons wa)
            in
               let dstarnew = make_apply2_term d (make_apply2_term dstar q w) a
               in
                        THEOREM1 `delprop0` [Q;d;q;w;a]
                  THENL (list 5 IDTAC) 
                      @ [       Seq [make_equal_term Qset [dstarnew;q1] ]
                          THENL [Thin_last; Equal]
                        ]
      ) proof
   ;;

   let star_reduction_concat no proof  =
      (let dstarqvw,q1,Qset = ordered_equality no proof
       in
         let dstar,q,vw = destruct_apply2 dstarqvw
         and Q          = destruct_finset Qset
         in
            let d,(v,w) = destruct_star dstar, (destruct_concat vw)
            in
               let dstarnew = make_apply2_term dstar (make_apply2_term dstar q v) w
               in
                        THEOREM1 `delprop1` [Q;d;v;w;q]
                  THENL (list 5 IDTAC) 
                      @ [       Seq [make_equal_term Qset [dstarnew;q1] ]
                          THENL [Thin_last; Equal]
                        ]
      ) proof
   ;;



%  III Tactics
   -----------
%
   
   let states_all_intro          = All_intro state_intro;;
   let dfa_all_intro             = AllIntro 2 dfa_intro;;
   let accept_all_intro          = All_intro (accept_intro THEN Equal);;

   let dfa_intro_elim proof      =
      (let last = length (hypotheses proof) in dfa_all_intro THEN dfa_elim (last+1)) proof ;;

   let accept_intro_elim proof   =
      (let last = length (hypotheses proof)
       in
          accept_all_intro THEN accept_elim (last+1) THENL [Equal; IDTAC]
      ) proof
    ;;


   let star_anticons_compute no  =
      star_reduction_anticons no THENL [Equal;Equal;Equal;Wintro;Wintro;IDTAC] ;;

   let star_concat_compute no    = 
      star_reduction_concat no THENL [Equal;Equal;Wintro;Wintro;Equal;IDTAC] ;;

   let delstar_apply             =
      delstar_equality_apply THENL [ TRY (state_set_intro THEN Equal); Equal; Equal; Wintro];;

   let Autotactic = TRY (equal ORELSE hypothesis) ;;               
   set_auto_tactic `refine (tactic \`Autotactic\` )` ;;            
   let membertactic = membership;;                                 


%%