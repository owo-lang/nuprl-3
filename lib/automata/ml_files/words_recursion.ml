
%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  words_recursion.ml      PRL_extensions for strings & recursive function definition       |
|                                                                                           |
+-------------------------------------------------------------------------------------------%





%  A: Tail-recursion (trk)
   -------------------------
%

%  I: Constructors, destructors & predicates
   -----------------------------------------
%
   let make_trk_term g h   = instantiate_def `trk` [g;h]  ;;
   let make_idtrk_term h   = instantiate_def `idtrk` [h]  ;;

   let make_trktype_term A B  =
      make_function_term `nil` (make_product_term `nil` A words) B ;;


   let destruct_trk t      = 
      let x,w,list_ind = destruct_lambda2 t in
         let val,tb,tu = destruct_list_induction list_ind in
            fst (destruct_apply tb), fst (destruct_apply (snd (destruct_bound_id tu)))
   ;;

   let destruct_idtrk t    = snd (destruct_trk t);;
   let destruct_trk_type t =
      let (),Awords,B = destruct_function t in
         let (),A,words = destruct_product Awords
         in
            A,B
   ;;


   let is_trk_term t       = 
      (let g,h = destruct_trk t in  t = make_trk_term g h) ? false;;
   let is_idtrk_term t     = (t = make_idtrk_term (destruct_idtrk t) ) ? false;;


%  II: RULES 
   ---------
%

%  IIb: Introduction
   -----------------
%

   let trk_intro           = THEOREM `trktype`;;

   let trkid_intro proof   =
      (let h.rest , A_WORDS_A = (destruct_equal (conclusion proof))
       in
         let A = fst (destruct_trk_type A_WORDS_A)
         in
         Seq   [ make_equal_term U1 [A]
               ; make_equal_term A_WORDS_A [h]
               ]
         THENL [ IDTAC
               ; trk_intro 
                 THENL [ Equal
                       ; Equal
                       ; refine (function_equality_lambda 1 (new `x` proof)) THEN Equal
                       ; IDTAC
                       ]
               ; Equal
               ]
      ) proof
   ;;

   let trkid_equality_apply proof =
      (let T =  snd (destruct_equal (conclusion proof))
       in 
               apply2_equality (make_trktype_term T T) 1
         THENL [ trkid_intro; IDTAC; IDTAC]
      ) proof
   ;;

%  IId: Computation
   ----------------
%

   let trkid_reduce_base no   = if no = 1 then Compute_term 5 else Compute_snd_term 5;;

   let trkid_reduce_up no proof  =
      (let dstarqwa,q1,B = ordered_equality no proof
       in
         let dstar,q,wa = destruct_apply2 dstarqwa
         in
            let d,(w,a) = destruct_idtrk dstar, (destruct_anticons wa)
            in
               let dstarnew = make_apply2_term d (make_apply2_term dstar q w) a
               in
                  Seq   [ make_equal_term U1 [B]
                        ; make_equal_term (make_function_term `nil` B B) [id]
                        ]
                  THENL [ IDTAC
                        ; membership   
                        ; THEOREM1 `trk2` [B;B;id;d;q;w;a]
                          THENL (list 3 Equal) @ (list 4 Thin_last) 
                           @ [Seq [make_equal_term B [dstarnew;q1] ] THENL [ThinLast 2; Equal] ]
                        ]
      ) proof
   ;;

   let trkid_reduce_concat no proof =
      (let dstarqvw,q1,B = ordered_equality no proof
       in
         let dstar,q,vw = destruct_apply2 dstarqvw
         in
            let d,(v,w) = destruct_idtrk dstar, (destruct_concat vw)
            in
               let dstarnew = make_apply2_term dstar (make_apply2_term dstar q v) w
               in
                  
                  Seq   [ make_equal_term U1 [B]
                        ; make_equal_term (make_function_term `nil` B B) [id]
                        ]
                  THENL [ IDTAC
                        ; membership      
                        ; THEOREM1 `trk4` [B;B;id;d;v;w;q]
                          THENL (list 3 Equal) @ (list 4 Thin_last) 
                           @ [ Seq [make_equal_term B [dstarnew;q1] ] THENL [ThinLast 2; Equal]]
                        ]
      ) proof
   ;;



%  III: Tactics
   ------------
%

   let trkid_anticons_compute no =
      trkid_reduce_up no THENL [Equal;Equal;Equal;Wintro;Wintro;IDTAC] ;;

   let trkid_concat_compute no = 
      trkid_reduce_concat no THENL [Equal;Equal;Wintro;Wintro;Equal;IDTAC] ;;

   let trkid_apply =
      trkid_equality_apply THENL [ Equal; Equal; Equal; Wintro];;

%%