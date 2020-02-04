
%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  words.ml          PRL_extensions for strings                                             |
|                                                                                           |
|  Rules, tactics  and supplement functions corresponding to the PRL-library "automata"     |
|                                                                                           |
+-------------------------------------------------------------------------------------------%




%  III: Tactics 
   ------------
%



   let Wintro                    = (REPEAT wintro) THEN Equal;;
   let Wmember                   = membertac wintro;;


%  IIIb:    All Introduction and Induction 
   ---------------------------------------
%

   let symbol_all_intro          = All_intro symbol_equality;;
   let word_all_intro            = All_intro word_equality;;


   let word_intro_elim proof     = 
      (let l = length (hypotheses proof) 
       in 
         word_all_intro THEN word_elim (l+1) THEN Thinning [l+1]
      ) proof
   ;;
   let word_induction            = word_intro_elim;;


   let word_tail_induction proof       = 
      (let l = length (hypotheses proof) 
       in 
         word_all_intro THEN word_elim_tail (l+1) THEN Thinning [l+1]
      ) proof
   ;;
   let tail_induction_using tac  =  word_tail_induction THENL [tac; IDTAC; IDTAC];;
   let tail_induction            =  tail_induction_using Wmember;;


   let word_lg_induction proof   = 
      (let l = length (hypotheses proof) 
       in   
         word_all_intro THEN word_elim_lg (l+1) THEN Thinning [l+1]
      ) proof
   ;;
   let lg_induction_using tac    =  word_lg_induction THENL [tac; IDTAC; IDTAC];;
   let lg_induction              =  lg_induction_using Wmember;;




%  IIIc: Some_introduction for words
   ---------------------------------
%

   let word_some_intro level wordlist  =
      let l = length wordlist 
      in
         RepeatSomeIntro level wordlist (list l Wmember) (list l wequal) IDTAC
   ;;



%  IIId: Noteps Introduction
   -------------------------
%
   let word_intro_noteps proof=
      (let a,l = destruct_cons (destruct_noteps (conclusion proof))
       in
         Seq   [make_equal_symbols_term [a]; make_equal_word_term [l] ]
         THENL [ IDTAC
               ; IDTAC
               ; repeat_some_intro 1 [a;l]
                 THENL 
                 [ sequal; wequal
                 ; Ui_equality THENL [wequal;wcons;wcons] THEN Equal
                 ; Equal; Equal; wcons THEN Equal
               ] ]
      ) proof
   ;;
   let wnoteps                = word_intro_noteps;;



%  IIIe: a special variant of con_assoz
   ------------------------------------
%

   let conassoz no proof   = 
     (let [uvw;xyz] = ordered_exp_list no proof in
         let (uv,w),(x,yz) = (destruct_concat uvw),(destruct_concat xyz) in
            let (u,v),(y,z) = (destruct_concat uv),(destruct_concat yz) in
               let uvw1 = make_concat_term u (make_concat_term v w)
               in
                   Seq [make_equal_word_term [u;x];
                        make_equal_word_term [v;y];
                        make_equal_word_term [w;z];
                        make_equal_word_term [uvw1;xyz] ]
                  THENL [IDTAC; IDTAC; IDTAC; THEOREM1 `con_assoz` [u;v;z] THEN Equal; Equal]
     ) proof
   ;;

% --------------------------------------------------------------------------------------- %
