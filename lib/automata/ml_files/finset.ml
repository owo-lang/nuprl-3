%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  finset.ml:     PRL-extensions for natural numbers/ finite sets etc.                      |
|                                                                                           |
+-------------------------------------------------------------------------------------------%


%  I. Constructors, Destructors & Predicates
   -----------------------------------------
%

%  Ia: Constructors
   ----------------
%
   let make_leq_term i j         = instantiate_def `leq` [i;j];;
   let make_uneq_term i j        = instantiate_def `uneq` [i;j];;
   let make_nat_term             = instantiate_def `N` [];;
   let make_nbar_term j          = instantiate_def `nbar` [j];;
   let make_nbar1_term j         = instantiate_def `nbar1` [j];;
   let make_finite_term          = instantiate_def `finite` [];;
   let make_finset_term A        = instantiate_def `finset` [A];;
   let nat                       = make_nat_term;;
   let finite_sets               = make_finite_term;;


%  Ib: Destructors
   ---------------
%
   let destruct_leq t            =
      let i_1,j = destruct_less t in (fst (destruct_subtraction i_1)),j ;;

   let destruct_uneq t           = 
      let [i;j],T = destruct_equal (destruct_not t) in i,j ;;

   let destruct_nbar t           =
      let id,(A,B) = destruct_set t in
         let (),l,r = destruct_product B in
            snd (destruct_leq r)
   ;;

   let destruct_nbar1            = destruct_nbar;;

   let destruct_finset t         = destruct_nbar t;;


%  Ic: Predicates
   --------------
%


%  II. Rules
   ---------
%

%  IIa: Formation
   --------------
%

   let nat_intro  proof          =
      (      refine (set_formation (new `i` proof)) 
      THENL [refine integer_equality; 
             refine less_equality THENL [Int_minus THEN Int_number; Equal]
            ]
      ) proof
   ;;

   let finset_intro = nat_intro;;

%  IIb: Introduction
   -----------------
%

   let finset_equality_conversion = Cumulativity THEN THEOREM `finsettype`;;

%  IIc: Elimination
   ----------------
%

%  IId: Computation
   ----------------
%

%%