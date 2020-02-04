%-------------------------------------------------------------------------------------------+
|                                                                                           |
|  tupling.ml:     PRL-extensions for tupling, multifunctions etc.                          |
|                                                                                           |
+-------------------------------------------------------------------------------------------%



%  I. Constructors, Destructors & Predicates
   -----------------------------------------
%


%  Ia:   Constructors
   ------------------
%

   
   let make_tup2_term a b              =  instantiate_def `tup2` [a;b];;
   let make_tup3_term a b c            =  instantiate_def `tup3` [a;b;c];;
   let make_tup4_term a b c d          =  instantiate_def `tup4` [a;b;c;d];;
   let make_where2_term t a b term     =  instantiate_def `detup2` [t;mvar a;mvar b;term];;
   let make_where3_term t a b c term   =
      instantiate_def `detup3` [t;mvar a;mvar b;mvar c;term];;
   let make_where4_term t a b c d term =
      instantiate_def `detup4` [t;mvar a;mvar b;mvar c;mvar d;term];;
   let make_id_function_term           =  make_lambda_term `x` (mvar `x`);;
   let make_lambda2_term x1 x2 t       =  instantiate_def `fun2`  [mvar x1;mvar x2;t];;
   let make_apply2_term f a b          =  make_apply_term f (make_tup2_term a b);;
   let id                              =  make_id_function_term;;

   % Additional helpful constructs%

   let make_equal_int_term terms    =  make_equal_term INT terms;;



%  Ib:   Destructors
   ------------------
%

   let destruct_tup2 t        =  destruct_pair t;;
   let destruct_tup3 t        =  let a,bc = destruct_tup2 t in a,(destruct_tup2 bc);;
   let destruct_tup4 t        =  let a,bcd = destruct_tup2 t in a,(destruct_tup3 bcd);;
   let destruct_where2 t      =  
      let term,spreadterm = destruct_spread t in 
         let [a;b],T = destruct_bound_id spreadterm in
            T,a,b,term
   ;;
   let destruct_where3 t      =  
      let t1,a,h1,term = destruct_where2 t in 
         let T,b,c,h1   = destruct_where2 t1 in
            T,a,b,c,term
   ;;
   let destruct_where4 t      =
      let t1,a,h1,term = destruct_where2 t in 
         let T,b,c,d,h1 = destruct_where3 t1 in
            T,a,b,c,d,term 
   ;;
   let destruct_lambda2 t     =  
      let T,x,y,xx = destruct_where2 (snd (destruct_lambda t)) in x,y,T ;;
   let destruct_apply2 t      =
      let f,x  = destruct_apply t in f,(destruct_tup2 x);;

   % Additional helpful constructs%

   let destruct_equal_int t   = 
      let terms,type = destruct_equal t in  if type = INT then terms else fail ;;

   

%  Ic:   Predicates
   ------------------
%
   let is_tup2_term t            =  is_pair_term t;;
   let is_tup3_term t            =  
      (is_tup2_term t) & (is_tup2_term (snd (destruct_tup2 t)));;
   let is_tup4_term t            =  
      (is_tup2_term t) & (is_tup3_term (snd (destruct_tup2 t)));;
   let is_where2_term t          =  is_spread_term t;;
   let is_where3_term t          =  
      (is_where2_term t) & (is_where2_term (fst (destruct_where2 t)));;
   let is_where4_term t          =  
      (is_where2_term t) & (is_where3_term (fst (destruct_where2 t)));;
   let is_id_function_term t     =
      (is_lambda_term t) & (let x,term = destruct_lambda t in term = make_var_term x);;
   let is_lambda2_term t         =  
      (let x,y,T = destruct_lambda2 t in  t = make_lambda2_term x y T) ? false;;
   let is_apply2_term t          =
      (is_apply_term t) & (is_tup2_term (snd (destruct_apply t)));;





%  II. Rules
   ---------
%




%  IIb:  Introduction                        
%
   
   let tup2_equality level proof    =
      (let id = fst (destruct_product (snd (destruct_equal (conclusion proof))))
       in
         if id = `NIL`
            then refine product_equality_pair_independent
            else refine (product_equality_pair level (new id proof))
      ) proof
   ;;
   
   letrec tup_equality level        =
      tup2_equality level THENL [IDTAC; TRY (tup_equality level); IDTAC] ;;

   letrec tup_equality_for n level  =
      if n = 1
         then IDTAC
         else tup2_equality level THENL [IDTAC; tup_equality_for (n-1) level; IDTAC];;

   let tup3_equality                = tup_equality_for 3;;
   let tup4_equality                = tup_equality_for 4;;


   let Where2Equality using a b proof  =
      (refine (product_equality_spread `nil` NIL using (new a proof) (new b proof))) proof;;

   let where2_equality using proof     =
      (let t,a,b,x = destruct_where2 (hd (fst (destruct_equal (conclusion proof))))
       in
         Where2Equality using a b
      ) proof
   ;;
   
   let Where3Equality using level x a b c proof =
      (let l         = length (hypotheses proof)
       and a,b,c,bc  = (new a proof),(new b proof),(new c proof),(new `bc` proof)
       and id,A,prod = destruct_product using
       in
         let new_using  = substitute prod [(mvar id),(mvar a)]
         and a_bc       = make_tup2_term (mvar a)(mvar bc)
         and abc        = make_tup3_term (mvar a)(mvar b)(mvar c)
         in
                  Where2Equality using a bc
            THENL [ IDTAC
                  ;       Where2Equality new_using b c
                    THENL [ Equal
                          ; Seq  [ make_equal_term using [a_bc;abc]
                                 ; make_equal_term using [x;abc]   
                                 ]
                           THENL [      tup2_equality level 
                                  THENL [Equal;Equal] 
                                        @ (if id = `NIL` 
                                             then [] 
                                             else [Thinning [l+1;l+2;l+3;l+4;l+5;l+6] ] )
                                 ; Equal
                                 ; Thinning [ l+2;l+3;l+6;l+7 ]
                                 ]
                          ]
                  ]
      ) proof
   ;;

   let where3_equality using level  proof    =
      (let t,a,b,c,x = destruct_where3 (hd (fst (destruct_equal (conclusion proof))))
       in
         Where3Equality using level x a b c
      ) proof
   ;;

   let Where4Equality using level x a b c d  proof =
      (let l            = length (hypotheses proof)
       and a,b,c,d,bcd  = (new a proof),(new b proof),(new c proof),(new d proof)
                         ,(new `bcd` proof)
       and id,A,prod = destruct_product using
       in
         let new_using  = substitute prod [mvar id, mvar a]
         and a_bcd      = make_tup2_term (mvar a)(mvar bcd)
         and abcd       = make_tup4_term (mvar a)(mvar b)(mvar c)(mvar d)
         in
                  Where2Equality using a bcd
            THENL [ IDTAC
                  ;       Where3Equality new_using level (mvar bcd) b c d
                    THENL [ Equal ]
                          @ (if (fst (destruct_product prod)) = `NIL`
                              then [] else [ Thinning [l+2;l+3]]
                            )
                          @ [Seq   [ make_equal_term using [a_bcd;abcd]
                                   ; make_equal_term using [x;abcd]   ]
                             THENL [      tup2_equality level 
                                    THENL if id = `NIL` 
                                           then [Equal;Equal]
                                           else [Equal;Equal
                                                ;Thinning [l+1;l+2;l+3;l+4;l+5;l+6;l+7] ] 
                                   ; Equal
                                   ; Thinning [l+2;l+3;l+7;l+8]
                                   ] 
                            ]
                  ]
      ) proof
   ;;

   let where4_equality using level proof     =
      (let t,a,b,c,d,x = destruct_where4 (hd (fst (destruct_equal (conclusion proof))))
       in
         Where4Equality using level x a b c d 
      ) proof
   ;;

   let lambda2_equality level proof =
      (let using  = fst (snd (destruct_function (snd (destruct_equal (conclusion proof)))))
       and l      = length (hypotheses proof)
       in
               refine (function_equality_lambda level (new `xx` proof))
         THENL [ where2_equality using THENL [Equal; Thinning [l+1;l+4] ] ; IDTAC ]
      ) proof
   ;;

   let apply2_equality using level     =
      refine (function_equality_apply using) THENL [IDTAC; tup2_equality level] ;;

   
   %  ----------  Now everything together by one rule-name  -------------  %

   





   

%  III. Tactics
   ------------
%

   %  COMPUTATION%


   let Compute_apply2_arg2 howoften proof =
      (let fxw.rest,T = destruct_equal (conclusion proof) in
         let f,x,w = destruct_apply2 fxw  in
            let tagged_fxw = make_apply2_term f x (make_tagged_term howoften w)
            in
               Direct_computation (make_equal_term T (tagged_fxw.rest))
      ) proof
   ;;

   let Compute_snd_apply2_arg2 howoften proof   =
      (let [t;fxw],T = destruct_equal (conclusion proof)  in
         let f,x,w = destruct_apply2 fxw  in
            let tagged_fxw = make_apply2_term f x (make_tagged_term howoften w)
            in
               Direct_computation (make_equal_term T [t;tagged_fxw])
      ) proof
   ;;

   let Compute_apply2_arg1 howoften proof =
      (let fxw.rest,T = destruct_equal (conclusion proof) in
         let f,x,w = destruct_apply2 fxw  in
            let tagged_fxw = make_apply2_term f (make_tagged_term howoften x) w
            in
               Direct_computation (make_equal_term T (tagged_fxw.rest))
      ) proof
   ;;

   let Compute_snd_apply2_arg1 howoften proof   =
      (let [t;fxw],T = destruct_equal (conclusion proof)  in
         let f,x,w = destruct_apply2 fxw  in
            let tagged_fxw = make_apply2_term f (make_tagged_term howoften x) w
            in
               Direct_computation (make_equal_term T [t;tagged_fxw])
      ) proof
   ;;

   let Compute_apply2_fun howoften proof  =
      (let fxw.rest,T = destruct_equal (conclusion proof) in
         let f,x,w = destruct_apply2 fxw  in
            let tagged_fxw = make_apply2_term (make_tagged_term howoften f) x w
            in
               Direct_computation (make_equal_term T (tagged_fxw.rest))
      ) proof
   ;;

   let Compute_snd_apply2_fun howoften proof =
      (let [t;fxw],T = destruct_equal (conclusion proof)  in
         let f,x,w = destruct_apply2 fxw  in
            let tagged_fxw = make_apply2_term (make_tagged_term howoften f) x w
            in
               Direct_computation (make_equal_term T [t;tagged_fxw])
      ) proof
   ;;



%%