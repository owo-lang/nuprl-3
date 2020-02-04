;;; -*- Package: Nuprl; Syntax: Common-lisp; Base: 10. -*-


;;;************************************************************************
;;;                                                                       *
;;;                Nuprl Proof Development System                         *
;;;                ------------------------------                         *
;;;                                                                       *
;;;   Developed by the Nuprl group, Department of Computer Science,       *
;;;   Cornell University, Ithaca NY.  See the release notes for a list    *
;;;   of the members of the group.                                        *
;;;                                                                       *
;;;   Permission is granted to use and modify Nuprl provided this notice  *
;;;   is retained in derived works.                                       *
;;;                                                                       *
;;;                                                                       *
;;;************************************************************************



(in-package "NUPRL")


(constant rule-to-Ttree-table                   
  (list
    '(APPLY-COMP (L |reduce |)  (2 N))
    '(DECIDE-COMP (L |reduce |) (2 N))
    '(IND-COMP-DOWN 
                (L |reduce |) (2 N) (L |down |)
     )
    '(IND-COMP-BASE 
                (L |reduce |) (2 N) (L |base |)
     )
    '(IND-COMP-UP (L |reduce |) (2 N) (L |up |))
    '(LIST-IND-COMP (L |reduce |) (2 N))
    '(SPREAD-COMP (L |reduce |) (2 N))
    '(FIX-COMP (L |reduce |) (2 N))
    '(REC-IND-COMP (L |reduce |) (2 N) )
    '(SIMPLE-REC-IND-COMP (L |reduce |) (2 N))
    '(DOM-COMP (L |reduce |) (2 N) (3 WS))
    '(ATOMEQ-COMP-TRUE (L |reduce |) (L |true |) (2 N)) 
    '(ATOMEQ-COMP-FALSE (L |reduce |) (L |false |) (2 N))
    '(INTEQ-COMP-TRUE (L |reduce |) (L |true |) (2 N))
    '(INTEQ-COMP-FALSE (L |reduce |) (L |false |) (2 N))
    '(INTLESS-COMP-TRUE (L |reduce |) (L |true |) (2 N))
    '(INTLESS-COMP-FALSE (L |reduce |) (L |false |) (2 N))
    '(ATOM-INTRO (L |intro |) (2 T))
    '(EQUAL-INTRO-UNIVERSE (L |intro |))
    '(EQUAL-INTRO-AXIOM-EQUAL (L |intro |))
    '(EQUAL-INTRO-EQUAL (L |intro |))
    '(EQUAL-INTRO-LESS (L |intro |))  
    '(EQUAL-INTRO-AXIOM-LESS (L |intro |))
    '(EQUAL-INTRO-ADD (L |intro |))
    '(EQUAL-INTRO-SUB (L |intro |))
    '(EQUAL-INTRO-MUL (L |intro |))
    '(EQUAL-INTRO-DIV (L |intro |))
    '(EQUAL-INTRO-MOD (L |intro |))
    '(EQUAL-INTRO-POS-NUMBER (L |intro |))
    '(EQUAL-INTRO-MINUS (L |intro |))
    '(EQUAL-INTRO-VOID (L |intro |))
    '(EQUAL-INTRO-ANY (L |intro |))  
    '(EQUAL-INTRO-TOKEN (L |intro |))
    '(EQUAL-INTRO-ATOM (L |intro |))
    '(EQUAL-INTRO-INT (L |intro |))
    '(EQUAL-INTRO-OBJECT (L |intro |))
    '(EQUAL-INTRO-IND (L |intro |) (IF 2 (2 V)) (3 WS))
    '(EQUAL-INTRO-LIST (L |intro |))  
    '(EQUAL-INTRO-NIL (L |intro |) (IF 2 (2 U)))
    '(EQUAL-INTRO-CONS (L |intro |))
    '(EQUAL-INTRO-LIST-IND (L |intro |) (IF 2 (2 V)) (3 G) (4 WS))
    '(EQUAL-INTRO-UNION (L |intro |))
    '(EQUAL-INTRO-INL (L |intro |) (2 U))
    '(EQUAL-INTRO-INR (L |intro |) (2 U))
    '(EQUAL-INTRO-DECIDE (L |intro |) (IF 2 (2 V)) (3 G) (4 WS))
    '(EQUAL-INTRO-PRODUCT (L |intro |) (2 W))
    '(EQUAL-INTRO-PAIR (L |intro |) (2 U) (3 W))
    '(EQUAL-INTRO-SPREAD (L |intro |) (IF 2 (2 V)) (3 G) (4 WS))
    '(EQUAL-INTRO-FUNCTION (L |intro |) (2 W))
    '(EQUAL-INTRO-PARFUNCTION (L |intro |) (2 W))
    '(EQUAL-INTRO-LAMBDA (L |intro |) (2 U) (3 W))
    '(EQUAL-INTRO-APPLY (L |intro |) (3 G) (4 WS))
    '(EQUAL-INTRO-APPLY-PARTIAL (L |intro |) (3 G) (4 W))
    '(EQUAL-INTRO-DOM (L |intro |) (3 G))
    '(EQUAL-INTRO-FIX (L |intro |) (2 U) (3 GL) )
    '(EQUAL-INTRO-QUOTIENT (L |intro new |) (2 WS))
    '(EQUAL-INTRO-QUOTIENT-ELEM (L |intro |) (2 U))
    '(EQUAL-INTRO-SET (L |intro |) (2 W))
    '(EQUAL-INTRO-SET-ELEM (L |intro |) (2 U))
    '(EQUAL-INTRO-VAR (L |intro |))
    '(EQUAL-INTRO-ATOMEQ (L |intro |))
    '(EQUAL-INTRO-INTEQ (L |intro |))
    '(EQUAL-INTRO-INTLESS (L |intro |))
    '(EQUAL-INTRO-OBJECT-MEMBER (L |intro |) (IF 3 (L |using |) (3 T)))
    '(EQUAL-INTRO-RECURSIVE-WITH-FIX (L |intro |) (2 GL))
    '(EQUAL-INTRO-RECURSIVE-WITHOUT-FIX (L |intro |) (2 GL))
    '(EQUAL-INTRO-SIMPLE-REC (L |intro |) (IF 2 (2 W)))
    '(EQUAL-INTRO-REC-MEMBER (L |intro |) (2 U))
    '(EQUAL-INTRO-SIMPLE-REC-MEMBER (L |intro |) (2 U))
    '(EQUAL-INTRO-REC-IND-WITH-FIX
       (L |intro |) (3 VL) (4 GL) (5 WS) (2 U)
     )
    '(EQUAL-INTRO-REC-IND-WITHOUT-FIX
       (L |intro |) (3 VL) (4 GL) (5 WS) (2 U)
     )
    '(EQUAL-INTRO-SIMPLE-REC-IND
       (L |intro |) (3 V) (4 G) (2 U) (5 WS)
     )
    '(FUNCTION-INTRO (L |intro |) (2 U) P (3 W))
    '(RECURSIVE-INTRO (L |intro |) (2 U))
    '(SIMPLE-REC-INTRO (L |intro |) (2 U))
    '(INT-INTRO-OP (L |intro |) (2 S))
    '(INT-INTRO-NUMBER (L |intro |) (2 N))
    '(LESS-INTRO (L |intro |))
    '(LIST-INTRO-NIL (L |intro nil|) (2 U))
    '(LIST-INTRO-CONS (L |intro|))
    '(PRODUCT-INTRO (L |intro |) (IF 3 (2 U) P (3 T) (4 W)))
    '(QUOTIENT-INTRO (L |intro |) (2 U) P (3 T))
    '(SET-INTRO (L |intro |) (IF 3 (2 U) P (3 T) (4 W)))
    '(UNION-INTRO (L |intro |) (2 U) P (3 S))
    '(UNIVERSE-INTRO-ATOM (L |intro atom |))
    '(UNIVERSE-INTRO-EQUAL (L |intro equality |) (2 T) P (3 N))
    '(UNIVERSE-INTRO-FUNCTION (L |intro function |) (IF 2 (3 T) (2 W)))
    '(UNIVERSE-INTRO-INT (L |intro int |))
    '(UNIVERSE-INTRO-LESS (L |intro less |))
    '(UNIVERSE-INTRO-LIST (L |intro list |) (2 T))
    '(UNIVERSE-INTRO-UNION (L |intro union |))
    '(UNIVERSE-INTRO-PRODUCT (L |intro product |) (IF 2 (3 T) (2 W)))     
    '(UNIVERSE-INTRO-QUOTIENT (L |intro quotient |) (2 T) C (3 T) (4 WS))
    '(UNIVERSE-INTRO-SET (L |intro set |) (IF 3 (3 T) (2 W)))
    '(UNIVERSE-INTRO-UNIVERSE (L |intro universe |) (2 U))
    '(UNIVERSE-INTRO-VOID (L |intro void |))
    '(FUNCTION-ELIM 
        (L |elim |) (2 N) (4 WS) (IF 3 (L | on |) (3 T))  
     )
    '(PARFUNCTION-ELIM
         (L |elim |) (2 N) (IF 3 (L | on |) (3 T)) (4 WS)
     )
    '(RECURSIVE-WITH-FIX-ELIM
       (L |elim |) (2 N) (IF 4 (4 VL)) (IF 5 (5 GL)) (6 WS) (3 U)
     )
    '(RECURSIVE-WITHOUT-FIX-ELIM
       (L |elim |) (2 N) (IF 4 (4 VL)) (IF 5 (5 GL)) (6 WS) (3 U)
     )
    '(SIMPLE-REC-ELIM (L |elim |) (2 N) (3 U) (4 WS))
    '(RECURSIVE-UNROLL-ELIM (L |elim |) (2 N) (4 WS))
    '(SIMPLE-REC-UNROLL-ELIM (L |elim |) (2 N) (3 W))
    '(INT-ELIM (L |elim |) (2 N)  (3 WS))
    '(LIST-ELIM (L |elim |) (2 N)  (3 WS))
    '(PRODUCT-ELIM (L |elim |) (2 N)  (3 WS))
    '(QUOTIENT-ELIM (L |elim |) (2 N) (3 U)  (4 WS))
    '(SET-ELIM (L |elim |) (2 N) (3 U)  (4 WS))
    '(UNION-ELIM (L |elim |) (2 N)  (3 WS))
    '(VOID-ELIM (L |elim |) (2 N))
    '(HYP (L |hyp |) (2 N))
    '(LEMMA (L |lemma |) (2 A)  (3 W))
    '(DEF (L |def |) (2 A)  (3 W))
    '(SEQUENCE (L |seq |) (2 TS)  (3 WS))
    '(EXPLICIT-INTRO (L |explicit intro |) (2 T))
    '(CUMULATIVITY (L |cumulativity |) (2 U))
    '(EQUALITY (L |equality |))
    '(ARITH (L |arith |) (2 U))
    '(SUBSTITUTE (L |subst |) (2 U) P (3 T) (L | over |) (4 T) )
    '(BECAUSE (L |because |))
    '(TACTIC (2 I))
    '(EXPERIMENTAL (L |experimental |) (2 I))
    '(DIRECT-COMP-HYP (L |compute hyp |) (2 N) (L | using |) (3 T))
    '(DIRECT-COMP (L |compute |) (L | using |) (2 T))
    '(THINNING (L |thinning |) (2 NS))
    '(EXTENSIONALITY (L |extensionality |) (2 U) (IF 3 (3 GL)) (4 W))
    '(MONOT (L |monotonicity |) (3 N) P (2 MONO-OP) P (4 N))
    '(DIVISION (L |division |))
  )
)

(defun rule-to-Ttree (rule)
    (Plet (action-sequence (assoc (kind-of-rule rule) rule-to-Ttree-table)
          result          nil
         )
        (Pif (null action-sequence) -->
            (error "~a~^ ~a" '|RULE-TO-TTREE: invalid rule kind -- | (kind-of-rule rule))
         fi)                   
        (<- action-sequence (cdr action-sequence))
        (<- result (cons 'Ttree (process-actions$ action-sequence rule)))
    )
)

(defun process-actions$ (actions rule)
    (Plet (result nil)
        (for (action in actions)
             (do 
                (<- result (append *-* (process-action$ action rule)))
             )
        )
        result
    )
)


(defun process-action$ (action rule)
    (Pif (eql action 'C) -->
        '#.(istring ",")
                                                         
     || (eql action 'P) -->
        '#.(istring " ")

     || (numberp (car action)) -->
        (process-field-action$
            (get-field-contents$ (car action) rule) (cadr action)
        )   

     || (eql (car action) 'L) -->
        (istring (cadr action))

     || (eql (car action) 'IF) -->
        (Pif (null-field (get-field-contents$ (cadr action) rule)) -->
            nil
         || t -->
            (process-actions$ (cddr action) rule)
         fi)

     fi)
)

(defun get-field-contents$ (n rule)
    (nthelem n rule)
)

(defun null-field (field)
    (or (null field)
	(and
	    (consp field)
	    (Ploop
		(local answer t)
		(while (and answer field))
		(do
		    (Pif (car field) --> (<- answer nil) fi)
		    (<- field (cdr field))
		)
		(result answer)
	     )
	 )
     )
)

(defun process-field-action$ (field action)
    (Pif (eql action 'I) -->
        (cdr field)

     || (member action '(A N)) -->
        (istring field)

     || (eql action 'NS) -->
	(Pif (not (null field)) -->
	    (append
		(istring (car field))
		(for (n in (cdr field))
		    (splice (append '#.(istring ",") (istring n)))
		)
	    )
	 || t -->
	    nil
	 fi)

     || (eql action 'T) -->
        (cdr (term-to-Ttree field))       
    
     || (eql action 'V) -->
        (append '#.(istring " over ")
		(istring (car field))
		'#.(istring ".")
		(cdr (term-to-Ttree (cdr field))))

     || (eql action 'VL) -->
	(append
	    '#.(istring " over ")
	    (istring (caar  field))
	    '#.(istring ".")
	    (cdr (term-to-Ttree (cdar field)))
	    (for (term in (cdr field))
		(splice
		    (append
			'#.(istring ",")
			(istring (car term))
			'#.(istring ".")
			;; This copylist and the following are necessary because splice
			;; turns into mapcan which is destructive.  The function
			;; term-to-Ttree returns list structure which may be shared.
			(copy-list
			  (cdr (term-to-Ttree (cdr term))))
		    )
		)
	    )
	)

     || (eql action 'G) -->
        (append '#.(istring " using ") (cdr (term-to-Ttree field)))

     || (eql action 'GL) -->
	(append
	    '#.(istring " using ")
	    (cdr (term-to-Ttree (car field)))
	    (for (term in (cdr field))
		(splice
		  (append '#.(istring ",") (copy-list (cdr (term-to-Ttree term)))))
	    )
	)

     || (eql action 'TS) -->
	(append
	    (cdr (term-to-Ttree (car field)))
            (for (term in (cdr field))
                (splice
		  (append '#.(istring ",") (copy-list (cdr (term-to-Ttree term)))))
            )         
        )

     || (eql action 'U) -->
        (Pif (= field 1) --> nil
	 || t --> (append '#.(istring " at U") (istring field))
	 fi)

     || (eql action 'W) -->
	(Pif (not (null-field field)) -->
	    (append '#.(istring " new ") (istring field))
	 fi)

     || (eql action 'WS) -->
	(Pif (not (null-field field)) -->
	    (append
		'#.(istring " new ")
		(istring (car field))
		(for (id in (cdr field))
		    (splice (append '#.(istring ",") (istring id)))
		)
            )
	 fi)

     || (eql action 'S) -->
        (cdr (assoc
	       field
	       #.`'((,TPlus . ,'#.(istring "+")) (,TMinus . ,'#.(istring "-"))
		    (,TStar . ,'#.(istring "*")) (,TSlash . ,'#.(istring "/"))
		    (,TMod . ,'#.(istring "mod "))  (,TLeft . ,'#.(istring "left "))
		    (,TRight . ,'#.(istring "right ")))))

     || (eql action 'MONO-OP) -->
        (list (cdr (assoc field
			  #.`'((PLUS . ,(ichar #\+ ))
			       (MINUS . ,(ichar #\- ))
			       (MULT . ,(ichar #\* ))
			       (DIV . ,(ichar #\/ ) )) )))

     || (eql action 'BOOL) -->
        (cond (field '#.(istring "true ")) (t '#.(istring "false ")))

     || (eql action 'TOKENS) -->
	(Pif (not (null-field field)) -->
	    (append
		(istring (car field))
		(for (id in (cdr field))
		    (splice (append '#.(istring ",") (istring id)))
		)
            )
	 fi)

     fi)
)
