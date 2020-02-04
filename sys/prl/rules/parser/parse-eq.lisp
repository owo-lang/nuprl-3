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


(defun parse-eq-intro-rule$ ()
    (Plet (terms-type   (terms-kind (terms-of-equal-term ref-concl))
          equal-type   (kind-of-term (type-of-equal-term ref-concl))
          level        nil
          term-id-pair nil
	  term-id-pair-list nil
          using-term   nil
	  using-term-list nil
          new-ids      nil
         ) 
        (Pif (and (eql terms-type 'UNIVERSE) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-UNIVERSE)

         || (and (eql terms-type 'VOID) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-VOID)
     
         || (eql terms-type 'ANY) -->
            (equal-intro-rule 'EQUAL-INTRO-ANY) 

         || (and (eql terms-type 'ATOM) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-ATOM)

         || (and (eql terms-type 'TOKEN) (eql equal-type 'ATOM)) -->
            (equal-intro-rule 'EQUAL-INTRO-TOKEN)

         || (and (eql terms-type 'OBJECT) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-OBJECT)

	 || (eql equal-type 'OBJECT) -->
	    (cond ((eql token-type TEndInput)
		   (equal-intro-rule-using 'EQUAL-INTRO-OBJECT-MEMBER nil nil nil))
		  (t
		   (check-token-type TUsing)
		   (Plet (term (catch 'process-err (parse-from-current-Ttree)))
			(cond ((eql (car term) 'ERR)
			       (ref-error '|Expecting a term after "using"|))
			      (t 
			       (equal-intro-rule-using 'EQUAL-INTRO-OBJECT-MEMBER nil term nil))))))

         || (and (eql terms-type 'INT) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-INT)

         || (eql terms-type 'IND) -->
            (<- term-id-pair (check-for-over-part$))
            (<- new-ids (get-n-new-ids$ 2))
            (equal-intro-rule-over 'EQUAL-INTRO-IND term-id-pair new-ids)

         || (and (eql terms-type 'LIST) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-LIST)

         || (and (eql terms-type 'NIL) (eql equal-type 'LIST)) -->
            (<- level (check-for-univ-level$))
            (equal-intro-rule-level 'EQUAL-INTRO-NIL level nil)
            
         || (and (eql terms-type 'CONS) (eql equal-type 'LIST)) -->
            (equal-intro-rule 'EQUAL-INTRO-CONS)

         || (eql terms-type 'LIST-IND) -->
            (<- term-id-pair (check-for-over-part$))
            (<- using-term (check-for-using-term$ 'LIST))
            (<- new-ids (get-n-new-ids$ 3))
            (equal-intro-rule-using
                   'EQUAL-INTRO-LIST-IND term-id-pair using-term new-ids
            )

         || (and (eql terms-type 'UNION) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-UNION)

         || (and (eql terms-type 'INL) (eql equal-type 'UNION)) -->
            (<- level (check-for-univ-level$))
            (equal-intro-rule-level 'EQUAL-INTRO-INL level nil)

         || (and (eql terms-type 'INR) (eql equal-type 'UNION)) -->
            (<- level (check-for-univ-level$))
            (equal-intro-rule-level 'EQUAL-INTRO-INR level nil)

         || (eql terms-type 'DECIDE) -->
            (<- term-id-pair (check-for-over-part$))
            (<- using-term (check-for-using-term$ 'UNION))
            (<- new-ids (get-n-new-ids$ 2))
            (equal-intro-rule-using
                    'EQUAL-INTRO-DECIDE term-id-pair using-term new-ids
            )

         || (and (eql terms-type 'PRODUCT) (eql equal-type 'UNIVERSE)) -->
            (<- new-ids (get-n-new-ids$ 1))
            (equal-intro-rule-new-id 'EQUAL-INTRO-PRODUCT (set-new-id$ new-ids))
 
         || (and (eql terms-type 'PAIR) (eql equal-type 'PRODUCT)) -->
	    (<- level (check-for-univ-level$))
	    (<- new-ids (get-n-new-ids$ 1))
	    (equal-intro-rule-level  
	      'EQUAL-INTRO-PAIR level (set-new-id$ new-ids))
;            (Pif (null 
;                  (bound-id-of-product-term (type-of-equal-term ref-concl))
;                ) -->
;                (equal-intro-rule-level 'EQUAL-INTRO-PAIR nil nil)
;             || t -->
;                (equal-intro-rule-level  
;                    'EQUAL-INTRO-PAIR level (set-new-id$ new-ids)
;                )
;             fi)

         || (eql terms-type 'SPREAD) -->
            (<- term-id-pair (check-for-over-part$))
            (<- using-term (check-for-using-term$ 'PRODUCT))
            (<- new-ids (get-n-new-ids$ 2))
            (equal-intro-rule-using
                    'EQUAL-INTRO-SPREAD term-id-pair using-term new-ids
            )

         || (and (eql terms-type 'FUNCTION) (eql equal-type 'UNIVERSE)) -->
            (<- new-ids (get-n-new-ids$ 1))
            (equal-intro-rule-new-id
                'EQUAL-INTRO-FUNCTION (set-new-id$ new-ids)
            )

	 || (and (eql terms-type 'PARFUNCTION) (eql equal-type 'UNIVERSE)) -->
	    (<- new-ids (get-n-new-ids$ 1))
	    (equal-intro-rule-new-id
	        'EQUAL-INTRO-PARFUNCTION (set-new-id$ new-ids))

	 || (and (eql terms-type 'RECURSIVE) (eql equal-type 'UNIVERSE)) -->
	    (<- using-term-list (check-for-using-term-list$))
	    (equal-intro-rule-recursive 'EQUAL-INTRO-RECURSIVE using-term-list)

	 || (and (eql terms-type 'SIMPLE-REC) (eql equal-type 'UNIVERSE)) -->
	    (equal-intro-rule-simple-rec
		'EQUAL-INTRO-SIMPLE-REC (set-new-id$ (get-n-new-ids$ 1)))

	 || (eql equal-type 'RECURSIVE) -->
	    (<- level (check-for-univ-level$))
	    (equal-intro-rule-level
	        'EQUAL-INTRO-REC-MEMBER level nil)

	 || (eql equal-type 'SIMPLE-REC) -->
	    (<- level (check-for-univ-level$))
	    (equal-intro-rule-level
	        'EQUAL-INTRO-SIMPLE-REC-MEMBER level nil)
    
         || (and (eql terms-type 'LAMBDA) (eql equal-type 'FUNCTION)) -->
            (<- level (check-for-univ-level$))
            (<- new-ids (get-n-new-ids$ 1))
            (equal-intro-rule-level 
                'EQUAL-INTRO-LAMBDA level (set-new-id$ new-ids)
            )

	 || (and (eql terms-type 'FIX) (eql equal-type 'PARFUNCTION)) -->
	    (<- level (check-for-univ-level$))
	    (<- using-term-list (check-for-using-term-list$))
	    (equal-intro-rule-fix 'EQUAL-INTRO-FIX level using-term-list nil)

         || (eql terms-type 'APPLY) -->
            (<- using-term (check-for-using-term$ 'FUNCTION))
	    (<- new-ids (get-n-new-ids$ 1))
            (equal-intro-rule-using 'EQUAL-INTRO-APPLY nil using-term new-ids)

         || (eql terms-type 'APPLY-PARTIAL) -->
            (<- using-term (check-for-using-term$ 'PARFUNCTION))
	    (<- new-ids (get-n-new-ids$ 1))
            (equal-intro-rule-using 'EQUAL-INTRO-APPLY-PARTIAL nil using-term new-ids)

	 || (eql terms-type 'REC-IND) -->
	    (<- term-id-pair-list (check-for-over-part-list$))
	    (check-token-type TUsing)
	    (<- using-term (parse-bound-id-term 1))
	    (check-token-type TComma)
	    (<- using-term-list (cons using-term (check-for-term-list$)))
	    (<- level (check-for-univ-level$))
	    (Pif (eql 'RECURSIVE (kind-of-term (term-of-bound-id-term using-term))) -->
		(equal-intro-rule-rec-ind
		  'EQUAL-INTRO-REC-IND level term-id-pair-list using-term-list
		)
	     || t -->
	        (ref-error
		 '|expecting a term of the form id.rec(...) as first term in using list.|
		)
	     fi)
	 || (eql terms-type 'SIMPLE-REC-IND) -->
	    (<- term-id-pair (check-for-over-part$))
	    (<- using-term (check-for-using-term$ '|rec|))
	    (<- level (check-for-univ-level$))
	    (<- new-ids (check-for-new-ids))
	    (Pif (eql 'SIMPLE-REC (kind-of-term using-term)) -->
		(equal-intro-rule-simple-rec-ind
	              'EQUAL-INTRO-SIMPLE-REC-IND level term-id-pair using-term new-ids)	
	     || t -->
	        (ref-error
		 '|expecting a simple rec term as the using term.|
		)
	     fi)

         || (and (eql terms-type 'QUOTIENT) (eql equal-type 'UNIVERSE)) -->
            (Pif (onep (length (terms-of-equal-term ref-concl))) -->
                (<- new-ids (get-n-new-ids$ 3))
             || t -->
                (<- new-ids (get-n-new-ids$ 2))
             fi)
            (equal-intro-rule-quotient 'EQUAL-INTRO-QUOTIENT new-ids)

         || (eql equal-type 'QUOTIENT) -->
            (<- level (check-for-univ-level$))
            (equal-intro-rule-level 'EQUAL-INTRO-QUOTIENT-ELEM level nil)

         || (and (eql terms-type 'SET) (eql equal-type 'UNIVERSE)) -->
            (Pif (eql token-type TNew) -->
                (scan)
                (equal-intro-rule-new-id 'EQUAL-INTRO-SET (check-type-and-return-value TId))
             || t -->
                (equal-intro-rule-new-id 'EQUAL-INTRO-SET nil)
             fi)

         || (eql equal-type 'SET) -->
            (equal-intro-rule-level
	      'EQUAL-INTRO-SET-ELEM
	      (check-for-univ-level$)
	      (car (check-for-new-ids)))

         || (and (eql terms-type 'EQUAL) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-EQUAL)
         
         || (and (eql terms-type 'AXIOM) (eql equal-type 'EQUAL)) -->
            (equal-intro-rule 'EQUAL-INTRO-AXIOM-EQUAL)

         || (and (eql terms-type 'LESS) (eql equal-type 'UNIVERSE)) -->
            (equal-intro-rule 'EQUAL-INTRO-LESS)

         || (and (eql terms-type 'AXIOM) (eql equal-type 'LESS)) -->
            (equal-intro-rule 'EQUAL-INTRO-AXIOM-LESS)

         || (and (eql terms-type 'ADD) (eql equal-type 'INT)) -->
            (equal-intro-rule 'EQUAL-INTRO-ADD)

         || (and (eql terms-type 'SUB) (eql equal-type 'INT)) -->
            (equal-intro-rule 'EQUAL-INTRO-SUB)

         || (and (eql terms-type 'MUL) (eql equal-type 'INT)) -->
            (equal-intro-rule 'EQUAL-INTRO-MUL)

         || (and (eql terms-type 'DIV) (eql equal-type 'INT)) -->
            (equal-intro-rule 'EQUAL-INTRO-DIV)

         || (and (eql terms-type 'POS-NUMBER) (eql equal-type 'INT)) -->
            (equal-intro-rule 'EQUAL-INTRO-POS-NUMBER)

         || (and (eql terms-type 'MINUS) (eql equal-type 'INT)) -->
            (equal-intro-rule 'EQUAL-INTRO-MINUS)

         || (and (eql terms-type 'MOD) (eql equal-type 'INT)) -->
            (equal-intro-rule 'EQUAL-INTRO-MOD)

         || (eql terms-type 'ATOMEQ) -->
            (equal-intro-rule 'EQUAL-INTRO-ATOMEQ)

         || (eql terms-type 'INTEQ) -->
            (equal-intro-rule 'EQUAL-INTRO-INTEQ) 
    
         || (eql terms-type 'INTLESS) -->
            (equal-intro-rule 'EQUAL-INTRO-INTLESS)

         || (eql terms-type 'VAR) -->
            (equal-intro-rule 'EQUAL-INTRO-VAR)

	 || (eql terms-type 'DOM) -->
	    (<- using-term (check-for-using-term$ 'PARFUNCTION))
	    (equal-intro-rule-using 'EQUAL-INTRO-DOM nil using-term nil)

         || t -->
            (ref-error '|no equality intro rule will work on this goal |)
            
         fi)
    )
)

(defun terms-kind (terms)
    (Pif (onep (length terms)) -->
        (kind-of-term (car terms))

     || (eql (kind-of-term (car terms)) (terms-kind (cdr terms))) -->
        (kind-of-term (car terms))

     || t -->
        'TERM-KINDS-DONT-MATCH
        
     fi)
)

(defun check-for-over-part$ ()
    (Pif (eql token-type TOver) -->
        (scan)
        (Plet (id (check-type-and-return-value TId))
            (check-token-type TPeriod)
            (cons
                id
                (check-for-term$ '|expecting a term after 'over id.' |)
            )
        )
     || t -->
        nil
     fi)
)

(defun check-for-over-part-list$ ()
    (Plet (first-pair (check-for-over-part$))
	 (Pif (null first-pair) -->
	     nil

	  || t -->
	     (Plet (over-pair-list (list first-pair))
		  (Ploop
		    (while (eql token-type TComma))
		    (do
		      (scan)
		      (Plet (id (check-type-and-return-value TId))
			   (check-token-type TPeriod)
			   (<- over-pair-list
			       (cons
				 (cons
				   id
				   (check-for-term$ (concat '|expecting a term after | id))
				 )
				 over-pair-list
			       )
 			   )
		       )
		    )
		  )
		  (nreverse over-pair-list)
	     )

	  fi)
    )
)

(defun check-for-using-term$ (kind-needed)
    (check-token-type TUsing)
    (check-for-term$         
        (concat '|expecting a | kind-needed '| term after 'using' |)
    )
)

(defun check-for-using-term-list$ ()
    (Pif (eql token-type TUsing) -->
	(scan)
        (check-for-term-list$)

    || t --> nil

    fi)
)
(defun check-for-term-list$ ()
     (Plet (term-list (list (check-for-term$ '|expecting a term after 'using' |)))
	     (Ploop
	       (while (eql token-type TComma))
	       (do
		 (scan)
	         (<- term-list
		     (cons
		       (check-for-term$ '|expecting a term after comma. |)
		       term-list
		     )
	         )
	       )
	     )
	     (nreverse term-list)
        )
)

(defun get-n-new-ids$ (n)
    (Pif (eql token-type TNew) -->
        (scan)
        (get-n-ids$ n)

     || t -->
        nil
     fi)
)

(defun get-n-ids$ (n)
    (Pif (onep n) -->
        (list (check-types-and-return-value (list TId TNil)))

     || t -->
        (Plet (id (check-types-and-return-value (list TId TNil)))
            (check-token-type TComma)
            (cons id (get-n-ids$ (1- n)))
        )
     fi)
)

(defun set-new-id$ (id-list)
    (Pif id-list -->
        (car id-list)
     || t -->
        nil
     fi)
)
 
