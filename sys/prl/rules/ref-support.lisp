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


;=======================================;
;                                       ;
;   SUPPORT ROUTINES FOR THE REFINER    ;
;                                       ;
;=======================================;

(defun make-child (assums conclusion &optional (new-hidden-given nil) new-hidden)
    (Plet (hidden
             (Pif (member (kind-of-term conclusion) '(EQUAL LESS VOID)) -->
                 nil
              || new-hidden-given -->
                 new-hidden
              || t -->
                 ref-hidden
              fi)
         )
        (proof-tree
            assums conclusion (copy raw-object-Ttree)
            nil nil 'INCOMPLETE hidden
        )
    )
)



;-----------------------------------------------------------;
;                                                           ;
;   GENERAL ROUTINES FOR MANIPULATING TERMS                 ;
;                                                           ;
;-----------------------------------------------------------;

;-- Some definitions to allow us to deal with terms in a sane manner.

(constant terms-with-no-subterms
        '(UNIVERSE VOID ATOM TOKEN INT POS-NUMBER NIL AXIOM
          TERM-OF-THEOREM VAR OBJECT
         )
)
(constant terms-with-a-constant-field
        '(UNIVERSE TOKEN POS-NUMBER TERM-OF-THEOREM)
)
(constant terms-with-no-binding-ids
        '(MINUS ADD SUB MUL DIV MOD IND LIST CONS LIST-IND UNION INL INR
          DECIDE PAIR SPREAD APPLY EQUAL LESS  ATOMEQ INTLESS INTEQ
	  DOM REC-IND FIX RECURSIVE APPLY-PARTIAL TAGGED SIMPLE-REC-IND ANY
         )
)
(constant terms-with-one-binding-id
        '(PRODUCT FUNCTION LAMBDA SET PARFUNCTION SIMPLE-REC)
)
(constant terms-with-a-list-of-binding-ids
        '(BOUND-ID-TERM QUOTIENT BOUND-ID-LIST)
)


(constant canonical-terms
	  '(UNIVERSE VOID ATOM TOKEN INT POS-NUMBER NIL AXIOM FUNCTION LAMBDA
	    OBJECT LIST CONS UNION INL INR PAIR EQUAL LESS FIX RECURSIVE PRODUCT
	    SET PARFUNCTION SIMPLE-REC QUOTIENT))




;-- WARNING:: The following three functions depend explicitly on the
;-- representation of terms.  They could in principle be made independent
;-- of the representation but it would be some work.

;-- Returns a list of the bound ids occuring in the term 
(defun binding-ids-of-term (term)
    (Pif (member (kind-of-term term) terms-with-one-binding-id) -->
        (list (caddr term))
     || (member (kind-of-term term) terms-with-a-list-of-binding-ids) -->
        (caddr term)
     || t -->
        nil
     fi)
)

;-- Returns a list of the subterms of the term.  Any changes to this
;-- function will require changes to the next function, (map-on-subterms),
;-- as well as to ml-list-subterms.
(defun subterms-of-term (term)
    (Pif (member (kind-of-term term) terms-with-no-subterms) -->
        nil
     || (eql (kind-of-term term) 'EQUAL) -->
        (cons (caddr term) (cadddr term))
     || (eql (kind-of-term term) 'BOUND-ID-LIST) -->
        (cadddr term)
     || (or
            (member (kind-of-term term) terms-with-one-binding-id)
            (member (kind-of-term term) terms-with-a-list-of-binding-ids)
        ) -->
        (cdddr term)
     || (eql (kind-of-term term) 'REC-IND) -->
        (list (caddr term) (cadddr term))
     || (eql (kind-of-term term) 'FIX) -->
        (list (caddr term))
     || (eql (kind-of-term term) 'RECURSIVE) -->
        (Pif (fix-term-of-recursive-term term) -->
	    (list (caddr term) (cadddr term) (cadr (cddddr term)))
	 || t -->
	    (list (caddr term) (cadr (cddddr term)))
	 fi)
     || (eql (kind-of-term term) 'TAGGED) --> (cdddr term)
     || (member (kind-of-term term) terms-with-no-binding-ids) -->
        (cddr term)
     fi)
)


;;; WARNING.  Dependent on term representation.
;;; Return the result of replacing each immediate subterm of term by
;;; (f term).
(defun map-on-subterms (f term)
    (let* ((kind (kind-of-term term))
	   (new-term
	     (Pif (member kind terms-with-no-subterms)
		 --> term  ||
		 (eql kind 'EQUAL)
		 --> ;; ensure f evaluated on subterms in left to right order.
		     (let* ((new-equands (mapcar f (fourth term)))
			    (new-type (funcall f (third term))))
		       `(,kind nil ,new-type ,new-equands))  ||
		 (eql kind 'BOUND-ID-LIST)
		 --> `(,kind nil ,(third term) ,(mapcar f (fourth term)))  ||
		 (or
		   (member kind terms-with-one-binding-id)
		   (member kind terms-with-a-list-of-binding-ids))
		 --> `(,kind nil ,(third term) ,@(mapcar f (cdddr term)))  ||
		 (eql kind `REC-IND)
		 --> `(,kind nil ,(funcall f (third term))
		       ,(funcall f (fourth term)) ,(fifth term)) ||
		 (eql kind `FIX)
		 --> `(,kind nil ,(funcall f (third term)) ,(fourth term))  ||
		 (eql kind 'RECURSIVE)
		 --> `(,kind nil ,(funcall f (third term))
		       ,(and (fourth term) (funcall f (fourth term)))
		       ,(fifth term) ,(funcall f (sixth term)))  ||
		 (eql kind 'TAGGED)
		 --> `(,kind nil ,(third term) ,(funcall f (fourth term))) ||
		 (member kind terms-with-no-binding-ids)
		 --> `(,kind nil ,@(mapcar f (cddr term)))  fi)))

      ;; Attempt to preserve Ttrees.
      (labels ((eq-members (l1 l2)
		 (cond ((null l1) t)
		       (t (and (eql (car l1) (car l2))
			       (eq-members (cdr l1) (cdr l2))))))
	       (restore-if-eq-members (l1 l2)
		 (cond ((eq-members l1 l2) term) (t new-term))))
	(cond ((eql kind 'BOUND-ID-LIST)
	       (restore-if-eq-members (fourth term) (fourth new-term)))
	      ((eql kind 'EQUAL)
	       (restore-if-eq-members
		 (cons (third term) (fourth term))
		 (cons (third new-term) (fourth new-term))))
	      (t
	       (restore-if-eq-members (cddr term)
				      (cddr new-term)))))))

;-- Warning:  this doesn't work for everything.
;-- (e.g., tagged terms).
(defun make-term (kind binding-id subterms)
    (Pif (member kind terms-with-no-binding-ids) -->
        `(,kind nil ,@subterms)
     || (member kind terms-with-one-binding-id) -->
        `(,kind nil ,binding-id ,@subterms)
     fi)
)


;;;  This next set of functions are for the equal-terms predicate.
;;;

(defvar id-stack-1 nil
  "The bound identifier stack for the first term")
(defvar id-stack-2 nil
  "The bound identifier stack for the second term")

(defvar top-of-id-stack)

;(declare
;  (localf push-ids pop-ids a-equal-terms a-equal-term-list check-vars)
;)

(defun init-equal-terms ()
    (<- id-stack-1 (new-evec 50))
    (<- id-stack-2 (new-evec 50))
)

;--
;-- equal-terms (x:term, y:term)
;--
;--     Return t if x and y are equivalent terms
;--     (have the same structure though perhaps different
;--     print forms), and return nil otherwise.
;--                              

(defun equal-terms (x y)
    (<- top-of-id-stack -1)
    (a-equal-terms x y)
)

(defun push-ids (v1 v2)
    (<- top-of-id-stack (1+ *-*))
    (evec-set id-stack-1 top-of-id-stack v1)
    (evec-set id-stack-2 top-of-id-stack v2)
)

(defun pop-ids ()
    (<- top-of-id-stack (1- *-*))
)

(defun check-vars (v1 v2)
    (do ((index top-of-id-stack (1- index)))
	((< index 0) (eql v1 v2))
      (Pif (eql v1 (evec-ref id-stack-1 index)) -->
	  (return (eql v2 (evec-ref id-stack-2 index)))
       || (eql v2 (evec-ref id-stack-2 index)) -->
          (return nil)
       fi)
    )
)


    
;-- 
;-- a-equal-terms (x:term, y:term)
;--
;-- a-equal-terms returns t if x and y are alpha-convertible, nil
;-- otherwise.  x and y are equivalent in their environments
;-- if for all i, 1 <= i <= length(stacks), the ith elements of each stack
;-- appear in their respective terms in exactly corresponding positions.
;--                                                            

(defun a-equal-terms (x y)

    (Plet (kind (kind-of-term x))

        (and (eql kind (kind-of-term y))
	     (Pif (member kind terms-with-a-constant-field) -->
		 (equal (caddr x) (caddr y))
	      || (eql kind 'VAR) -->
		 (check-vars (id-of-var-term x) (id-of-var-term y))
	      || (member kind '(PRODUCT FUNCTION SET PARFUNCTION)) -->
		 (and
		     (a-equal-terms (cadddr x) (cadddr y))
		     (prog2
		       (push-ids (caddr x) (caddr y))
		       (a-equal-terms (car (cddddr x)) (car (cddddr y)))
		       (pop-ids)
		     )
		 )
	      || (or (eql kind 'LAMBDA) (eql kind 'SIMPLE-REC)) -->
		 (prog2
		      (push-ids (caddr x) (caddr y))
		      (a-equal-terms (cadddr x) (cadddr y))
		      (pop-ids)
		 )
	      || (eql kind 'QUOTIENT) -->
		 (and
		     (a-equal-terms (cadddr x) (cadddr y))
		     (prog2
			 (mapc #'push-ids (caddr x) (caddr y))
			 (a-equal-terms (car (cddddr x)) (car (cddddr y)))
			 (mapc #'(lambda (x) (pop-ids)) (caddr x))
		     )
		 )
	      || (eql kind 'BOUND-ID-TERM) -->
		 (and
		      (= (length (caddr x)) (length (caddr y)))
		      (prog2
			  (mapc #'push-ids (caddr x) (caddr y))
			  (a-equal-terms (cadddr x) (cadddr y))
			  (mapc #'(lambda (x) (pop-ids)) (caddr x))
		      )
		  )

	      || (eql kind 'BOUND-ID-LIST) -->
	         (and
		      (= (length (caddr x)) (length (caddr y)))
		      (prog2
			  (mapc #'push-ids (caddr x) (caddr y))
			  (a-equal-term-lists (cadddr x) (cadddr y))
			  (mapc #'(lambda (x) (pop-ids)) (caddr x))
		      )
		  )

	      || (member kind  '(REC-IND FIX)) -->
	         (and
		      (= (length (caddr x)) (length (caddr y)))
		      (eql (selected-position x)
			  (selected-position y)
		      )
		      (a-equal-terms (caddr x) (caddr y))
		  )

	      || (eql kind 'RECURSIVE) -->
	         (and
		      (= (length (term-list-of-bound-id-list-term
				   (bound-id-list-term-of-recursive-term x))
			 )
			 (length (term-list-of-bound-id-list-term
				   (bound-id-list-term-of-recursive-term y))
			 )
		      )
		      (eql (selected-position x)
			  (selected-position y)
		      )
		      (a-equal-terms (term-of-recursive-term x) (term-of-recursive-term y))
		      (a-equal-terms
			(fix-term-of-recursive-term x) (fix-term-of-recursive-term y)
		      )
		      (a-equal-terms (bound-id-list-term-of-recursive-term x)
			       (bound-id-list-term-of-recursive-term y)
		      )
		  )
	      
	      || (eql kind 'EQUAL) -->
		 (and
		     (= (length (cadddr x)) (length (cadddr y)))
		     (a-equal-terms (caddr x) (caddr y))
		     (a-equal-term-lists (cadddr x) (cadddr y))
		 )

	      || (eql kind 'TAGGED) -->
	         (and (= (tag-of-tagged-term x) (tag-of-tagged-term y))
		      (a-equal-terms (cadddr x) (cadddr y))
		 )

	      || t -->
		 (a-equal-term-lists (cddr x) (cddr y))
	      fi)
	 )
    )
)

(defun a-equal-term-lists (l1 l2)
    (do ((list1 l1 (cdr list1))
	 (list2 l2 (cdr list2))
	)
	((null list1) t)
      (Pif (not (a-equal-terms (car list1) (car list2))) -->
	  (return nil)
       fi)
    )
)

;;; This set of functions defines a hashing function for equal terms.
;;;

(defvar id-stack nil
  "Stack of bound variables")

(defvar id-stack-top -1
  "Index of top of id-stack")

(defun init-equal-term-hash ()
    (<- id-stack (new-evec 50))
)

;(declare (localf push-id pop-id lookup-var eqt-hash eqt-hash-list))

(defun equal-term-hash (term)
    (<- id-stack-top -1)
    (abs (eqt-hash term))
)


(defun push-id (id)
    (<- id-stack-top (1+ id-stack-top))
    (evec-set id-stack id-stack-top id)
)

(defun pop-id ()
    (<- id-stack-top (1- id-stack-top))
)

(defun lookup-var (var)
    (do ((index id-stack-top (1- index))
	 (val 0 (1+ val))
	)
	((< index 0) (sxhash var))
      (and (eql var (evec-ref id-stack index)) (return val))
    )
)

(defun eqt-hash (term)
    (Plet (kind (kind-of-term term))
      (Pif (member kind terms-with-a-constant-field) -->
	  (logxor (sxhash kind) (rot (sxhash (caddr term)) 1))
       || (eql kind 'VAR) -->
          (logxor (sxhash kind) (rot (lookup-var (caddr term)) 1))
       || (member kind '(PRODUCT FUNCTION SET PARFUNCTION)) -->
          (logxor
	    (sxhash kind)
	    (rot (eqt-hash (cadddr term)) 1)
	    (rot
	      (prog2
		(push-id (caddr term))
		(eqt-hash (car (cddddr term)))
		(pop-id)
	      )
	      5
	    )
	  )
       || (or (eql kind 'LAMBDA) (eql kind 'SIMPLE-REC)) -->
          (logxor
	    (sxhash kind)
	    (rot
	      (prog2
		(push-id (caddr term))
		(eqt-hash (cadddr term))
		(pop-id)
	      )
	      1
	    )
	  )
       || (eql kind 'QUOTIENT) -->
          (logxor
	    (sxhash kind)
	    (rot (eqt-hash (cadddr term)) 1)
	    (rot
	      (prog2
		(mapc #'push-id (caddr term))
		(eqt-hash (car (cddddr term)))
		(mapc #'(lambda (x) (pop-id)) (caddr term))
	      )
	      5
	    )
	  )
       || (eql kind 'BOUND-ID-TERM) -->
          (logxor
	    (sxhash kind)
	    (rot
	      (prog2
		(mapc #'push-id (caddr term))
		(eqt-hash (cadddr term))
		(mapc #'(lambda (x) (pop-id)) (caddr term))
	      )
	      1
	    )
	  )
       || (eql kind 'BOUND-ID-LIST) -->
          (logxor
	    (sxhash kind)
	    (rot
	      (prog2
		(mapc #'push-id (bound-ids-of-bound-id-list-term term))
		(eqt-hash-list (term-list-of-bound-id-list-term term))
		(mapc #'(lambda (x) (pop-id)) (bound-ids-of-bound-id-list-term term))
	      )
	      1
	    )
	  )
       || (eql kind 'EQUAL) -->
          (logxor
	    (sxhash kind)
	    (rot (eqt-hash (caddr term)) 1)
	    (rot (eqt-hash-list (cadddr term)) 5)
	  )
       || (member kind '(floor REC-IND)) -->          ;;;- should selecting id in recursive,
          (logxor                                  ;;;- rec_ind or fix terms be used?
	    (sxhash kind)
	    (rot (eqt-hash (caddr term)) 1)
	  )
       || (eql kind 'RECURSIVE) -->
          (logxor
	    (sxhash kind)
	    (rot (eqt-hash (bound-id-list-term-of-recursive-term term)) 1)
	    (rot (eqt-hash (fix-term-of-recursive-term term)) 1)
	    (rot (eqt-hash (term-of-recursive-term term)) 1)
	  )
       || (eql kind 'TAGGED) -->
          (throw 'process-err
		 `(ERR |eqt-hash: unexpected tagged term|)
	  )
       || t -->
          (logxor
	    (sxhash kind)
	    (rot (eqt-hash-list (cddr term)) 5)
	  )
       fi)
    )
)

(defun eqt-hash-list (term-list)
    (cond ((null term-list) 0)
	  (t (do ((term-list (cdr term-list) (cdr term-list))
		  (rotation 1 (cond ((> rotation 13) 1) (t (+ rotation 3))))
		  (hashval (eqt-hash (car term-list))
			   (logxor
			     hashval
			     (rot (eqt-hash (car term-list)) rotation)
			   )
		  )
		 )
		 ((null term-list) hashval)
	      )
	  )
     )
)

;--
;-- free-vars (x:formula-or-term)
;--
;--     Return a set of the free variables of x.
;--

(defun free-vars (x)

     (Pif (eql (kind-of-term x) 'BOUND-ID-TERM) -->
         (prl-set-difference (free-vars (term-of-bound-id-term x))
                         (list-to-set (bound-ids-of-bound-id-term x))
         )

      || (eql (kind-of-term x) 'PRODUCT) -->
         (Plet (bound-id-list nil
              )
             (Pif (bound-id-of-product-term x) -->
                 (<- bound-id-list (list (bound-id-of-product-term x)))
              fi)
             (set-union2 (free-vars (lefttype-of-product-term x))
                         (prl-set-difference 
                              (free-vars (righttype-of-product-term x))
                              (list-to-set bound-id-list)     
                         )
             )
         )             
                                      
      || (eql (kind-of-term x) 'FUNCTION) -->
         (Plet (bound-id-list nil)
             (Pif (bound-id-of-function-term x) -->
                 (<- bound-id-list (list (bound-id-of-function-term x)))
              fi)                                
             (set-union2 (free-vars (lefttype-of-function-term x))
                         (prl-set-difference 
                              (free-vars (righttype-of-function-term x))
                              (list-to-set bound-id-list)
                         )
             )
         )             

      || (eql (kind-of-term x) 'PARFUNCTION) -->
         (Plet (bound-id-list nil)
             (Pif (bound-id-of-parfunction-term x) -->
                 (<- bound-id-list (list (bound-id-of-parfunction-term x)))
              fi)                                
             (set-union2 (free-vars (lefttype-of-parfunction-term x))
                         (prl-set-difference 
                              (free-vars (righttype-of-parfunction-term x))
                              (list-to-set bound-id-list)
                         )
             )
         )             

      || (eql (kind-of-term x) 'SET) -->
         (Plet (bound-id-list (list (bound-id-of-set-term x))
              )
             (set-union2 (free-vars (lefttype-of-set-term x))
                         (prl-set-difference 
                                     (free-vars (righttype-of-set-term x))
                                     (list-to-set bound-id-list)
                         )
             )
         )
	 
      || (eql (kind-of-term x) 'RECURSIVE) -->
         (Pif (fix-term-of-recursive-term x) -->
             (set-union (list 
	                  (free-vars (term-of-recursive-term x))
	                  (free-vars (fix-term-of-recursive-term x))
		          (free-vars (bound-id-list-term-of-recursive-term x))
		        )
	     )
	  || t -->
	     (set-union (list 
	                  (free-vars (term-of-recursive-term x))
		          (free-vars (bound-id-list-term-of-recursive-term x))
		        )
	     )
	  fi)

      || (eql (kind-of-term x) 'FIX) -->
         (free-vars (bound-id-list-term-of-fix-term x))

      || (eql (kind-of-term x) 'REC-IND) -->
         (set-union2
	   (free-vars (term-of-rec-ind-term x))
	   (free-vars (bound-id-list-term-of-rec-ind-term x))
	 )

      || (eql (kind-of-term x) 'LAMBDA) -->
         (prl-set-difference (free-vars (term-of-lambda-term x))
                         (list-to-set (list (bound-id-of-lambda-term x)))
         )
	 
      || (eql (kind-of-term x) 'SIMPLE-REC) -->
         (prl-set-difference (free-vars (term-of-simple-rec-term x))
                         (list-to-set (list (bound-id-of-simple-rec-term x)))
         )

      || (member (kind-of-term x) '(ADD SUB MUL DIV MOD)) -->
         (set-union2 (free-vars (leftterm-of-binary-term x))
                     (free-vars (rightterm-of-binary-term x))
         )

      || (eql (kind-of-term x) 'MINUS) -->
         (free-vars (term-of-minus-term x))
                                    
      || (member (kind-of-term x) '(INL INR)) -->
         (free-vars (term-of-injection-term x))

      || (eql (kind-of-term x) 'DOM) -->
         (free-vars (term-of-dom-term x))

      || (eql (kind-of-term x) 'ANY) -->
         (free-vars (term-of-any-term x))

      || (eql (kind-of-term x) 'EQUAL) -->
         (set-union  (append
                          (mapcar #'free-vars
                                  (terms-of-equal-term x)  
                          )
                          (list (free-vars (type-of-equal-term x)))
                     )
         )

      || (eql (kind-of-term x) 'BOUND-ID-LIST) -->
         (prl-set-difference (set-union (mapcar #'free-vars
					    (term-list-of-bound-id-list-term x)
				    )
			 )
                         (list-to-set (bound-ids-of-bound-id-list-term x))
         )

      || (member (kind-of-term x) 
                 '(POS-NUMBER TOKEN ATOM INT AXIOM OBJECT
                   NIL UNIVERSE VOID TERM-OF-THEOREM)
         ) -->
         (list-to-set nil)

      || (eql (kind-of-term x) 'VAR) -->
         (list-to-set (list (id-of-var-term x)))

      || (eql (kind-of-term x) 'APPLY) -->
         (set-union2 (free-vars (function-of-apply-term x))
                     (free-vars (arg-of-apply-term x))
         )

      || (eql (kind-of-term x) 'APPLY-PARTIAL) -->
         (set-union2 (free-vars (function-of-apply-partial-term x))
                     (free-vars (arg-of-apply-partial-term x))
         )

      || (eql (kind-of-term x) 'LIST) -->
         (free-vars (type-of-list-term x))

      || (eql (kind-of-term x) 'IND) -->
         (set-union (list (free-vars (value-of-ind-term x))
                          (free-vars (downterm-of-ind-term x))
                          (free-vars (baseterm-of-ind-term x))
                          (free-vars (upterm-of-ind-term x))
                    )
         )                                     

      || (eql (kind-of-term x) 'LIST-IND) -->
         (set-union (list (free-vars (value-of-list-ind-term x))
                          (free-vars (baseterm-of-list-ind-term x))
                          (free-vars (upterm-of-list-ind-term x))
                    )
         )
                          
      || (eql (kind-of-term x) 'SPREAD) -->
         (set-union2 (free-vars (value-of-spread-term x))
                     (free-vars (term-of-spread-term x))
         )

      || (eql (kind-of-term x) 'SIMPLE-REC-IND) -->
         (set-union2 (free-vars (value-of-simple-rec-ind-term x))
                     (free-vars (term-of-simple-rec-ind-term x))
         )

      || (eql (kind-of-term x) 'DECIDE) -->
         (set-union (list (free-vars (value-of-decide-term x))
                          (free-vars (leftterm-of-decide-term x))
                          (free-vars (rightterm-of-decide-term x))
                    )
         )                                 

      || (eql (kind-of-term x) 'CONS) -->
         (set-union2 (free-vars (head-of-cons-term x))
                     (free-vars (tail-of-cons-term x))
         )

      || (eql (kind-of-term x) 'UNION) -->
         (set-union2 (free-vars (lefttype-of-union-term x))
                     (free-vars (righttype-of-union-term x))          
         )                                                  

      || (eql (kind-of-term x) 'QUOTIENT) -->
         (set-union2 (free-vars (lefttype-of-quotient-term x))
                     (prl-set-difference
                                (free-vars (righttype-of-quotient-term x))
                                (list-to-set (bound-ids-of-quotient-term x))
                     )
         )            

      || (eql (kind-of-term x) 'PAIR) -->
         (set-union2 (free-vars (leftterm-of-pair-term x))
                     (free-vars (rightterm-of-pair-term x))
         )                         

      || (eql (kind-of-term x) 'LESS) -->
         (set-union2 (free-vars (leftterm-of-less-term x))
                     (free-vars (rightterm-of-less-term x))
         )
      || (eql (kind-of-term x) 'TAGGED) -->
         (free-vars (term-of-tagged-term x)
	 )
      || (member (kind-of-term x) '(ATOMEQ INTEQ INTLESS)) -->
         (set-union
               (list (free-vars (leftterm-of-decision-term x))
                     (free-vars (rightterm-of-decision-term x))
                     (free-vars (if-term-of-decision-term x))
                     (free-vars (else-term-of-decision-term x))
               )
         )

      fi)
)



;-- An fv-node is defined wrt a term.  The free-vars of the node are
;-- the free vars of the term, and the children of the node are the fv-nodes
;-- of the subterms of the term.
(deftuple fv-node
    free-vars
    children
)

;-- get-free-var-tree (term): fv-node
;-- 
;-- Returns the free variable tree for a term
;-- 
(defun get-free-var-tree (term)
  (cond
    ((null term) '(nil nil))
    ((eq (kind-of-term term) 'VAR) 		; must be before next condition
     (list (list (id-of-var-term term)) nil))
    ((member (kind-of-term term) terms-with-no-subterms) '(nil nil))
    ((member (kind-of-term term) terms-with-no-binding-ids) 
     (let ((children (mapcar #'get-free-var-tree (subterms-of-term term))))
       (list (set-union (mapcar #'free-vars-of-fv-node children)) children)))
    ((eq (kind-of-term term) 'LAMBDA) 
     (let ((child (get-free-var-tree (term-of-lambda-term term))))
       (list (set-difference (free-vars-of-fv-node child) 
			     (list (bound-id-of-lambda-term term)))
	     (list child))))
    ((eq (kind-of-term term) 'SIMPLE-REC)
     (let ((child (get-free-var-tree (term-of-simple-rec-term term))))
       (list (set-difference (free-vars-of-fv-node child) 
			     (list (bound-id-of-simple-rec-term term)))
	     (list child))))
    ((member (kind-of-term term) '(PRODUCT FUNCTION SET))
     (let ((child1 (get-free-var-tree (fourth term)))
	   (child2 (get-free-var-tree (fifth term))))
       (list (set-union2 (free-vars-of-fv-node child1)
			 (set-difference (free-vars-of-fv-node child2) (list (third term))))
	     (list child1 child2))))
    ((eq (kind-of-term term) 'QUOTIENT)
     (let ((child1 (get-free-var-tree (lefttype-of-quotient-term term)))
	   (child2 (get-free-var-tree (righttype-of-quotient-term term))))
       (list (set-union2 (free-vars-of-fv-node child1)
			 (set-difference (free-vars-of-fv-node child2) 
					 (bound-ids-of-quotient-term term)))
	     (list child1 child2))))
    ((member (kind-of-term term) '(BOUND-ID-TERM BOUND-ID-LIST))
     (let ((children (mapcar #'get-free-var-tree (subterms-of-term term))))
       (list (set-difference 
	       (set-union (mapcar #'free-vars-of-fv-node children))
	       (binding-ids-of-term term))
	     children)))
    (t (error "get-free-var-tree does not recognize term kind : ~a." (kind-of-term term))) ))


;-- free-vars-of-children (children: list of fv-node): list of id
;-- 
;-- Returns the union of the free vars of each node in children
;--  
(defun free-vars-of-children (children)
    (set-union
        (mapcar #'free-vars-of-fv-node children)))


(deftuple sub
    id                      ;-- The identifier to substitute for
    term                    ;-- The term to be substituted
    free-vars               ;-- The free vars of term
)

;-- 
;-- make-sub-list (id-term-pairs: list): list of sub
;-- 
;-- Returns a list of sub's corresponding to the id term pairs.  Null 
;-- substitutions are optimized out.
;-- 
   
(defun make-sub-list (id-term-pairs)
    (for (pair in id-term-pairs)
        (when
            (not
                (and
                    (eql (kind-of-term (cadr pair)) 'VAR)
                    (eql (car pair) (id-of-var-term (cadr pair)))
                )
            )
        )
        (save
            (list
                (car pair)
                (cadr pair)
                (free-vars (cadr pair))
            )
        )
    )
)

;-- ids-from-sub-list (sub-list: list of subs): list of id
;-- 
;-- Returns a list of the id's in the id fields of the sub's in sub-list
;-- 
(defun ids-from-sub-list (sub-list)
    (mapcar #'id-of-sub sub-list))


;-- free-vars-of-sub-terms (sub-list: list of sub): list of id
;-- 
;-- Returns a list of the ids which occur free in any of the terms in
;-- sub-list.
;-- 
(defun free-vars-of-sub-terms (sub-list)
    (set-union (mapcar #'free-vars-of-sub sub-list)))

(defun subst-init ()
    (for (term-type in '(MINUS ADD SUB MUL DIV MOD IND LIST CONS LIST-IND UNION INL INR
                         DECIDE PAIR SPREAD APPLY EQUAL LESS  ATOMEQ INTLESS INTEQ
			 DOM APPLY-PARTIAL TAGGED SIMPLE-REC-IND ANY
			)
	 )
	 (do
	     (setf (get term-type 'substitution-fcn) 'no-binding-id-sub)
	 )
    )
    (for (term-type in '(FUNCTION PRODUCT SET PARFUNCTION))
	 (do
	     (setf (get term-type 'substitution-fcn) 'possible-binding-id-sub)
	 )
    )
    (setf (get 'LAMBDA 'substitution-fcn) 'lambda-sub)
    (setf (get 'SIMPLE-REC 'substitution-fcn) 'simple-rec-sub)
    (setf (get 'QUOTIENT 'substitution-fcn) 'quotient-sub)
    (setf (get 'BOUND-ID-TERM 'substitution-fcn) 'bound-id-sub)
    (setf (get 'BOUND-ID-LIST 'substitution-fcn) 'bound-id-list-sub)
    (setf (get 'RECURSIVE 'substitution-fcn) 'recursive-sub)
    (setf (get 'REC-IND 'substitution-fcn) 'rec-ind-sub)
    (setf (get 'FIX 'substitution-fcn) 'fix-sub)
    t
)


;--
;-- substitute (target: term, id-term-pairs :list)
;--
;--     id-term-pairs is a list of pairs, each of the form (id term)
;--     Return a term which is the same as target except
;--     that all free occurrences of those variables in the id fields
;--     of id-term-pairs have been replaced by their corresponding terms.
;--
;--     Best Ttrees are maintained as much as possible.  
;--     

(defvar worry-about-capture)

(defun substitute (target id-term-pairs)
    (internal-substitute target id-term-pairs t)
)

(defun substitute-with-capture (target id-term-pairs)
    (internal-substitute target id-term-pairs nil)
)



;;; Uses respect the invariant { hack-ttree? = t }.
(defvar *hack-Ttree?* t "Should ttree maintenance be done during substitution?")


(defun internal-substitute (target id-term-pairs worry-about-capture)
    (Plet (sub-list (make-sub-list id-term-pairs))
        (Pif (not (null sub-list)) -->
            (Plet (fv-tree (get-free-var-tree target))
                (Pif (set-intersection
                        (free-vars-of-fv-node fv-tree)
                        (ids-from-sub-list sub-list)
                    ) -->
                    (Plet (subst-result (subst-term target fv-tree sub-list)
                          good-Ttree-result (and *hack-ttree?*
						 (hack-Ttree-and-parse target sub-list))
                         )
                        (Pif (and
                                (not (null good-Ttree-result))
                                (equal-terms subst-result good-Ttree-result)
                            ) -->
                            good-Ttree-result
                         || t -->
                            subst-result
                         fi)
                    )
                 || t --> target
                 fi)
            )
         || t -->
            target
         fi)
    )
)


;-- subst-term (term: term, fv-tree: fv-node, sub-list: list of sub): term
;-- 
;-- Returns a term the same as target except that all free occurences of
;-- those variables in the id fields of the sub's in sub-list have been
;-- replaced with their corresponding terms.  fv-tree should be the free var
;-- tree for term.  Some Ttree structure is maintained; the Ttree of a term
;-- is made nil only if a substitution actually occurs in it.
;--

(defun subst-term (term fv-tree sub-list)
    (Pif (eql (kind-of-term term) 'VAR) -->
        (Plet (sub (assoc (id-of-var-term term) sub-list))
            (Pif (not (null sub)) -->
                (term-of-sub sub)
             || t -->
                term
             fi)
        )
     || (not
            (set-intersection
                (free-vars-of-fv-node fv-tree)
                (ids-from-sub-list sub-list)
            )
        ) -->
        term
     || t -->
        (funcall
	    (get (kind-of-term term) 'substitution-fcn)
	    term fv-tree sub-list
	)
     fi)
)

(defun no-binding-id-sub (term fv-tree sub-list)
    (Pif (eql (kind-of-term term) 'EQUAL) -->
	(equal-term
	    'EQUAL nil
	    (subst-term
	        (type-of-equal-term term)
	       	(car (children-of-fv-node fv-tree)) sub-list
	    )
	    (for
	        (subterm in (terms-of-equal-term term))
		(node in (cdr (children-of-fv-node fv-tree)))
		(save (subst-term subterm node sub-list))
	    )
	)
     || (eql (kind-of-term term) 'TAGGED) -->
        (tagged-term
	    'TAGGED
	    nil
	    (tag-of-tagged-term term)
	    (subst-term
	        (term-of-tagged-term term)
		(car (children-of-fv-node fv-tree)) sub-list
	    )
	)
     || t -->
        (make-term
            (kind-of-term term)
	    nil
	    (for
	        (subterm in (cddr term))
		(node in (children-of-fv-node fv-tree))
		(save (subst-term subterm node sub-list))
	    )
	 )
     fi)
)

(defun lambda-sub (term fv-tree sub-list)
    (multiple-value-bind
        (new-ids new-term)
	(deal-with-capture
	    (list (bound-id-of-lambda-term term))
	    (list (term-of-lambda-term term))
	    (children-of-fv-node fv-tree)
	    sub-list
	)
        (lambda-term 'LAMBDA nil
	    (car new-ids)
	    (car new-term)
	)
    )
)

(defun simple-rec-sub (term fv-tree sub-list)
    (multiple-value-bind
        (new-ids new-term)
	(deal-with-capture
	    (list (bound-id-of-simple-rec-term term))
	    (list (term-of-simple-rec-term term))
	    (children-of-fv-node fv-tree)
	    sub-list
	)
        (simple-rec-term 'SIMPLE-REC nil
	    (car new-ids)
	    (car new-term)
	)
    )
)

(defun possible-binding-id-sub (term fv-tree sub-list)
    (Plet (id       (caddr term)
	  subterms (cdddr term)
	  fv-list  (children-of-fv-node fv-tree)
	 )
	(Pif id -->
	    (multiple-value-bind
	        (new-ids new-bound-term)
		(deal-with-capture
		    (list id)
		    (list (cadr subterms))
		    (cdr fv-list)
		    sub-list
	        )
	        (make-term
		    (kind-of-term term)
		    (car new-ids)
		    (list
		        (subst-term (car subterms) (car fv-list) sub-list)
			(car new-bound-term)
		    )
		)
	    )
	 || t -->
	    (make-term
	        (kind-of-term term)
		nil
		(for (subterm in subterms)
		     (fv-node in fv-list)
		     (save (subst-term subterm fv-node sub-list))
		)
	    )
	 fi)
     )
)

(defun quotient-sub (term fv-tree sub-list)
    (multiple-value-bind
       (new-ids new-righttype)
	(deal-with-capture
	    (bound-ids-of-quotient-term term)
	    (list (righttype-of-quotient-term term))
	    (cdr (children-of-fv-node fv-tree))
 	    sub-list
	)
        (quotient-term
	    'QUOTIENT nil
	    new-ids
	    (subst-term
	        (lefttype-of-quotient-term term)
		(car (children-of-fv-node fv-tree))
		sub-list
	    )
	    (car new-righttype)
	)
    )
)

(defun bound-id-sub (term fv-tree sub-list)
    (multiple-value-bind
        (new-ids new-term)
	(deal-with-capture
	    (bound-ids-of-bound-id-term term)
	    (list (term-of-bound-id-term term))
	    (children-of-fv-node fv-tree)
	    sub-list
	)
        (bound-id-term
	    'BOUND-ID-TERM nil
	    new-ids
	    (car new-term)
	)
    )
)

(defun bound-id-list-sub (term fv-tree sub-list)
    (multiple-value-bind
        (new-ids new-terms)
	(deal-with-capture
	    (bound-ids-of-bound-id-list-term term)
	    (term-list-of-bound-id-list-term term)
	    (children-of-fv-node fv-tree)
	    sub-list
	)
        (bound-id-list-term
	    'BOUND-ID-LIST nil
	    new-ids
	    new-terms
	)
    )
)


(defun recursive-sub (term fv-tree sub-list)
    (Plet (new-term1 (subst-term
		      (bound-id-list-term-of-recursive-term term)
		      (car (children-of-fv-node fv-tree))
		      sub-list
		    )
	  new-term2 nil
	  new-term3 nil
	  n         (selected-position term)
	 )
	 (Pif (fix-term-of-recursive-term term) -->
	     (<- new-term2 (subst-term
			     (fix-term-of-recursive-term term)
			     (cadr (children-of-fv-node fv-tree))
			     sub-list
			    )
	     )
	     (<- new-term3 (subst-term
			     (term-of-recursive-term term)
			     (caddr (children-of-fv-node fv-tree))
			     sub-list
			   )
	     )
	  || t -->
	     (<- new-term2 nil)
	     (<- new-term3 (subst-term
			     (term-of-recursive-term term)
			     (cadr (children-of-fv-node fv-tree))
			     sub-list
			   )
	     )
	  fi)
	 (recursive-term
	   'RECURSIVE
	   nil
	   new-term1
	   new-term2
	   (nth n (bound-ids-of-bound-id-list-term new-term1))
	   new-term3
	 )
    )
)
 
(defun fix-sub (term fv-tree sub-list)
    (Plet (n        (selected-position term)
	  new-term (subst-term
		     (bound-id-list-term-of-fix-term term)
		     (car (children-of-fv-node fv-tree))
		     sub-list
		   )
	 )
	 (fix-term
	   'FIX
	   nil
	   new-term
	   (nth n (bound-ids-of-bound-id-list-term new-term))
	 )
    )
)

(defun rec-ind-sub (term fv-tree sub-list)
    (Plet (n         (selected-position term)
	  new-term2 (subst-term
		      (bound-id-list-term-of-rec-ind-term term)
		      (cadr (children-of-fv-node fv-tree))
		      sub-list
		    )
	  new-term1 (subst-term
		      (term-of-rec-ind-term term)
		      (car (children-of-fv-node fv-tree))
		      sub-list
		    )
	 )
	 (rec-ind-term
	   'REC-IND
	   nil
	   new-term1
	   new-term2
	   (nth n (bound-ids-of-bound-id-list-term new-term2))
	 )
    )
)




;-- deal-with-capture (binding-ids: list of id
;--                    bound-terms: list of term
;--                    fv-nodes: list of fv-node
;--                    sub-list: list of sub
;--                   ): (list of id, list of term)
;-- 
;-- This function deals with the problem of capture that can arise when
;-- substituting terms for variables in terms which contain binding
;-- operators.  An identifier, x, is said to be captured by the substitution
;-- of the term t for the identifier y in term t' if x occurs free in t and
;-- y occurs free in t'.  We deal with this by renaming the binding
;-- identifier x to x', and substituting x' for x in t', where x' is some
;-- identifier which does not occur free in t'.  Let the result of this be
;-- t''.  We can then replace free occurences of y in t'' with t with no
;-- capture and return that as the result.
;-- In the general case we have a list of binding ids x1, ..., xm, a list of
;-- bound terms s1,...,sn and a list of substitutions, (y1,t1), ...,(yk,tk).
;-- A binding id is now said to be captured if it is captured for any of the
;-- substitutions in any of the bound terms.
;-- The meaning of the parameters is:
;--   binding-ids is a list of the binding ids of a term
;--   bound-terms is a list of the bound subterms of a term
;--   fv-list is a list of fv-nodes corresponding to bound-terms
;--   sub-list is a list of sub's to be made
;-- 
;-- After handling the problem of capture, this function returns the new
;-- list of binding ids and the term resulting from the substitutions.
;-- 

(defun deal-with-capture (binding-ids bound-terms fv-nodes sub-list)
    (Pif worry-about-capture -->
        (Plet (;--  We compute a vector, x, such that the ith component of x is
	      ;-- the set of binding id's occuring free in ti.
		 x (for (sub in sub-list)
		    (save (set-intersection
			      binding-ids
			      (free-vars-of-sub sub)
			  )
		    )
		)
	      sub-ids (ids-from-sub-list sub-list)
	     )
	    (Plet (y (set-intersection
			sub-ids
			(set-union
			  (mapcar #'free-vars-of-fv-node fv-nodes)
			)
		    )
		 )
		(Plet (;-- An id is captured if it is both free in a substituting
		      ;-- term and the corresponding id to be substituted for is
		      ;-- free in bound-term.
			 capturing-ids
			 (set-union
			     (for (ids in x)
				 (sub in sub-list)
				 (when (member (id-of-sub sub) y))
				 (save ids)
			     )
			 )
		     )
		    (Plet (new-names
			     (get-new-names
				 capturing-ids
				 (set-union
				   (list
				     binding-ids
				     (set-difference
				       (set-union (mapcar 'free-vars-of-fv-node fv-nodes))
				       y)
				     (free-vars-of-sub-terms sub-list))
				 )
			     )
			 )
			(Plet (new-sub-list
				 (adjust-sub-list
				     sub-list capturing-ids new-names binding-ids
				 )
			      new-binding-ids
				 (update-binding-ids
				     binding-ids capturing-ids new-names
				 )
			     )
			    (values
				new-binding-ids
				(mapcar #'(lambda (x y) (subst-term x y new-sub-list))
					bound-terms fv-nodes
				)
			    )
			)
		    )
		)
	    )
	)
     || t -->
        ;-- don't worry about capture, just do the substitution.
        (values
	    binding-ids
	    (mapcar #'(lambda (x y) (subst-term x y sub-list)) bound-terms fv-nodes)
	)
     fi)
)


(global new-id-suffix)

;-- get-new-names (ids, others: list of id): list of id
;-- 
;-- For each id in ids, returns an new id which doesn't occur in others
;-- 
(defun get-new-names (ids others)
    (<- new-id-suffix 0)
    (for (id in ids) (save (get-new-name id others)))
)

;-- get-new-name (id:id, others: list of id)
;-- 
;-- Given an id, return an id which does not occur in others
;-- 
(defun get-new-name (id others)
    (Ploop
        (local test (concat id '|@| new-id-suffix))
        (while (member test others))
        (do
            (<- new-id-suffix (1+ new-id-suffix))
            (<- test (concat id '|@| new-id-suffix))
        )
        (result test)
    )
)       

;-- adjust-sub-list (old-list: list of sub
;--                  capturing-ids, new-ids, binding-ids: list of id
;--
;--                 ): list of sub
;-- 
;-- Returns a new sub list which specifies that each of the capturing ids
;-- should be replaced with the corresonding new id, and that contains no
;-- other substitution for the binding-ids or the new-ids.
;-- 
(defun adjust-sub-list (old-list capturing-ids new-ids binding-ids)
    (append
        (for (old in capturing-ids)
            (new in new-ids)
            (save (list old (var-term 'VAR nil new) (list new)))
        )
        (Plet (binding-names (set-union2 new-ids binding-ids))
            (Ploop
                (local answer nil)
                (while (not (null old-list)))
                (do
                    (Pif (not
                            (member
                                (id-of-sub (car old-list))
                                binding-names
                            )
                        ) -->
                        (<- answer (cons (car old-list) *-*))
                     fi)
                    (<- old-list (cdr old-list))
                )
                (result (nreverse answer))
            )
        )
    )
)

;-- update-binding-ids (old, captured, new: list of id): list of id
;-- 
;-- Returns a list of ids the same length as old, but with each occurence of
;-- an id in captured replaced with the corresponding id in new.
;--
(defun update-binding-ids (old captured new)
    (for (id in old)
	 (save (update-id id captured new))
    )
	    
)

(defun update-id (id captured new)
    (Ploop
        (while (and (not (null captured)) (not (eql id (car captured)))))
	(do
	    (<- captured (cdr captured))
	    (<- new (cdr new))
	)
	(result
	    (Pif (not (null captured)) --> (car new)
	     || t                     --> id
	     fi)
	)
    )
)


;-- hack-Ttree-and-parse (target: term, sub-list: list of sub): term
;-- 
;-- Substitute the ttrees for the terms in sub-list into the ttree for
;-- target, returning the result of parsing this, or nil if some error
;-- occurs.
;-- 
(defun hack-Ttree-and-parse (target sub-list)
    (Plet (sub-Ttrees
             (for (sub in sub-list)
                 (save
                     (list
                         (id-of-sub sub)
                         (nreverse (cdr (term-to-Ttree-with-parens (term-of-sub sub))))
                     )
                 )
             )
         )
        (Plet (parse-result
                 (catch
                     'process-err
                     (cons
                         'SUCCESS
                         (parse
                             (subst-Ttree (term-to-Ttree target) sub-Ttrees)
                         )
                     )
                 )
             )
	    (flush-scanner-input)
            (Pif (and (consp parse-result) (eql (car parse-result) 'SUCCESS)) -->
                (cdr parse-result)
             || t -->
                nil
             fi)
        )
    )
)

;--
;-- subst-Ttree (target:Ttree, sub:list of (id Ttree))
;--
;--     Return a Ttree obtained from target by replacing every occurrence
;--     of any id in sub by its corresponding Ttree.  An id occurs in target
;--     if the chars of the id appear contiguously in the top level or if
;--     the id occurs in any actual of any defref in target (and so on down
;--     through defrefs in the actuals).  The chars of the id must not be
;--     preceded or followed by any chars that can appear in an id.  This
;--     heuristic for finding ids fails if an id is spread across levels
;--     of the Ttree.  It also finds binding and bound instances of vars
;--     as well as free ones.  Thus, one should not count on this routine 
;--     replacing precisely the free instances of ids in target.  It just
;--     attempts to do so.
;--

(constant start-idchars$
    '#.(istring "_ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
)
(constant idchars$
    '#.(istring "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_0123456789@")
)

(defun subst-Ttree (target sub)

    (Plet (source (cdr target)   ;-- remainder of target to be examined,
                                ;--   skip leading Ttree atom
          result nil            ;-- reversed result of substituting on the chars
                                ;--   and defrefs already taken from source
         )

        (Ploop
            (while source)
            (do
                (Pif (consp (car source)) -->
                    ;-- a defref heads source -- substitute in its actuals
                        (<- result
                            (cons
                                (cons
                                    (caar source)
                                    (for (actual in (cdar source))
                                        (save (subst-Ttree actual sub))
                                    )
                                )
                                result
                            )
                        )
                        (<- source (cdr source))

                 || (member (car source) start-idchars$) -->
                    ;-- the leading char can start an id, get the id, see if
                    ;-- it is to be substituted for, and do so or don't
                        (Plet (id nil
                             )

                            (Ploop
                                (while (and source
                                            (member (car source) idchars$)
                                       )
                                )
                                (do
                                    (<- id (cons (car source) *-*))
                                    (<- source (cdr *-*))
                                )
                            )

                            (Plet (subpair (assoc (implode (reverse id)) sub))

                                (Pif subpair -->
                                    ;-- place the new Ttree on the front of result
                                        (<- result
                                            (append
					      (cadr subpair)
                                              *-*
                                            )
                                        )


                                  || t -->
                                     ;-- the id isn't to be changed,
                                     ;-- put it onto result
                                         (<- result (append id *-*))
                                 fi)
                            )
                        )

                 || t -->
                    ;-- a non-id char leads source
                        (<- result (cons (car source) *-*))
                        (<- source (cdr *-*))

                 fi)
            )
        )

        ;-- Build a Ttree from result and yield it
            (cons 'Ttree (nreverse result))

    )
)

;-- occurs-positively
;--
;-- used in parsing the rec form.              

(defun occurs-positively (var term)
    (Plet (term-kind (kind-of-term term))
	 (Pif (or (member term-kind terms-with-no-subterms)
		 (member term-kind terms-with-a-constant-field)) --> t

	  || (eql term-kind 'DECIDE) -->
	     (and (not (member var (free-vars (value-of-decide-term term))))
		  (occurs-positively var (leftterm-of-decide-term term))
	          (occurs-positively var (rightterm-of-decide-term term)))

	 || (eql term-kind 'IND) -->
	    (and (not (member var (free-vars (value-of-ind-term term))))
		 (occurs-positively var (downterm-of-ind-term term))
		 (occurs-positively var (baseterm-of-ind-term term))
		 (occurs-positively var (upterm-of-ind-term term)))
		 
		  
	 || (eql term-kind 'LIST-IND) -->
	    (and (not (member var (free-vars (value-of-list-ind-term term))))
		 (occurs-positively var (baseterm-of-list-ind-term term))
		 (occurs-positively var (upterm-of-list-ind-term term)))
		  
	 || (eql term-kind 'SPREAD) -->
	     (and (not (member var (free-vars (value-of-spread-term term))))
		  (occurs-positively var (term-of-spread-term term)))

	  || (eql term-kind 'PRODUCT) -->
	     (and (or (eql var (bound-id-of-product-term term))
		      (occurs-positively var (righttype-of-product-term term)))
		  (occurs-positively var (lefttype-of-product-term term)))

	  || (eql term-kind 'LIST) -->
	     (occurs-positively var (type-of-list-term term))

	  || (eql term-kind 'CONS) -->
	     (and (occurs-positively var (head-of-cons-term term))
		  (occurs-positively var (tail-of-cons-term term)))

	  || (eql term-kind 'SET) -->
	     (and (or (eql var (bound-id-of-set-term term))
		      (occurs-positively var (righttype-of-set-term term)))
		  (occurs-positively var (lefttype-of-set-term term)))
	  
	  || (eql term-kind 'QUOTIENT) -->
	     (and (or (member var (bound-ids-of-quotient-term term))
		      (occurs-positively var (righttype-of-quotient-term term)))
		  (occurs-positively var (lefttype-of-quotient-term term)))
	     
	  || (eql term-kind 'UNION) -->
	     (and (occurs-positively var (lefttype-of-union-term term))
		  (occurs-positively var (righttype-of-union-term term)))

	  || (eql term-kind 'PAIR) -->
	     (and (occurs-positively var (leftterm-of-pair-term term))
		  (occurs-positively var (rightterm-of-pair-term term)))

	  || (member term-kind '(INL INR)) -->
	     (occurs-positively var (term-of-injection-term term))

	  || (eql term-kind 'DOM) -->
	     (occurs-positively var (term-of-dom-term term))

	  || (eql term-kind 'PARFUNCTION) -->
	     (and (or (eql var (bound-id-of-parfunction-term term))
		      (occurs-positively var (righttype-of-parfunction-term term)))
		  (occurs-positively var (lefttype-of-parfunction-term term)))

	  || (eql term-kind 'FUNCTION) -->
	     (and (not (member var (free-vars (lefttype-of-function-term term))))
		  (or (eql var (bound-id-of-function-term term))
		      (occurs-positively var (righttype-of-function-term term))))

	  || (eql term-kind 'APPLY) -->
	     (and (not (member var (free-vars (arg-of-apply-term term))))
		  (occurs-positively var (function-of-apply-term term)))

	  || (eql term-kind 'APPLY-PARTIAL) -->
	     (and (not (member var (free-vars (arg-of-apply-partial-term term))))
		  (occurs-positively var (function-of-apply-partial-term term)))

	  || (eql term-kind 'BOUND-ID-TERM) -->
	     (Pif (member var (bound-ids-of-bound-id-term term)) --> t

	      || t --> (occurs-positively var (term-of-bound-id-term term))

	      fi)

	  || (eql term-kind 'BOUND-ID-LIST) -->
	     (Pif (member var (bound-ids-of-bound-id-list-term term)) --> t

	      || t -->(Plet (result t)
		           (for (x in (term-list-of-bound-id-list-term term))
			        (when (not (occurs-positively var x)))
			              (do
			                (<- result nil)
			         )
		           )
		           result
	               )

	      fi)

	  || (eql term-kind 'LAMBDA) -->
	     (Pif (eql var (bound-id-of-lambda-term term)) --> t

	      || t --> (occurs-positively var (term-of-lambda-term term))

	      fi)

	  || (eql term-kind 'RECURSIVE) -->
	     (and (not (member var (free-vars (term-of-recursive-term term))))
		  (occurs-positively
		    var
		    (bound-id-list-term-of-recursive-term term)
		  )
		  (occurs-positively var (fix-term-of-recursive-term term))
	     )

	  || (eql term-kind 'FIX) -->
	     (occurs-positively var (bound-id-list-term-of-fix-term term))

	  || (eql term-kind 'REC-IND) -->
	     (and (not (member var (free-vars (term-of-rec-ind-term term))))
		  (occurs-positively var (bound-id-list-term-of-rec-ind-term term)))

	  || (eql term-kind 'SIMPLE-REC-IND) -->
	     (and (not (member var (free-vars (value-of-simple-rec-ind-term term))))
		  (occurs-positively var (term-of-simple-rec-ind-term term)))

	  || (eql term-kind 'TAGGED) -->
	     (occurs-positively var (term-of-tagged-term term))

	  || (eql term-kind 'EQUAL) -->
	     (Pevery #'(lambda (x) (occurs-positively var x))
		    (subterms-of-term term))

	  fi)
    )
)

(defun is-base-term (x)
    (Pif (eql (kind-of-term x) 'BOUND-ID-TERM) -->
	(is-base-term (term-of-bound-id-term x))
     || (eql (kind-of-term x) 'BOUND-ID-LIST-TERM) -->
        (not (member nil
		   (mapcar #'(lambda (z) (is-base-term z))
			   (term-list-of-bound-id-list-term x))))
     || t -->
        (and (eql (kind-of-term x) 'EQUAL)
	     (eql (kind-of-term (type-of-equal-term x)) 'INT)
	     (= (length (terms-of-equal-term x)) 1)
	     (eql (kind-of-term (car (terms-of-equal-term x))) 'POS-NUMBER)
	     (= (number-of-pos-number-term (car (terms-of-equal-term x))) 0)
        )
     fi)
)

;--
;-- domain-transform
;--
;-- 
(defun domain-transform (x id-pair-list bound-ids)
    (Plet (term-kind   (kind-of-term x)
	  base-term   (equal-term 'EQUAL
				  nil
				  (int-term 'INT nil)
				  (list (pos-number-term 'POS-NUMBER nil 0))
		      )
	  )
	 (Pif (eql term-kind 'APPLY-PARTIAL) -->
	     (Plet (arg      (domain-transform
			      (arg-of-apply-partial-term x) id-pair-list bound-ids
			    )
		   function nil
		  )
		  (Pif (and (eql (kind-of-term (function-of-apply-partial-term x)) 'VAR)
			   (assoc (id-of-var-term (function-of-apply-partial-term x))
				  id-pair-list
			   )
			   (not
			     (member (id-of-var-term (function-of-apply-partial-term x))
				   bound-ids
			     )
			   )
		       ) -->   (Pif (is-base-term arg) -->
				    (apply-term 'APPLY nil
				       (cdr (assoc (id-of-var-term
						   (function-of-apply-partial-term x)
						 )
						 id-pair-list
					    )
				       )
				      (arg-of-apply-partial-term x)
				    )
				 || t -->
				    (product-term 'PRODUCT nil nil arg
				      (apply-term 'APPLY nil
					(cdr (assoc (id-of-var-term
						   (function-of-apply-partial-term x)
						  )
						  id-pair-list
					     )
				        )
				       (arg-of-apply-partial-term x)
				      )
				    )
				 fi)
		  || t -->
		     (<- function (domain-transform
				    (function-of-apply-partial-term x) id-pair-list bound-ids
				  )
		     )
		     (Pif (and (is-base-term function) (is-base-term arg)) -->
			 (apply-term 'APPLY nil
			    (dom-term 'DOM nil (function-of-apply-partial-term x))
			    (arg-of-apply-partial-term x)
			 )
		      || (is-base-term function) -->
		         (product-term 'PRODUCT nil nil arg
			    (apply-term 'APPLY nil
			       (dom-term 'DOM nil (function-of-apply-partial-term x))
			       (arg-of-apply-partial-term x)
			    )
			 )
		      || (is-base-term arg) -->
		         (product-term 'PRODUCT nil nil function
			    (apply-term 'APPLY nil
			       (dom-term 'DOM nil (function-of-apply-partial-term x))
			       (arg-of-apply-partial-term x)
			    )
			 )
		      || t -->
		         (product-term 'PRODUCT nil nil function
			    (product-term 'PRODUCT nil nil arg
			       (apply-term 'APPLY nil
			          (dom-term 'DOM nil (function-of-apply-partial-term x))
			          (arg-of-apply-partial-term x)
			       )
			    )
			 )
		      fi)
		  fi)
	     )

	  || (eql term-kind 'SPREAD) -->
	     (Plet (value          (domain-transform (value-of-spread-term x)
						    id-pair-list
						    bound-ids
				  )
		   term-of-spread (domain-transform (term-of-spread-term x)
						    id-pair-list
						    bound-ids
				  )
		  )
		  (Pif (and (is-base-term value) (is-base-term term-of-spread)) -->
		      base-term
		   || (is-base-term value) -->
		      (spread-term 'SPREAD nil (value-of-spread-term x) term-of-spread)
		   || t -->
		      (product-term 'PRODUCT nil nil value
			(spread-term 'SPREAD nil (value-of-spread-term x) term-of-spread)
		      )
		   fi)
	     )

	  || (eql term-kind 'DECIDE) -->
	     (Plet (value (domain-transform (value-of-decide-term x) id-pair-list bound-ids)
		   left  (domain-transform (leftterm-of-decide-term x) id-pair-list bound-ids)
		   right (domain-transform
			   (rightterm-of-decide-term x) id-pair-list bound-ids
			 )
		  )
		  (Pif (and
			(is-base-term value) (is-base-term left) (is-base-term right)
		      ) --> base-term
		      
		   || (and (is-base-term left) (is-base-term right)) --> value

		   || (is-base-term value) -->
		      (decide-term 'DECIDE nil (value-of-decide-term x) left right)

		   || t -->
		      (product-term 'PRODUCT nil nil value
			  (decide-term 'DECIDE nil (value-of-decide-term x) left right)
		      )
		   fi)
	     )

	  || (eql term-kind 'BOUND-ID-TERM) -->
	     (bound-id-term
	       'BOUND-ID-TERM
	       nil
	       (bound-ids-of-bound-id-term x)
	       (domain-transform
		  (term-of-bound-id-term x)
		  id-pair-list
		  (append bound-ids (bound-ids-of-bound-id-term x))
	        )
	     )

	  || (eql term-kind 'BOUND-ID-LIST-TERM) -->
	     (bound-id-list-term
	       'BOUND-ID-LIST
	       nil
	       (bound-ids-of-bound-id-list-term x)
	       (mapcar #'(lambda (y)
			  (domain-transform
			    y
			    id-pair-list
			    (append bound-ids (bound-ids-of-bound-id-list-term x))
			  )
		       )
		       (term-list-of-bound-id-list-term x)
	       )
	     )

	  || (member term-kind '(ATOMEQ INTEQ INTLESS)) -->
	     (Plet (left
		     (domain-transform (leftterm-of-decision-term x) id-pair-list bound-ids)
		   right
		     (domain-transform (rightterm-of-decision-term x) id-pair-list bound-ids)
		   if-term
		     (domain-transform (if-term-of-decision-term x) id-pair-list bound-ids)
		   else-term
		     (domain-transform (else-term-of-decision-term x) id-pair-list bound-ids)
		  )
		  (Pif (and (is-base-term left) (is-base-term right)
			   (is-base-term if-term) (is-base-term else-term)
		      ) --> base-term

		   || (and (is-base-term left) (is-base-term right)) -->
		      (decision-term
			 (kind-of-decision-term x)
			 nil
			 (leftterm-of-decision-term x)
			 (rightterm-of-decision-term x)
			 if-term else-term
		      )
		   || (and (is-base-term if-term) (is-base-term else-term)) -->
		      (Pif (is-base-term left) --> right

		       || (is-base-term right) --> left

		       || t --> (product-term 'PRODUCT nil nil left right)

		       fi)

		   || (not (and (is-base-term left) (is-base-term right)
			        (is-base-term if-term) (is-base-term else-term)
			   )
		      ) -->
		         (product-term 'PRODUCT nil nil left
				       (product-term 'PRODUCT nil nil right
					  (decision-term
			                     (kind-of-decision-term x)
					     nil
					     (leftterm-of-decision-term x)
					     (rightterm-of-decision-term x)
					     if-term else-term
		                           )
					)
		       )
		    || t --> (product-term 'PRODUCT nil nil
					   (Pif (is-base-term left) --> right
		                            || (is-base-term right) --> left
		                            fi)
					   (decision-term
			                     (kind-of-decision-term x)
					     nil
					     (leftterm-of-decision-term x)
					     (rightterm-of-decision-term x)
					     if-term else-term
		                           )
					   
			     )
		    fi)
		      
	     )

	  || (eql term-kind 'IND) -->
	     (Plet (value  (domain-transform (value-of-ind-term x) id-pair-list bound-ids)
		   downt  (domain-transform (downterm-of-ind-term x) id-pair-list bound-ids)
		   baset  (domain-transform (baseterm-of-ind-term x) id-pair-list bound-ids)
		   upt    (domain-transform (upterm-of-ind-term x) id-pair-list bound-ids)
		  )
		  (Pif (and (is-base-term value) (is-base-term downt)
			   (is-base-term baset) (is-base-term upt)
		      ) --> base-term
		   || (and  (is-base-term downt) (is-base-term baset) (is-base-term upt)) -->
		      value
		   || (is-base-term value) -->
		      (ind-term 'IND nil (value-of-ind-term x) downt baset upt)
		   || t -->
		      (product-term 'PRODUCT nil nil value
				    (ind-term 'IND nil (value-of-ind-term x) downt baset upt)
		      )
		   fi)
	     )

	  || (eql term-kind 'LIST-IND) -->
	     (Plet (value
		     (domain-transform (value-of-list-ind-term x) id-pair-list bound-ids)
		   baset
		     (domain-transform (baseterm-of-list-ind-term x) id-pair-list bound-ids)
		   upt
		     (domain-transform (upterm-of-list-ind-term x) id-pair-list bound-ids)
		  )
		  (Pif (and (is-base-term value) 
			   (is-base-term baset) (is-base-term upt)
		      ) --> base-term
		   || (and (is-base-term baset) (is-base-term upt)) -->
		      value
		   || (is-base-term value) -->
		      (list-ind-term 'LIST-IND nil (value-of-list-ind-term x) baset upt)
		   || t -->
		      (product-term 'PRODUCT nil nil value
			 (list-ind-term 'LIST-IND nil (value-of-list-ind-term x) baset upt)
		      )
		   fi)
	     )

	  || (eql term-kind 'REC-IND) -->
	     (Plet (term
		     (domain-transform (term-of-rec-ind-term x) id-pair-list bound-ids)
		   sub-term
		     (domain-transform
		       (bound-id-list-term-of-rec-ind-term x) id-pair-list bound-ids
		     )
		  )
		  (Pif (and (is-base-term term) (is-base-term sub-term)) --> base-term
		   || (is-base-term term) -->
		      (rec-ind-term
			'REC-IND nil (term-of-rec-ind-term x) sub-term (id-of-rec-ind-term x)
		      )
		   || t -->
		      (product-term 'PRODUCT nil nil term
			(rec-ind-term
			 'REC-IND nil (term-of-rec-ind-term x) sub-term (id-of-rec-ind-term x)
		        )
		      )
		   fi)
	     )

	  || (eql term-kind 'LAMBDA) -->
	     (domain-transform (term-of-lambda-term x) id-pair-list bound-ids)

	  || (eql term-kind 'APPLY) -->
	     (Plet (function
		    (domain-transform (function-of-apply-term x) id-pair-list bound-ids)
		   arg
		    (domain-transform (arg-of-apply-term x) id-pair-list bound-ids)
		  )
		  (Pif (is-base-term function) --> arg

		   || (is-base-term arg) --> function

		   || t --> (product-term 'PRODUCT nil nil function arg)

		   fi)
	     )

	  || (member term-kind '(INR INL)) -->
	     (domain-transform (term-of-injection-term x) id-pair-list bound-ids)

	  || (eql term-kind 'MINUS) -->
	     (domain-transform (term-of-minus-term x) id-pair-list bound-ids)

	  || (member term-kind '(ADD SUB MUL DIV MOD)) -->
	     (Plet (left
		     (domain-transform (leftterm-of-binary-term x) id-pair-list bound-ids)
		   right
		     (domain-transform (rightterm-of-binary-term x) id-pair-list bound-ids)
		  )
		  (Pif (is-base-term left) --> right

		   || (is-base-term right) --> left

		   || t --> (product-term 'PRODUCT nil nil left right)

		   fi)
	     )

	  || (eql term-kind 'CONS) -->
	     (Plet (head  (domain-transform (head-of-cons-term x) id-pair-list bound-ids)
		   tail  (domain-transform (tail-of-cons-term x) id-pair-list bound-ids)
		  )
		  (Pif (is-base-term head) --> tail

		   || (is-base-term tail) --> head

		   || t --> (product-term 'PRODUCT nil nil head tail)

		   fi)
	     )

	  || (eql term-kind 'PAIR) -->
	     (Plet (left  (domain-transform (leftterm-of-pair-term x) id-pair-list bound-ids)
		   right (domain-transform (rightterm-of-pair-term x) id-pair-list bound-ids)
		  )
		  (Pif (is-base-term left) --> right

		   || (is-base-term right) --> left

		   || t --> (product-term 'PRODUCT nil nil left right)

		   fi)
	     )

	  || t --> base-term 

	  fi)
    )
)

;--------------------------------;
;                                ;
;   SET MANIPULATION ROUTINES    ;
;                                ;
;--------------------------------;

;--
;-- Sets are stored as unordered lists with no duplicates.
;-- Eventually this representation may change.  Elements of
;-- sets are arbitrary s-expressions.
;--


;--
;-- list-to-set (x:list)
;--
;--     Turn the list x into a set.  This is trivial since sets are
;--     stored as unordered lists.
;--

(defun list-to-set (x)
    
    x

)


;--
;-- set-to-list (x:set)
;--
;--     Turn the set x into a list.  This is trivial since sets are
;--     stored as unordered lists.
;--

(defun set-to-list (x)
    
    x

)


;--
;-- set-union2 (x:set, y:set)
;--
;--     Return the union of x and y.
;--

(defun set-union2 (x y)

    (set-union (list x y))

)


;--
;-- set-union (x:list-of-sets)
;--
;--     Return the union of the elements of x.  That is, append together
;--     all the elements of x, but remove duplicates.
;--

(defun set-union (x)

    (Plet (result nil    ;-- the result built so far
         )

        (for (set in x)
             (do
                 (for (elem in set)
                      (do
                          (Pif (not (member elem result)) -->
                              (<- result (cons elem result))
                           fi)
                      )
                 )
             )
        )

        result

    )
)


;--
;-- set-difference (x:set, y:set)
;--
;--     Return the set containing elements of x not occurring in y.
;--

(defun prl-set-difference (x y)

    (Plet (result nil    ;-- the elements of x not in y, so far
         )
    
        (for (elem in x)
             (do
                 (Pif (not (member elem y)) -->
                     (<- result (cons elem result))
                  fi)
             )
        )

        result

    )

)

;-- 
;-- set-intersection (x:set, y:set)
;-- 

(defun set-intersection (x y)
    (Ploop
        (local answer nil)
        (while (not (null x)))
        (do
            (Pif (member (car x) y) -->
                (<- answer (cons (car x) *-*))
             fi)
            (<- x (cdr x))
        )
        (result answer)
    )
)


;;; has no two eq list members.
(defun no-duplicates? (x)
    (or (null x)
	(and (not (member (car x) (cdr x)))
	     (no-duplicates? (cdr x)))))




(defun ref-assert (P x msg-atom)
  (cond ((funcall P x) x)
	(t (ref-error msg-atom))))


(defun genvar () (gentemp "v" (find-package 'nuprl)))
