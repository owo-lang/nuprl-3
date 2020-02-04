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


;;; The monotonicity rule.

(defparameter valid-monot-opkinds '(PLUS MINUS MULT DIV)
  "The valid operator kinds for monotonicity")

(defparameter monot-pattern-vars '(|t1| |t2| |t3| |t4|)
  "The variables used in the pattern-terms in the monotonicity tables")

;;; Tables associating the op-kind atoms to the numbers
;;;   used as indices into the monotonicity tables.
(defvar relation-codes-plus)
(defvar relation-codes-minus)
(defvar relation-codes-mult2)
(defvar relation-codes-mult1)
(defvar relation-codes-div1)
(defvar relation-codes-div2)

;;; The arrays.
(defvar monot-table-plus)
(defvar monot-table-minus)
(defvar monot-table-mult)
(defvar monot-table-div)


(defun init-monotonicity ()
    ;; Initializes the monotonicity tables.
    (setq relation-codes-plus
	  (pairup '(GREATER GEQ EQ NEQ) '(0 1 2 3)))
    (setq relation-codes-minus
	  (pairup '(GREATER GEQ EQ NEQ) '(0 1 2 3)))
    (setq relation-codes-mult2
	  (pairup '(GEQ GREATER EQ NEQ) '(0 1 2 3)))
    (setq relation-codes-mult1
	  (pairup '(GREATER GEQ EQ LEQ LESS NEQ) '(0 1 2 3 4 5)))
    (setq relation-codes-div1
	  (pairup '(GREATER LESS NEQ) '(0 1 2)))
    (setq relation-codes-div2
	  (pairup '(GREATER GEQ EQ NEQ) '(0 1 2 3)))
    (setq monot-table-plus (make-array '(4 4) :initial-contents
      (list
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1+t3 < t2+t4+2) -> void|
	  '|(t1+t3 < t2+t4+1) -> void|
	  '|((t1+t3 < t2+t4+1) -> void) # ((t1+t4 < t2+t3+1) -> void)|
	  '|ERROR|))
       (mapcar 
	#'make-prl-term
	(list
	  '|(t1+t3 < t2+t4+1) -> void|
	  '|(t1+t3 < t2+t4) -> void|
	  '|((t1+t3 < t2+t4)->void) # ((t1+t4 < t2+t3) -> void)|
	  '|ERROR|))
       (mapcar 
	#'make-prl-term
	(list
	  '|((t1+t3 < t2+t4+1)->void) # ((t2+t3 < t1+t4+1) -> void)|
	  '|((t1+t3 < t2+t4)->void) # ((t2+t3 < t1+t4) -> void)|
	  '|(t1+t3 = t2+t4 in int) # (t1+t4 = t2+t3 in int)|
	  '|((t1+t3 = t2+t4 in int)->void) # ((t1+t4 = t2+t3 in int) -> void)|))
       (mapcar 
	#'make-prl-term
	(list
	  '|ERROR|
	  '|ERROR|
	  '|((t1+t3 = t2+t4 in int)->void) # ((t1+t4 = t2+t3 in int) -> void)|
	  '|ERROR|)))))

    (setq monot-table-minus (make-array '(4 4) :initial-contents
      (list
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1-t4 < (t2-t3)+2) -> void|
	  '|(t1-t4 < (t2-t3)+1) -> void|
	  '|((t1-t4 < (t2-t3)+1)->void) # ((t1-t3 < (t2-t4)+1) -> void)|
	  '|ERROR|))
       (mapcar 
 	 #'make-prl-term
 	 (list
	  '|(t1-t4 < (t2-t3)+1) -> void|
	  '|(t1-t4 < t2-t3) -> void|
	  '|((t1-t4 < t2-t3)->void) # ((t1-t3 < t2-t4) -> void)|
	  '|ERROR|))
       (mapcar 
	 #'make-prl-term
	 (list
	  '|((t1-t4 < (t2-t3)+1)->void) # ((t2-t4 < (t1-t3)+1) -> void)|
	  '|((t1-t4 < t2-t3)->void) # ((t2-t4 < t1-t3) -> void)|
	  '|(t1-t4 = t2-t3 in int) # (t2-t4 = t1-t3 in int)|
	  '|((t1-t4 = t2-t3 in int)->void) # ((t1-t3 = t2-t4 in int) -> void)|))
       (mapcar 
	 #'make-prl-term
	 (list
	  '|ERROR|
	  '|ERROR|
	  '|((t1-t4 = t2-t3 in int)->void) # ((t1-t3 = t2-t4 in int) -> void)|
	  '|ERROR|)))))

    (setq monot-table-mult (make-array '(6 4) :initial-contents
      (list
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1*t2 < t1*t3) -> void|
	  '|(t1*t3 < t1*t2)|
	  '|(t1*t2 =  t1*t3 in int)|
	  '|(t1*t2 = t1*t3 in int) -> void|))
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1*t2 < t1*t3) -> void|
	  '|(t1*t2 < t1*t3) -> void|
	  '|(t1*t2 =  t1*t3 in int)|
	  '|ERROR|))
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1*t2 = t1*t3 in int) # (t1*t3 = 0 in int)|
	  '|(t1*t2 = t1*t3 in int) # (t1*t2 = 0 in int)|
	  '|(t1*t2 = t1*t3 in int) # (t1*t2 = 0 in int)|
	  '|(t1*t2 = t1*t3 in int) # (t1*t2 = 0 in int)|))
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1*t3 < t1*t2) -> void|
	  '|(t1*t3 < t1*t2) -> void|
	  '|(t1*t2 =  t1*t3 in int)|
	  '|ERROR|))
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1*t3 < t1*t2) -> void|
	  '|(t1*t2 < t1*t3)|
	  '|(t1*t2 =  t1*t3 in int)|
	  '|(t1*t2 = t1*t3 in int) -> void|))
      (mapcar 
	#'make-prl-term
	(list
	  '|ERROR|
	  '|(t1*t2 = t1*t3 in int) -> void|
	  '|(t1*t2 =  t1*t3 in int)|
	  '|(t1*t2 = t1*t3 in int) -> void|)))))

    (setq monot-table-div (make-array '(3 4) :initial-contents
      (list
      (mapcar 
	#'make-prl-term
	(list
	  '|(t2 < t1)|
	  '|(t1 < t2) -> void|
	  '|(t1 = t2 in int)|
	  '|(t1 = t2 in int) -> void|))
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1 < t2)|
	  '|(t2 < t1) -> void|
	  '|(t1 = t2 in int)|
	  '|(t1 = t2 in int) -> void|))
      (mapcar 
	#'make-prl-term
	(list
	  '|(t1 = t2 in int) -> void|
	  '|ERROR|
	  '|(t1 = t2 in int)|
	  '|(t1 = t2 in int) -> void|)))))

    nil
)


(defun refine-monot () 
 (let*  
   ((hnum1    (hypnum1-of-monot-rule ref-rule))
    (hnum2    (hypnum2-of-monot-rule ref-rule))
    (opkind   (op-of-monot-rule ref-rule))
    (decl1    (get-assum$ hnum1 ref-assums))
    (decl2    (get-assum$ hnum2 ref-assums))
    (hyp1     (type-of-declaration decl1))
    (hyp2     (type-of-declaration decl2))
    (monot-result  (catch 'monot-tag
			  (do-monot$ opkind hyp1 hyp2))))
   (cond ((atom monot-result)
	  (ref-error monot-result))
	 (t
	  (<- ref-children
	      (list
		(make-child
		  (append
		    ref-assums
		    (ncons
		      (declaration nil nil monot-result)))
		  ref-concl)))))
   nil))


;; Checks opkind and the hypothesis-terms for correct format,
;;  and if correct, returns the new hypotheses-term (representing
;;  an inference using one instance of non-trivial monotonicity
;;  of integer arithmetic.)

(defun do-monot$ (opkind hyp1 hyp2)
  ;; Returns the new hypothesis term representing an inference using
  ;; one instance of non-trivial monotonicity.
  (case opkind
    (PLUS
     (lookup-and-make-literal$
       monot-table-plus (process-hyps-plus$ hyp1 hyp2)))
    (MINUS
     (lookup-and-make-literal$
       monot-table-minus (process-hyps-minus$ hyp1 hyp2)))
    (MULT
     (lookup-and-make-literal$
       monot-table-mult (process-hyps-mult$ hyp1 hyp2)))
    (DIV
     (lookup-and-make-literal$
       monot-table-div (process-hyps-div$ hyp1 hyp2)))
    (otherwise
     (throw 'monot-tag '|Improper operation given for monotonicity rule|))))

;; Returns the term which will be the new hypoth generated by
;;   monot rule.  Uses the indices (obtained from the relation-kind
;;   of the input hypoths), and the terms (primary subterms of
;;   the input hypoths) to find the right pattern-term in the monot
;;   tables and then perform the appropriate substitution.

(defun lookup-and-make-literal$  (table  indices-and-terms)
  
  (let*
    ((indices  (car indices-and-terms))
     (terms    (cadr indices-and-terms))
     (row      (car indices))
     (column   (cadr indices))
     (pattern-term  (aref table row column)))
    (cond
      ((is-error-term pattern-term)
       (throw 'monot-tag
              '|Wrong relation-kind in a monot hypothesis.|))
      (t
       (make-new-monot-literal pattern-term terms)))))

;; Pair up the variables from the pattern-term with
;;   the user-supplied terms.  Perform the substitution.
(defun make-new-monot-literal (pattern terms)
 (let*
   ((vars monot-pattern-vars)
    (subst-list  (pairup vars terms)))
   (substitute pattern subst-list)))

;;**********************************************************
;; The destruct-...-monot functions:
;;   Analyze a monot hypothesis, check for correct form,
;;   and return     1. relation-kind  ('EQ, 'LESS, etc.)
;;                  2. The two subterms
;;
;;   The correct format depends on which kind of monotonicity 
;;     (addition, mult, subt, div), and which of the two necessary
;;     hypoths is being processed.
;;
;;   There are six of these functions:
;;       addition     1
;;       subtraction  1
;;       multiplic.   2
;;       division     2
;;
;;**********************************************************
(defun destruct-plus-monot (hyp-term)

  (cond

    ((is-less-term hyp-term)
     (list  'GREATER
	    (rightterm-of-less-term hyp-term)
	    (leftterm-of-less-term hyp-term)))

    ((is-equal-term hyp-term)
       (let*  ((tms (terms-of-equal-term hyp-term)))
	 (cond
	   ((= (length tms) 1)
	    (list  'EQ
		   (car tms)
		   (car tms)))

	   (t
	    (list  'EQ
		   (car tms)
		   (cadr tms))))))

    ((is-not-term hyp-term)
     (let*  ((ltm (lefttype-of-function-term hyp-term)))
       (cond
	 ((is-less-term ltm)
	  (let*
	    ((left (leftterm-of-less-term ltm))
	     (right (rightterm-of-less-term ltm)))
	    (list  'GEQ
		   left
		   right)))

	 ((is-equal-term ltm)
	  (let* ((tms (terms-of-equal-term ltm)))
	    (cond
	      ((= (length tms) 2)
	       (list  'NEQ
		      (car tms)
		      (cadr tms)))
	      (t (throw 'monot-tag '|monot: Bad hypothesis, too many terms in equal term|)))))

       
	 (t (throw 'monot-tag '|monot: Bad format for hypothesis. |)))))

     (t (throw 'monot-tag '|monot: Bad format for hypothesis.|))))


(defun destruct-minus-monot (hyp-term)
  (destruct-plus-monot hyp-term))


(defun destruct-mult2-monot (hyp-term)
  (destruct-plus-monot hyp-term))


(defun destruct-mult1-monot (hyp-term)

  (cond

    ((is-less-term hyp-term)
     (let*
       ((left (leftterm-of-less-term hyp-term))
	(right (rightterm-of-less-term hyp-term)))
       (cond 
	 ((is-zero-term left)
	  (list  'GREATER
		 right
		 left))
	 ((is-zero-term right)
	  (list  'LESS
		 left
		 right))
	 (t (throw 'monot-tag '|monot: Bad format for hypothesis.|)))))

    ((is-equal-term hyp-term)
       (let*  ((tms (terms-of-equal-term hyp-term)))
	 (cond
	   ((= (length tms) 2)
	    (cond 
	      ((is-zero-term (car tms))
	       (list  'EQ
		      (cadr tms)
		      (car tms)))
	      ((is-zero-term (cadr tms))
	       (list  'EQ
		      (car tms)
		      (cadr tms)))
	      (t  (throw 'monot-tag '|monot: Bad format for hypothesis.|))))
	   (t  (throw 'monot-tag '|monot: Bad format for hypothesis.|)))))

	  

    ((is-not-term hyp-term)
     (let*  ((ltm (lefttype-of-function-term hyp-term)))
       (cond
	 ((is-less-term ltm)
	  (let*
	    ((left (leftterm-of-less-term ltm))
	     (right (rightterm-of-less-term ltm)))
	    (cond 
	      ((is-zero-term left)
	       (list  'LEQ
		      right
		      left))
	      ((is-zero-term right)
	       (list  'GEQ
		      left
		      right))
	      (t  (throw 'monot-tag '|monot: Bad format for hypothesis.|)))))

	 ((is-equal-term ltm)
	  (let* ((tms (terms-of-equal-term ltm)))
	    (cond
	      ((= (length tms) 2)
	       (cond 
		 ((is-zero-term (car tms))
		  (list  'NEQ
			 (cadr tms)
			 (car tms)))
		 ((is-zero-term (cadr tms))
		  (list  'NEQ
			 (car tms)
			 (cadr tms)))
		 (t  (throw 'monot-tag '|monot: Bad format for hypothesis.|))))

	      (t (throw 'monot-tag '|monot: Bad format for hypothesis.|)))))

       
	 (t (throw 'monot-tag '|monot: Bad format for hypothesis.|)))))

     (t (throw 'monot-tag '|monot: Bad format for hypothesis.|))))

(defun destruct-div2-monot (hyp-term)
  (destruct-plus-monot  hyp-term))

(defun destruct-div1-monot (hyp-term)

  (cond

    ((is-less-term hyp-term)
     (let*
       ((left (leftterm-of-less-term hyp-term))
	(right (rightterm-of-less-term hyp-term)))
       (cond 
	 ((is-zero-term left)
	  (list  'GREATER
		 right
		 left))
	 ((is-zero-term right)
	  (list  'LESS
		 left
		 right))
	 (t (throw 'monot-tag '|monot: Bad format for hypothesis.|)))))

	  

    ((is-not-term hyp-term)
     (let*  ((ltm (lefttype-of-function-term hyp-term)))
       (cond
	 ((is-equal-term ltm)
	  (let* ((tms (terms-of-equal-term ltm)))
	    (cond
	      ((= (length tms) 2)
	       (cond 
		 ((is-zero-term (car tms))
		  (list  'NEQ
			 (cadr tms)
			 (car tms)))
		 ((is-zero-term (cadr tms))
		  (list  'NEQ
			 (car tms)
			 (cadr tms)))
		 (t  (throw 'monot-tag '|monot: Bad format for hypothesis.|))))

	      (t (throw 'monot-tag '|monot: Bad format for hypothesis.|)))))

       
	 (t (throw 'monot-tag '|monot: Bad format for hypothesis.|)))))

     (t (throw 'monot-tag '|monot: Bad format for hypothesis.|))))

;; Process the user's two hypotheses given to
;;  the monotonicity-addition rule.
;; Return list (rels  tms), where
;;   rels is list of the two relation-codes which will
;;   index into the monotonicity-addition table, and
;;   tms is list of the terms given for substitution into
;;   the new, rule-generated hypothesis term.
;;
(defun process-hyps-plus$ (hyp1 hyp2)
  (let*
    ((results1  (destruct-plus-monot hyp1))
     (results2  (destruct-plus-monot hyp2))
     (rel1  (cadr (assoc (car results1) relation-codes-plus)))
     (rel2  (cadr (assoc (car results2) relation-codes-plus)))
     (t1  (cadr results1))
     (t2  (caddr results1))
     (t3  (cadr results2))
     (t4  (caddr results2)))
    (list
      (list rel1 rel2)
      (list t1 t2 t3 t4))))

;; Process the user's two hypotheses given to
;;  the monotonicity-subtraction rule.
;; Return list (rels  tms), where
;;   rels is list of the two relation-codes which will
;;   index into the monotonicity-subtraction table, and
;;   tms is list of the terms given for substitution into
;;   the new, rule-generated hypothesis term.
;;
(defun process-hyps-minus$ (hyp1 hyp2)
  (let*
    ((results1  (destruct-minus-monot hyp1))
     (results2  (destruct-minus-monot hyp2))
     (rel1  (cadr (assoc (car results1) relation-codes-minus)))
     (rel2  (cadr (assoc (car results2) relation-codes-minus)))
     (t1  (cadr results1))
     (t2  (caddr results1))
     (t3  (cadr results2))
     (t4  (caddr results2)))
    (list
      (list rel1 rel2)
      (list t1 t2 t3 t4))))

;; Process the user's two hypotheses given to
;;  the monotonicity-multiplication rule.
;; Return list (rels  tms), where
;;   rels is list of the two relation-codes which will
;;   index into the monotonicity-multiplication table, and
;;   tms is list of the terms given for substitution into
;;   the new, rule-generated hypothesis term.
(defun process-hyps-mult$ (hyp1 hyp2)
  (let*
    ((results1  (destruct-mult1-monot hyp1))
     (results2  (destruct-mult2-monot hyp2))
     (rel1  (cadr (assoc (car results1) relation-codes-mult1)))
     (rel2  (cadr (assoc (car results2) relation-codes-mult2)))
     (t1  (cadr results1))
    
     (t2  (cadr results2))
     (t3  (caddr results2)))
    (list
      (list rel1 rel2)
      (list t1 t2 t3))))

;; Process the user's two hypotheses given to
;;  the monotonicity-division rule.
;; Return list (rels  tms), where
;;   rels is list of the two relation-codes which will
;;   index into the monotonicity-division table, and
;;   tms is list of the terms given for substitution into
;;   the new, rule-generated hypothesis term.
(defun process-hyps-div$ (hyp1 hyp2)
  (declare (ignore hyp1 hyp2))
  (ref-error '|The monotonicity rule is not yet implemented for division.  Sorry.|)
  #|
  (let*
    ((results1  (destruct-div1-monot hyp1))
     (results2  (destruct-div2-monot hyp2))
     (rel1  (cadr (assoc (car results1) relation-codes-div1)))
     (rel2  (cadr (assoc (car results2) relation-codes-div2)))
     (t1  (cadr results1))
    
     (t2  (cadr results2))
     (t3  (caddr results2))
     (d1  (simplify (poly-div t2 t1)))
     (d2  (simplify (poly-div t3 t1))))
    (list
       (list rel1 rel2)
       (list d1 d2)))
  |#)



