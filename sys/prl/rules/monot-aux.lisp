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


;; ******************************************************************
;; ******************************************************************
;; ******************************************************************
;;
;; Auxilliary Functions Used by the Main Monotonicity Rule Functions
;;
;; ******************************************************************
;; ******************************************************************
;; ******************************************************************

(defun make-prl-term (tok) (parse (cons 'Ttree (istring tok))))

;; Returns the (obvious) list of pairs of elements (e1 e2),
;;   ei froom listi.  Length is lenth of shorter of the two lists.
(defun pairup (list1 list2)
  (cond
    ((null list1)  nil)			 
    ((null list2)  nil)
    (t 
      (cons  (list (car list1)
		   (car list2))
	     (pairup (cdr list1)
		     (cdr list2))))))


;************************************************
;************************************************
; Predicates on nuprl terms
;
;************************************************

(defun is-not-term (tm)
  (and
     (eql (kind-of-term tm) 'FUNCTION)
     (eql (kind-of-term (righttype-of-function-term tm))  'VOID)))

(defun is-less-term (tm)
  (eql (kind-of-term tm) 'LESS))

(defun is-equal-term (tm)
  (eql (kind-of-term tm)  'EQUAL))

(defun is-minus-term (tm)
  (eql (kind-of-term tm) 'MINUS))

; Is tm the polynomial representing zero?

(defun is-zero-term (tm)
  (and
    (eql (kind-of-term tm) 'POS-NUMBER)
    (=  (number-of-pos-number-term tm) 0)))


; Is tm the special error-term used by monot-tables?
					    
(defun is-error-term (tm)
  (and  (eql (kind-of-term tm) 'VAR)
	(eql (id-of-var-term tm) 'ERROR)))

;**********************************************
;**********************************************
;
;  Term Manipulators
;
;**********************************************
;**********************************************


; Returns the first summand if tm is an add-term
;   else tm

(defun first-of-poly (poly) 
  (cond ((eql (kind-of-term poly) 'ADD)
	 (caddr poly))
	
	(t poly)
   ))



; Returns the second summand if tm is an add-term
;   else nil

(defun rest-of-poly (poly) 
  (cond ((eql (kind-of-term poly) 'ADD)
	 (cadddr poly))
	
	(t nil)
   ))


;  Returns the second summand of a normalized (right-associated)
;   poly.

(defun second-of-poly (poly)
  (first-of-poly (rest-of-poly poly)))


;  Returns the first factor in a mult term
;    else the term

(defun first-of-monomial (tm)
  (cond 
    ((eql (kind-of-term tm)
	 'MUL)
     (caddr tm))

    (t tm)))




; Returns the second factor, if tm a mult term
;   else tm.

(defun rest-of-monomial (tm)
  (cond
    ((eql (kind-of-term tm)
	 'MUL)
     (cadddr tm))

    (t nil)))





;  Construct a binary term: either
;   'MUL, 'DIV 'ADD 'SUB 'MOD, depending on type.

(defun make-binary-term (type ttree left right)
  (cond
    ((and (null left)
	  (null right))
     nil)

    ((null left)  right)
    
    ((null right) left)
    
    (t  (binary-term  type
		      ttree
		      left
		      right))))








;  Are terms the same kind of term?

(defun same-kind-terms (term1 term2) 
  (eql (kind-of-term term1)
      (kind-of-term term2)))





; (In some applications, it's useful to view poly's
;    as lists.)  Is tm null?

(defun null-poly-p (tm) (eql tm nil))





;  Return tm stripped of its leading integer coefficient.

(defun remove-coeff (tm)
  (cond
     ((eql (kind-of-term (first-of-monomial tm))
	  'POS-NUMBER)
      (rest-of-monomial tm))

     (t tm)))






; (p1 - p2) in the ring of polys  

(defun poly-subtract (p1 p2)
  (reverse-normalized-sum 
    (simplify
      (poly-add 
	(list p1 (dist-neg p2))))))






; Reverse the order of summands in normalized polynomial
;  term.  (Order needed for poly division is opposite that
;  used in other nuprl functions).

(defun reverse-normalized-sum (term)
  (labels
    ((rev-sum (tm accum) 
	 (cond
	   ((not (eql (kind-of-term tm)
		     'ADD))
	    (make-binary-term 'ADD 
			      nil
			      tm
			      accum))
    
	   (t  (let* 
		 ((head (first-of-poly tm))
		  (new-accum (make-binary-term 'ADD 
					       nil
					       head
					       accum)))
	  
		 (rev-sum (rest-of-poly tm)
			  new-accum))))))
  (rev-sum term
	   nil)))

