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


;*****************************************************************************
;*****************************************************************************
;*****************************************************************************
;
; MAIN FUNCTIONS IMPLEMENTING THE DIVISION RULE
;
;*****************************************************************************
;*****************************************************************************
;*****************************************************************************



;; Variables used in the pattern terms

(defparameter div-pattern-vars `(|a| |b| |q| |r|))

(defun is-addition-term (tm)
  (eql (kind-of-term tm) 'ADD))



(defun is-subtraction-term (tm)
  (eql (kind-of-term tm) 'SUB))


(defun is-division-term (tm)
  (eql (kind-of-term tm) 'DIV))


(defun is-mod-term (tm)
  (eql (kind-of-term tm) 'MOD))

(defun is-conjunction (tm)
  (and (eql (kind-of-term tm)  'PRODUCT)
       (equal (bound-id-of-product-term tm) nil)))

(defun is-mult-term (tm)
  (eql (kind-of-term tm) 'MUL))

(defun is-int-binary-equality (tm)
  (and
    (is-equal-term tm)
    (= (length (terms-of-equal-term tm)) 2)
    (eql (kind-of-term (type-of-equal-term tm)) 'INT)))


;; Catch the result of (do-division ref-concl) , and if it succeeds attach the
;; newly generated subgoals (each will have same hyps as current sequent but a new
;; conclusion).  If it fails, return error message.

(defun refine-division ()
  (let*
    ((goal  ref-concl)
     (assums ref-assums)
     (result  (catch 'division-tag
		      (do-division goal))))
    (cond
      
      ((atom result)
       (ref-error result))
      
      (t
       (<- ref-children 
	   (mapcar
	     #'(lambda (newconcl) (make-child assums newconcl))
	     result))))
    nil))


;; Partially destructs the goal-term (conclusion) and decides which of the
;; division rules is appropriate, and invokes the corresponding function to 
;; analyze the term further.  Returns the list of new conclusions or else fails
;; in non-local exit with message.

(defun do-division (goal-term)
  (cond
    ((is-int-binary-equality goal-term)
     (let* 
       ((left-equand (car (terms-of-equal-term goal-term)))
	(right-equand (cadr (terms-of-equal-term goal-term))))
       
       (cond 
	 
	 ((and 
	    (is-addition-term left-equand)
	    (is-mod-term (leftterm-of-binary-term left-equand)))
	  (process-div1-goal  right-equand
			      (rightterm-of-binary-term left-equand)
			      (leftterm-of-binary-term left-equand)))
	 
	 ((and 
	    (is-addition-term left-equand)
	    (is-mod-term (rightterm-of-binary-term left-equand)))
	  (process-div1-goal  right-equand
			      (leftterm-of-binary-term left-equand)
			      (rightterm-of-binary-term left-equand)))
	 
	 
	 ((and 
	    (is-addition-term right-equand)
	    (is-mod-term (leftterm-of-binary-term right-equand)))
	  (process-div1-goal  left-equand
			      (rightterm-of-binary-term right-equand)
			      (leftterm-of-binary-term right-equand)))
	 
	 ((and 
	    (is-addition-term  right-equand)
	    (is-mod-term (rightterm-of-binary-term right-equand)))
	  (process-div1-goal  left-equand
			      (leftterm-of-binary-term right-equand)
			      (rightterm-of-binary-term right-equand)))
	 
; ----------	
	 
	 
	 ((and 
	    (is-subtraction-term left-equand)
	    (is-mod-term (leftterm-of-binary-term left-equand)))
	  (process-div2-goal  right-equand
			      (rightterm-of-binary-term left-equand)
			      (leftterm-of-binary-term left-equand)))
	 
	 ((and 
	    (is-subtraction-term left-equand)
	    (is-mod-term (rightterm-of-binary-term left-equand)))
	  (process-div2-goal  right-equand
			      (leftterm-of-binary-term left-equand)
			      (rightterm-of-binary-term left-equand)))
	 
	 
	 ((and 
	    (is-subtraction-term right-equand)
	    (is-mod-term (leftterm-of-binary-term right-equand)))
	  (process-div2-goal  left-equand
			      (rightterm-of-binary-term right-equand)
			      (leftterm-of-binary-term right-equand)))
	 
	 ((and 
	    (is-subtraction-term  right-equand)
	    (is-mod-term (rightterm-of-binary-term right-equand)))
	  (process-div2-goal  left-equand
			      (leftterm-of-binary-term right-equand)
			      (rightterm-of-binary-term right-equand)))
	 
	 ((and (is-zero-term left-equand)
	       (is-division-term right-equand))
	  (process-div5-goal  right-equand))
	 
	 
	 ((and (is-zero-term right-equand)
	       (is-division-term left-equand))
	  (process-div5-goal  left-equand))
	 
	 
	 (t (throw 'division-tag '|division: Bad goal format.|)))))
    
    
    ((is-less-term goal-term)
     (let*
       ((lesser (leftterm-of-less-term goal-term))
	(greater (rightterm-of-less-term goal-term)))
       (cond
	 
	 ((and  (is-zero-term lesser)
		(is-division-term greater))
	  (process-div3-goal greater))
	 
	 ((and  (is-zero-term greater)
		(is-division-term lesser))
	  (process-div4-goal lesser))
	 
	 (t  (throw 'division-tag
	            '|division: Goal has bad format.  Less-term should be either 0<a/b or a/b<0|)))))
    
    ((is-conjunction goal-term)
     (let* 
       ((conjunct1 (lefttype-of-product-term goal-term))
	(conjunct2 (righttype-of-product-term goal-term)))
       (cond
	 
	 ((not (and (is-int-binary-equality conjunct1)
		    (is-int-binary-equality conjunct2)))
	  (throw 'division-tag
	         '|division: Bad goal.  Both of the conjuncts must be integer binary equality terms.|))
	 
	 (t 
	  (process-div6-goal conjunct1 conjunct2)))))
    
    (t  
     (throw 'division-tag
	    '|division: Bad goal format.|))))






;*****************************************************************
; FUNCTIONS WHICH PROCESS THE GOAL TERM FOR EACH OF THE 
; 6 ACTUAL DIVISION RULES
;****************************************************************






;; This function represents the rule: 
;; 
;;  H >> a = b*(a/b)+(a mod b) in int   By division
;;    1.  (b = 0 in int)->void 
;;    2.  (a < 0) -> void 
 
(defun process-div1-goal (a  mult-term a-mod-b )
  (cond
    ((not  (and
	     (equal-terms a 
			  (leftterm-of-binary-term  a-mod-b))
	     (is-mult-term mult-term)))
     (throw 'division-tag
            '|division:2 |))
    
    (t
     (let* 
       ((b (rightterm-of-binary-term  a-mod-b))
	(left-factor (leftterm-of-binary-term mult-term))
	(right-factor (rightterm-of-binary-term mult-term)))
       
       (cond
	 
	 ((and
	    (is-division-term left-factor)
	    (equal-terms  a
			  (leftterm-of-binary-term left-factor))
	    (equal-terms  b
			  (rightterm-of-binary-term left-factor))
            (equal-terms  b
			  right-factor))
	  (make-div-subgoals 1 (list a b)))
	 
	 
	 ((and
	    (is-division-term right-factor)
	    (equal-terms  a
			  (leftterm-of-binary-term right-factor))
	    (equal-terms  b
			  (rightterm-of-binary-term right-factor))
	    (equal-terms  b
			  left-factor))
	  (make-div-subgoals 1 (list a b)))
	 
	 (t
	  (throw 'division-tag
		 '|division: 2 |)))))))







;; This function represents the rule: 
;; 
;;  H >> a = b*(a/b)-(a mod b) in int   By division
;;    1.  (b = 0 in int)->void 
;;    2.  (0 < a) -> void 
 

(defun process-div2-goal (a  mult-term a-mod-b)
  (cond
    ((not  (and
	     (equal-terms a 
			  (leftterm-of-binary-term  a-mod-b))
	     (is-mult-term mult-term)))
     (throw 'division-tag
            '|division: |))
    
    (t
     (let* 
       ((b (rightterm-of-binary-term  a-mod-b))
	(left-factor (leftterm-of-binary-term mult-term))
	(right-factor (rightterm-of-binary-term mult-term)))
       
       (cond
	 
	 ((and
	    (is-division-term left-factor)
	    (equal-terms  a
			  (leftterm-of-binary-term left-factor))
	    (equal-terms  b
			  (rightterm-of-binary-term left-factor))
            (equal-terms  b
			  right-factor))
	  (make-div-subgoals 2 (list a b)))
	 
	 
	 ((and
	    (is-division-term right-factor)
	    (equal-terms  a
			  (leftterm-of-binary-term right-factor))
	    (equal-terms  b
			  (rightterm-of-binary-term right-factor))
            (equal-terms  b
			  left-factor))
	  (make-div-subgoals 2 (list a b)))
	 
	 (t
	  (throw 'division-tag
		 '|division: |)))))))





;; This function represents the rule: 
;; 
;;  H >> 0 < a/b   By division
;;    1. ((0 < b) # ((a<b) -> void)) | ((b<0) # ((b < a) -> void))
	   
(defun process-div3-goal (a-div-b)
  (let*
    ((a  (leftterm-of-binary-term a-div-b))
     (b  (rightterm-of-binary-term a-div-b)))
    (make-div-subgoals 3 (list a b))))







;; This function represents the rule: 
;; 
;;  H >> a/b < 0   By division
;;     1. ((0 < b) # ((-a < b) -> void) | ((b<0) # ((b < -a) -> void))
	   
(defun process-div4-goal (a-div-b)
  (let*
    ((a  (leftterm-of-binary-term a-div-b))
     (b  (rightterm-of-binary-term a-div-b)))
    (make-div-subgoals 4 (list a b))))







;; This function represents the rule: 
;; 
;;  H >> a/b = 0 in int     By division
;;     1.  (b = 0 in int) -> void 
;;     2.  a = 0 in int 

(defun process-div5-goal (a-div-b)
  (let*
    ((a  (leftterm-of-binary-term a-div-b))
     (b  (rightterm-of-binary-term a-div-b)))
    (make-div-subgoals 5 (list a b))))









;; This function represents the rule: 
;; 
;;  H >> a/b = q in int # a mod b = r in int     By division
;;     1.  (b = 0 in int) -> void
;;     2.  (((a<0)->void)#(a=b*q+r in int)) | ((0<a) -> void)#(a=b*q-r in int)
;;     3.  (r < 0) -> void 
;;     4.  ((0<b)#(r<b)) | ((b<0)#(r < -b)) 
	 
(defun process-div6-goal (con1 con2)
  (let*
    ((e1 (car (terms-of-equal-term con1)))
     (e2 (cadr (terms-of-equal-term con1)))
     (e3 (car (terms-of-equal-term con2)))
     (e4 (cadr (terms-of-equal-term con2))))
    
    (cond
      
      ((and (is-division-term e1)
	    (is-mod-term e3)
	    (let*
	      ((a1 (leftterm-of-binary-term e1))
	       (a2 (leftterm-of-binary-term e3))
	       (b1 (rightterm-of-binary-term e1))
	       (b2 (rightterm-of-binary-term e3)))
	      (and  (equal-terms a1 a2)
		    (equal-terms b1 b2))))
       (make-div-subgoals 6 (list (leftterm-of-binary-term e1)
				  (rightterm-of-binary-term e1)
				  e2
				  e4)))
      
      
      ((and (is-division-term e1)
	    (is-mod-term e4)
	    (let*
	      ((a1 (leftterm-of-binary-term e1))
	       (a2 (leftterm-of-binary-term e4))
	       (b1 (rightterm-of-binary-term e1))
	       (b2 (rightterm-of-binary-term e4)))
	      (and  (equal-terms a1 a2)
		    (equal-terms b1 b2))))
       (make-div-subgoals  6 (list (leftterm-of-binary-term e1)
				   (rightterm-of-binary-term e1)
				   e2
				   e3)))
      
      
      ((and (is-division-term e2)
	    (is-mod-term e3)
	    (let*
	      ((a1 (leftterm-of-binary-term e2))
	       (a2 (leftterm-of-binary-term e3))
	       (b1 (rightterm-of-binary-term e2))
	       (b2 (rightterm-of-binary-term e3)))
	      (and  (equal-terms a1 a2)
		    (equal-terms b1 b2))))
       (make-div-subgoals 6 (list (leftterm-of-binary-term e2)
				  (rightterm-of-binary-term e2)
				  e1
				  e4)))
      
      
      ((and (is-division-term e2)
	    (is-mod-term e4)
	    (let*
	      ((a1 (leftterm-of-binary-term e2))
	       (a2 (leftterm-of-binary-term e4))
	       (b1 (rightterm-of-binary-term e2))
	       (b2 (rightterm-of-binary-term e4)))
	      (and  (equal-terms a1 a2)
		    (equal-terms b1 b2))))
       (make-div-subgoals  6 (list (leftterm-of-binary-term e2)
				   (rightterm-of-binary-term e2)
				   e1
				   e3)))
      
      
      (t  (throw 'division-tag
		 '|division: Goal term has bad format.|)))))






;*****************************************************************
; CONSTANTS : THE PATTERNS FOR THE SUBGOAL CONCLUSIONS WHICH WILL
; BE RETURNED BY EACH OF THE 6 DIVISION RULES
;*****************************************************************

(defvar div1-subgoals)
(defvar div2-subgoals)
(defvar div3-subgoals)
(defvar div4-subgoals)
(defvar div5-subgoals)
(defvar div6-subgoals)

(defun init-division ()
    (setf div1-subgoals
	  (mapcar
	    #'make-prl-term
	    '(| (b = 0 in int)->void | | (a < 0) -> void |)))
    (setf div2-subgoals
	  (mapcar
	    #'make-prl-term
	    '(| (b = 0 in int)->void | | (0 < a) -> void |)))
    (setf div3-subgoals
	  (let*
	    ((t1  (make-prl-term '| (0 < b) # ((a<b) -> void) |))
	     (t2  (make-prl-term '| (b<0) # ((b < a) -> void) |)))
	    (list (union-term 'UNION nil t1 t2))))
    (setf div4-subgoals
	  (let*
	    ((t1  (make-prl-term '| (0 < b) # ((-a < b) -> void) |))
	     (t2  (make-prl-term '| (b<0) # ((b < -a) -> void) |)))
	    (list (union-term 'UNION nil t1 t2))))
    (setf div5-subgoals
	  (mapcar
	    #'make-prl-term
	    '(| (b = 0 in int) -> void | | a = 0 in int |)))
    (setf div6-subgoals
	  (let*
	    ((t1  (make-prl-term '| (b = 0 in int) -> void|))
	     (t21 (make-prl-term '| ((a<0)->void)#(a=b*q+r in int) |)) 
	     (t22 (make-prl-term '| ((0<a) -> void)#(a=b*q-r in int) |))
	     (t3  (make-prl-term '| (r < 0) -> void |))
	     (t41 (make-prl-term '| ((0<b)#(r<b)) |))
	     (t42 (make-prl-term '| (b<0)#(r < -b) |)))
	    (list
	      t1
	      (union-term 'UNION nil t21 t22)
	      t3
	      (union-term 'UNION nil t41 t42)))))




;; Gets subgoal patterns from the lists shown above; then pairs up 
;; the user's terms with variables from the pattern terms, and performs
;; the substitution -- returning the instantiated pattern terms.

(defun make-div-subgoals (choice-num terms)
  (let*
    ((vars  div-pattern-vars)
     (subst-list (pairup vars terms))
     (patterns (get-div-subgoals choice-num)))
    (mapcar
      #'(lambda (pattern) (substitute pattern subst-list))
      patterns)))		      




(defun get-div-subgoals (num)
  (case num
    (1 div1-subgoals)
    (2 div2-subgoals)
    (3 div3-subgoals)
    (4 div4-subgoals)
    (5 div5-subgoals)
    (6 div6-subgoals)
    (t (throw 'division-tag '|division: You #@&*ing idiot!!|))))







