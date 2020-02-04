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

;--     TTREE-GEN.L
;-- 
;-- This file provides a method of successively producing each character in
;-- the expansion of a Ttree.  The expansion of a Ttree is simply the Ttree
;-- resulting when all definition references are expanded out.  Besides
;-- supplying the characters on demand, it also sends some information to
;-- the best Ttree computor.  Every time a character is supplied, it is also
;-- sent to the best Ttree computor.  Whenever a definition reference is
;-- starting to be expanded, notification is sent, and when the definition
;-- reference is completely expanded, the definition reference itself is
;-- sent.  
;-- 
;-- The Ttree generator is created by calling
;-- 
;--     (TG-create)
;-- 
;-- To initialize the generator for a given Ttree, one calls
;-- 
;--     (TG-init Ttree)
;-- 
;-- and to obtain the next character one calls
;-- 
;--     (TG-next-char)
;-- 
;-- 

;-- IMPLEMENTATION
;-- 
;-- We keep a stack of generators, each responsible for generating one level
;-- of a Ttree.  

(defun make-ttree-generator (ttree ttree-env)
  #'(lambda ()
      (if (null ttree)
	  (values ':done)
	  (let ((val (pop ttree))) 
            (cond ((not (consp val))
		   (if (and (null ttree) (= val NL))
		       (values ':done)
		       (progn
			 (add-to-action-buffer val)
			 (values ':value val))))
		  ((eql (car val) 'FORMAL)
		   (multiple-value-bind (new-Ttree new-env)
		       (lookup-formal (cadr val) ttree-env)
		     (values ':handle-Ttree new-Ttree new-env)))
		  (t (values ':handle-def-ref val ttree-env)))))))


(defun make-def-generator (def ttree-env &aux (first-time t))
  #'(lambda ()
      (if first-time
	  (let ((def-object (get-def-object (car def))))
	    (<- first-time nil)
	    (add-to-action-buffer 'ENTER)
	    (values
                ':handle-Ttree
                (sel (definition-object def-object) rhs)
                (get-new-env
                    (cdr def)
                    (get-formal-names (car def) def-object)
                    ttree-env)))
	  (progn
	    (add-to-action-buffer (replace-formals-with-actuals def ttree-env))
	    (values ':done)))))

;-- Variables to remember generators.
(defvar generator-stack)
(defvar current-generator)

(constant stack-init-size 200)

(defun TG-create ()
    (<- generator-stack
	(make-stack stack-init-size #'(lambda () nil) #'(lambda (x y) x y))))

(defun TG-init (Ttree)
    ;; Initializations for a given Ttree.
    (make-empty-stack generator-stack)
    (<- current-generator
	(make-ttree-generator (cdr Ttree) nil)))

;-- Forget the rest of the input and return eof on the next call of TG-next-char.
;-- This is a hack.
(defun flush-scanner-input ()
    ;; Forget the rest of the input and return eof on the next call of TG-next-char.
    ;; This is a hack.
    (<- current-generator nil))


(defun TG-next-char ()
  ;; Return the next character in the expanded form of a ttree.  As a side effect,
  ;; information is sent to the best ttree generator.
  (prog ()
     tryagain
	(when (null current-generator) (return nil))
	(multiple-value-bind (result val1 val2)
	    (funcall current-generator)
	  (case result
	    (:value
	     (return val1))
	    (:done
	     (setf current-generator (stack-pop generator-stack)))
	    (:handle-Ttree
	     (stack-push generator-stack current-generator)
	     (setf current-generator
		   (make-ttree-generator (cdr val1) val2)))
	    (:handle-def-ref
	     (stack-push generator-stack current-generator)
	     (setf current-generator
		   (make-def-generator val1 val2)))))
	(go tryagain)))

;; Environments are a list of environment entries.  An environment entry is
;; an assoc list of name, Ttree pairs.

(defun lookup-formal (id env)
  (values (cdr (assoc id (car env))) (cdr env)))

(defun get-new-env (actuals names oldenv)
  (cons (mapcar
	  #'(lambda (x y) (cons x y))
	  names
	  actuals)
	oldenv))

(defun get-def-object (name)
  ;; Return the definition object associated with name.
  (when (not (lib-member name))
    (scan-error "definition not in library: " name))
  (let ((object (library-object name)))
    (sel (object object) value)))



;(defun get-formal-names (name object)
;  (let ((result (get name 'formal-names)))
;    (if result
;	result
;	(<- (get name 'formal-names) (get-names object)))))


;;; Reason for change: I don't have the time to find out how property
;;; lists are used by the parser-ttree crap, so I've made a patch here
;;; to bypass property lists.  The problem was that the state-changing
;;; code (in prl.lisp) doesn't account for any such use of plists.   
;;;   - Doug
(defun get-formal-names (name object)
  (<- (get name 'formal-names) (get-names object)))
	      
(defun get-names (def-object)
  (let ((num-formals (sel (definition-object def-object) num-formals)))
    (do ((i num-formals (1- i))
	 (answer nil (cons
		       (implode
			 (sel (definition-object def-object) formal (i) name))
		       answer)))
	((zerop i) answer))))

(defun replace-formals-with-actuals (def-ref env)
  ;; Recursively replace all formals with actuals in the actuals of the given
  ;; definition reference and return the result.  The result if fully cdr-coded on
  ;; the Lisp Machine.
  (let* ((result (make-list (length def-ref)))
	 (r (cdr result)))
    (<- (car result) (name-of-def-ref def-ref))
    (dolist (actual (actuals-of-def-ref def-ref))
      (setf (car r) (make-cdr-coded (rwfa-Ttree actual env)))
      (setf r (cdr r)))
    result))

;-- Handle a Ttree.  Since we do nconc's and nreverse's on these lists we don't cdr code
;-- them here, but leave it up to replace-formals-with-actuals to do that.
;-- 
(defun rwfa-Ttree (Ttree env)
  ;; Handle a Ttree.  Since we do nconcs and nreverses on these lists we don't cdr
  ;; code them here but leave that up to replace-formals-with-actuals.
  (do ((answer nil)
       (Ttree Ttree (cdr Ttree)))
      ((null Ttree) (nreverse answer))
    (cond ((not (consp (car Ttree)))
	   (push (car Ttree) answer))
          ((eql (caar Ttree) 'FORMAL)
	   (<- answer
	       (nconc
		 (nreverse
		   (multiple-value-bind (new-tree new-env)
		       (lookup-formal (cadar Ttree) env)
		     (cdr (rwfa-Ttree new-tree new-env))))
		 answer)))
	  (t (push (replace-formals-with-actuals (car Ttree) env) answer)))))

            
          
