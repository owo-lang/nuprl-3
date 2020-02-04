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


;--     TTREE-MAINT.L
;-- 
;-- Defines a Ttree Maintainer (TM).  The constructor is:
;-- 
;--     (TM-create size)
;-- 
;-- The operations are:
;-- 
;--     (TM-init)
;--         Initializes the ttree maintainer.
;-- 
;--     (TM-add-value val)
;--         Adds the value val to the sequence of things being remembered.
;-- 
;--     (TM-current-index)
;--         Returns the index of the spot where the next value will be added.
;-- 
;--     (TM-replace left right new)
;--         Replace the values in left .. right-1 with the value new.
;-- 
;--     (TM-make-Ttree left)
;--         Returns a Ttree whose elements are the significant values from
;--         left on.  We ignore surrounding white space and matching parentheses.
;--
;--     (TM-forget-parens left)
;--         Called only when the values from left on parse to a paren term.  If
;--         the parens are visible ie they aren't hidden inside a definition, they
;--         are removed, and as multiple values t and the indices of the parens are
;--         returned.  If it isn't possible to remove the parens, nil is returned.
;-- 

;-- IMPLEMENTATION
;-- 
;-- The values are stored in an extensible vector (as defined in evector.l).
;-- Things are complicated slightly because we want to be able to check if two
;-- parens are matching. Let the level of a string be the number of ('s minus
;-- the number of )'s, and the excess of a string be the min of the level's of
;-- the initial prefixes of the string.  Then two parens are matching if only if
;-- the excess of the string between them is nonnegative.  To extend this to deal
;-- with defs, we store for each value corresponding to a def the level and excess
;-- of the right hand side of the def.  Knowing these, we can compute the excess
;-- of any string containing a def.


(defvar   TM-values)             ;-- The vector in which values are stored.
(defvar   TM-next)               ;-- The index of spot where next value
                                 ;-- should be added.
(defvar   TM-pinfo)		 ;-- If TM-values(i) is a def, TM-pinfo(i) is a
                                 ;-- pair containing the level and excess of the
                                 ;-- right hand side of the def.

(defun TM-create (size)
    (<- TM-values (new-evec size))
    (<- TM-pinfo (new-evec size))
)

(defun TM-init ()
    (<- TM-next 0)
)

(defun TM-add-value (val)
    (<- (evec-ref TM-values TM-next) val)
    ;; Force TM-pinfo to have the same size as TM-values.
    (<- (evec-ref TM-pinfo TM-next) nil)
    (<- TM-next (1+ TM-next))
)

(defun TM-current-index ()
    TM-next
)

(defun TM-replace (left right new)
    (<- (evec-ref TM-pinfo left) (build-pinfo left right))
    (<- (evec-ref TM-values left) new)
    (TM-shift right TM-next (1+ left))
    (<- TM-next (- TM-next (- right left 1)))
)

(declaim (special white-space))

(defun is-left (x) (equal x #.(ichar #\()))
(defun is-right (x) (equal x #.(ichar #\))))
(defun is-whitespace (x) (member x white-space))

(defun TM-make-Ttree (left)
    (build-ttree left (1- TM-next)))

(defun build-ttree (left right)
    ;; Skip over surrounding white space.
    (Ploop
      (while (is-whitespace (evec-ref TM-values left)))
      (do (<- left (1+ left))))
    (Ploop
      (while (is-whitespace (evec-ref TM-values right)))
      (do (<- right (1- right))))
    
    (Pif (and
	  (is-left (evec-ref TM-values left))
	  (is-right (evec-ref TM-values right))
	  (are-matching-parens left right)) -->
	;; Forget matching parens.
	(build-ttree (1+ left) (1- right))

     || t -->
        ;; Make a Ttree of the elements from left up
        ;; through right.
        (let* ((list (make-list (+ 2 (- right left)))))
	  (<- (car list) 'Ttree)
	  (Ploop
	    (local l (cdr list) i left)
	    (while l)
	    (do
	      (<- (car l) (evec-ref TM-values i))
	      (<- l (cdr l))
	      (<- i (1+ i)))
	    (result list)))
     fi))

(defun are-matching-parens (left right)
    (let* ((level 1))
      (<- left (1+ left))
      (Ploop
	(while (< left right))
	(do
	  (let* ((v (evec-ref TM-values left)))
	    (Pif (numberp v) -->
		(Pif (is-left v) --> (<- level (1+ level))
		 || (is-right v) -->
		    (<- level (1- level))
		    (Pif (zerop level) --> (return nil) fi)
		 fi)
	     || t -->
	        (let* ((tmpv  (evec-ref TM-pinfo left))
		       (l (car tmpv))
		       (excess (cdr tmpv)))
		  (Pif (zerop (+ level excess)) -->
		      (return nil)
		   || (< (+ level excess) 0) -->
		      (parse-error '|bad paren nesting in term|)
		   fi)
		  (<- level (+ level l)))
	     fi))
	  (<- left (1+ left)))
	(result t))))

(defun build-pinfo (left right)
    ;; The values from left up to right are the values
    ;; for the right hand side of a def.  Compute and
    ;; return the level and excess.
    (let* ((level 0)
	   (excess 0))
      (Ploop
	(local i left)
	(while (< i right))
	(do
	  (let* ((v (evec-ref TM-values i)))
	    (Pif (numberp v) -->
		(Pif (is-left v) --> (<- level (1+ level))
		 || (is-right v) -->
		    (<- level (1- level))
		    (<- excess (min excess level))
		 fi)
	     || t -->
	        (let* ((tmpv (evec-ref TM-pinfo i))
		       (l (car tmpv))
		       (ex (cdr tmpv)))
		  (<- excess (min excess (+ level ex)))
		  (<- level (+ level l)))
	     fi))
	  (<- i (1+ i)))
	(result (cons level excess)))))

(defun TM-forget-parens (beginning)
    (let* ((left
	     (Ploop
	       (local i beginning)
	       (while (is-whitespace (evec-ref TM-values i)))
	       (do (<- i (1+ i)))
	       (result i)))
	   (right
	     (Ploop
	       (local i (1- TM-next))
	       (while (is-whitespace (evec-ref TM-values i)))
	       (do (<- i (1- i)))
	       (result i))))
      (Pif (and
	    (is-left (evec-ref TM-values left))
	    (is-right (evec-ref TM-values right))
	  ) -->
	  (TM-shift (1+ left) right left)
	  (TM-shift (1+ right) TM-next (1- right))
	  (<- TM-next (- TM-next 2))
	  (values t left right)
       || t -->
          (values nil)
       fi)))

(defun TM-shift (left right beginning)
    ;-- Shift the values in left .. right-1 so that they now begin at
    ;-- position beginning.
        (Pif (not (equal left beginning)) -->
            (Pif (> left beginning) -->
                (Ploop
                    (local from left to beginning)
                    (while (< from right))
                    (do
                        (<- (evec-ref TM-values to) (evec-ref TM-values from))
			(<- (evec-ref TM-pinfo to) (evec-ref TM-pinfo from))
                        (<- from (1+ from))
                        (<- to (1+ to))
                    )
                )
             || t -->
                (Ploop
                    (local from (1- right) to beginning)
                    (while (>= from left))
                    (do
                        (<- (evec-ref TM-values to) (evec-ref TM-values from))
			(<- (evec-ref TM-pinfo to) (evec-ref TM-pinfo from))
                        (<- from (1- from))
                        (<- to (1- to))
                    )
                )
             fi)
         fi)
)
