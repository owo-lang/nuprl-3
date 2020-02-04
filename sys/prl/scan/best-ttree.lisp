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


;--        BEST-TTREE.l
;-- 
;-- This file defines a best Ttree computor.
;-- It is constructed by:
;-- 
;--      (BestTtree-create)
;--
;-- It is initially inactive, ie it won't respond to any requests.  To make it
;-- come alive, and initialize it one calls:
;-- 
;--      (activate-BestTtree)
;--  
;-- To make it inactive again, one calls:
;-- 
;--      (deactivate-BestTtree)
;-- 
;-- Normally, it is active only during the parsing of terms.
;-- 
;-- It accepts the following messages with associated meanings:
;-- 
;--      :value value
;--           The value is added to the sequence of remembered values.
;-- 
;--      :enter
;--           Remember the current position in the sequence.
;-- 
;--      :exit value
;--           Replace the elements of the sequence from the closest
;--           unmatched enter to the current position with value.
;-- 
;--      :open
;--           Remember the current position in the sequence.
;-- 
;--      :yield
;--           Return a Ttree whose elements are the values from the closest
;--           unmatched open to the current position.
;-- 
;--      :close
;--           Forget the matching open.
;--
;--      :forget-parens
;--           This is message is sent only when the characters from the
;--           current open on are the characters that parsed to a paren
;--           term.  This attempts to delete the parens from the characters
;--           as they are logically redundant.
;-- 
;-- The messages are sent by calling send-to-best-Ttree on them.
;-- 
;-- The :value, :enter and :exit messages are sent by the Ttree generator.
;-- A matching :enter, :exit pair define the beginning and end of a
;-- definition reference in the Ttree, and the value of an :exit message is
;-- the best Ttree for that definition reference.
;-- The :open and :close-and-yield messages are sent by the parser.  The :open
;-- message is sent at the beginning of parsing a term and the :close-and-yield
;-- message is sent at the end of parsing a term.
;-- 
;-- The action for an :exit cannot always be performed immediately.  If
;-- there is an unmatched :open between the matching :enter and the :exit,
;-- the action for the :action must be delayed until all the intervening
;-- :open's have been matched.  This is because the the best Ttree for the
;-- term corresponding to the :open should contain the values which would be
;-- replaced by the immediate execution of the action for the :exit.
;-- This delay is implemented by giving the closest (to the matching :enter)
;-- unmatched :open a request to perform the associated action when it is 
;-- matched.  Any request already given to that :open can be ignored as the
;-- effect of the current request will wipe out all effect of any previous
;-- request.
;-- 


;-- IMPLEMENTATION
;-- 
;-- We create a Ttree Maintainer to do all the work of storing values and
;-- replacing values.  The outstanding :enter and :open messages are stored
;-- in two stacks, the enter-stack and the open-stack.  The only information
;-- we need to remember for an :enter is (TM-current-index) when the :enter
;-- is sent.  For an :open we must remember the same thing, but we must also
;-- be able to remember a delayed exit action.
;-- 

(defvar BestTtree-active)     ;-- True iff the best Ttree computor should
                              ;-- accept messages.

;-- The variables for remembering :enter's.
(defvar current-enter)            
(defvar enter-stack)


;-- Types and variables for remembering :open's.
(Pdeftype delayed-exit-action
    (left right value)        ;-- The arguments to be passed to TM-replace
)

(Pdeftype open-descriptor
    (TM-index                 ;-- The value of (TM-current-index) when the 
                              ;-- open was sent 
     delayed-action 
         type delayed-exit-action
                              ;-- The delayed action associated with this
                              ;-- open.  A value of -1 in left is used to
                              ;-- indicate that there is no action.
    )
)

(global current-open open-descriptor)
(defvar open-stack)

;-- A couple declarations to make typing easier.
(global desc1 open-descriptor)
(global desc2 open-descriptor)
(global action1 delayed-exit-action)
(global action2 delayed-exit-action)

(defun open-descriptor-update (desc1 desc2)
    ;-- The update function for open descriptors.
        (<- (sel desc1 TM-index) (sel desc2 TM-index))
        (Plet (action1 (sel desc1 delayed-action)
              action2 (sel desc2 delayed-action)
             )
            (<- (sel action1 left) (sel action2 left))
            (<- (sel action1 right) (sel action2 right))
            (<- (sel action1 value) (sel action2 value))
        )
        desc1
)

(constant TM-init-size 500)
(constant enter-stack-init-size 50)
(constant open-stack-init-size 100)

(defun BestTtree-create ()
    (TM-create TM-init-size)
    (<- enter-stack
        (make-stack
            enter-stack-init-size
            #'(lambda () 0)
            #'(lambda (x y) x y)
        )
    )
    (<- open-stack
        (make-stack
            open-stack-init-size
            #'(lambda () (new open-descriptor))
            #'open-descriptor-update
        )
    )
    (<- current-open (new open-descriptor))
)

(defun activate-BestTtree ()
    (<- BestTtree-active t)
    (TM-init)
    (make-empty-stack enter-stack)
    (make-empty-stack open-stack)
    (<- (sel current-open TM-index) -1)
    (<- current-enter -1)
)

(defun deactivate-BestTtree ()
    (<- BestTtree-active nil)
)

(defun send-to-best-Ttree (kind &optional value)
     (Pif BestTtree-active -->
         (case kind
            (:value    (TM-add-value value))
            (:enter
                (stack-push enter-stack current-enter)
                (<- current-enter (TM-current-index))
            )
            (:exit
                (Pif (>= current-enter (sel current-open TM-index)) -->
                    ;-- The enter is within the scope of the most recent
                    ;-- open so we can execute the action for the :exit
                    ;-- right away.
                    (TM-replace current-enter (TM-current-index) value)
                 || t -->
                    ;-- The action must be stored away on the open closest
                    ;-- to the matching enter.
                        (Plet (desc1 (get-closest-enclosed-open current-enter))
                            (Plet (action1 (sel desc1 delayed-action))
                                (<- (sel action1 left) current-enter)
                                (<- (sel action1 right) (TM-current-index))
                                (<- (sel action1 value) value)
                            )
                        )
                 fi)
                (<- current-enter (stack-pop enter-stack))
            )
            (:open
                (stack-push open-stack current-open)
                (<- (sel current-open TM-index) (TM-current-index))
                (<- (sel current-open delayed-action left) -1)
            )
            (:close
                (check-delayed-action)
                (open-descriptor-update current-open (stack-pop open-stack))
            )
            (:yield
                (check-delayed-action)
                (TM-make-Ttree (sel current-open TM-index))
            )
	    (:forget-parens
	        (multiple-value-bind
		  (done left right) (TM-forget-parens (sel current-open TM-index))
		  (Pif done --> (update-delayed-actions left right) fi))
	    )
        )
     fi)
)

(defun get-closest-enclosed-open (enter-index)
    (Ploop
        (local
            i       0
            desc1   (ith-element open-stack 0)
        )
        (while (< enter-index (sel desc1 TM-index)))
        (do
            (<- i (1+ i))
            (<- desc1 (ith-element open-stack i))
        )
        (result
            (Pif (= i 0) --> desc1
             || t --> (ith-element open-stack (1- i))
             fi)
        )
    )
)


(defun check-delayed-action ()
    (Plet (action1 (sel current-open delayed-action))
        (Pif (and
                (>= (sel action1 left) 0)
                (>= (sel action1 left) (sel current-open TM-index))
            ) -->
            (TM-replace (sel action1 left) (sel action1 right) (sel action1 value))
            (<- (sel action1 left) -1)
         fi)
    )
)

(defun update-delayed-actions (left right)
  (update-delayed-action current-open left right)
  (dotimes (i (current-size open-stack))
    (update-delayed-action (ith-element open-stack i) left right)))

(defun update-delayed-action (open left right)
    (Plet (action1 (sel (open-descriptor open) delayed-action))
       (Pif (> (sel action1 left) -1) -->
	   (Pif (< right (sel action1 right)) -->
	      (<- (sel action1 right) (- *-* 2))
	      (Pif (< right (sel action1 left)) -->
		  (<- (sel action1 left) (- *-* 2))
	       || (< left (sel action1 left)) -->
	          (<- (sel action1 left) (1- *-*))
	       fi)
	    || (< left (sel action1 right)) -->
	       (<- (sel action1 right) (1- *-*))
	       (Pif (< left (sel action1 left)) -->
		   (<- (sel action1 left) (1- *-*))
	        fi)
	    fi)
	fi)))
