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


;-- Much of the Prl side of the interface to ML is here.  ML also uses
;-- rule-to-Ttree, term-to-Ttree.

;--
;-- refine-tactic 
;--
;--     Do work of refine for TACTIC reference rule.
;--                                 
;--     Use the tactic indicated by the rule-body of pt to refine pt.
;--

(defun refine-tactic ()


    (Plet (
             pt
             (proof-tree
                 ref-assums ref-concl ref-rule-body nil nil nil ref-hidden
             )
             original-pt       ;-- pt gets destructively changed
             (proof-tree
                 ref-assums ref-concl ref-rule-body nil nil nil ref-hidden
             )
             tactic-body (tactic-body-of-tactic-rule ref-rule)
         )

        ;-- Set the rule back to what it "really" should be.  This must be
        ;-- here as otherwise checking progress of tactics gets screwed.
            (<- ref-rule nil)

        (Plet (
                 result-proof
                 (do-tactic
                     pt
                     tactic-body
		     #'(lambda (message)
			 (ref-error (implode message))
                         )
		     )
		 )
            (Pif (and
                    result-proof
                    (made-progress result-proof original-pt)
                ) -->
                (<- ref-rule (tactic-rule 'TACTIC tactic-body result-proof))
                (<- ref-children
                    (mapcan
                        #'unproved-leaves$
                        (children-of-proof-tree result-proof)
                    )
                )

             || t -->
                (<- ref-rule nil)
                (<- ref-children nil)
                (ref-error '|Tactic made no progress|)
             fi)
        )
    )
)

(defun made-progress (tactic-result original)
    ;-- 
    ;-- True iff the tactic made any progress towards the goal.
    ;--
        (not
            (and
                (eq
                    (rule-body-of-proof-tree tactic-result)
                    (rule-body-of-proof-tree original)
                )
                (eq
                    (rule-of-proof-tree tactic-result)
                    (rule-of-proof-tree original)
                )
                (eq
                    (children-of-proof-tree tactic-result)
                    (children-of-proof-tree original)
                )
            )
        )
)



(defun do-tactic (proof tactic err-fnc)
    ;-- 
    ;-- The PRL side of the tactic interface.  (The ml system side being
    ;-- apply-tactic).  Invokes apply-tactic and checks the result.  If
    ;-- everything is okay, the proof top is returned.  Otherwise the given
    ;-- error function is called with a prl-string describing the situation
    ;-- as an argument, and nil is returned (if the error function returns).
    ;--
        (Plet (original-pt
                 (proof-tree
                     (assumptions-of-proof-tree proof)
                     (conclusion-of-proof-tree proof)
                     (rule-body-of-proof-tree proof)
                     (rule-of-proof-tree proof)
                     (children-of-proof-tree proof)
                     (status-of-proof-tree proof)
                     (hidden-of-proof-tree proof)
                 )
             )
            (Plet (tactic-result (apply-tactic proof tactic))
                
                (Pif (eql (car tactic-result) 'SUCCESS) --> 
                    (Pif (equal-sequent (cdr tactic-result) original-pt) -->
                        
                        (cdr tactic-result)

                        
                     || t -->
                        
                        (funcall
                            err-fnc
                            (append
                                '#.(istring "tactic has returned with ")
                                '#.(istring "goal other than original goal")
                            )
                        )
                        nil
                     fi)
                    
                 || (eql (car tactic-result) 'FAILURE) -->       
		    (funcall
		      err-fnc
		      (compact-message (cdr tactic-result))
		    )
		    nil
                        
                   || t -->
                      
                      (funcall
                          err-fnc
                          (compact-message
			    (append
                              '#.(istring "[internal ML error!] ")
                              (istring (cdr tactic-result))
			    )
                          )
                      )
                      nil
                 fi)
            )
        )
)


;-- Compact message ruturned by ML.
;-- delete leading CR and trailing CR  and change
;-- others to ' / '
(defun compact-message (message)
  (mapcon
   #'(lambda (c)
        (Pif (null c) -->
            nil
         || (equal c (list CR)) -->
            nil
         || (equal (car c) CR) -->
            (copy '#.(istring " / "))
            ;;;NEXT LINE IS TEMPORARY (circa 3/83)
         || (equal (car c) LF) --> nil
         || t -->
            (list (car c))
        fi)
      )
    message
  )
)

;-- Ttree-to-list (Ttree)
;-- 
;-- Takes a Ttree and returns a list which is the "best display form" for
;-- the Ttree.  That is, all definition references are expanded out using
;-- the left hand side.  Note that there is no initial 'Ttree in the
;-- returned list.
;-- 
(defun Ttree-to-list (arg-ttree)
    (Ploop
        (local
            answer nil
            Ttree  (cdr arg-ttree)
        )
        (while Ttree)
        (do
            (Pif (not (consp (car Ttree))) -->
                (<- answer (cons (car Ttree) answer))
             || t -->
                (<- answer
                    (nconc
                        (def-ref-to-list (car Ttree))
                        answer
                    )
                )
             fi)
            (<- Ttree (cdr Ttree))
        )
        (result (nreverse answer))
    )
)

(defun def-ref-to-list (def-ref)
    (Plet (obj-name (car def-ref)
          actuals  (cdr def-ref)
         )
        (Pif (lib-member obj-name) -->
            (Plet (obj (library-object obj-name))
                (Pif (and (eql 'COMPLETE (sel (object obj) status))
                         (eql 'DEF (sel (object obj) kind))
                    ) -->
                    (def-ref-to-list$ (sel (object obj) value) actuals)
                 || t -->
                    (bad-def-to-list obj-name actuals)
                 fi)
            )
         || t -->
            (bad-def-to-list obj-name actuals)
         fi)
    )
)

(defun def-ref-to-list$ (def-obj actuals)
    (Plet (num-formals (sel (definition-object def-obj) num-formals))
        (Ploop
            (local
                i      1
                result (reverse (sel (definition-object def-obj) lhs-text (0)))
            )
            (while (<= i num-formals))
            (do
                (<- result
                    (nconc
                        (reverse
                            (sel (definition-object def-obj) lhs-text (i))
                        )
                        (nconc
                            (nreverse (Ttree-to-list (car actuals)))
                            result
                        )
                    )
                )
                (<- i (1+ i))
                (<- actuals (cdr actuals))
            )
            (result result)
        )
    )
)

(defun bad-def-to-list (name actuals)
    (nreverse
        (nconc
            (istring name)
            (cons
                (ichar #\space)
                (mapcan 'Ttree-to-list actuals)
            )
        )
    )
)



;-- Refine-experimental.
;--
;--     Use ML code to implement an experimental rule.
;--                                 
;--     Use the tactic indicated by the rule-body of pt to call experimental
;--     rule encoded by ML function.
;--

(defun refine-experimental ()

    (Plet (   pt
             (proof-tree
                 ref-assums ref-concl ref-rule-body ref-rule nil nil ref-hidden
             )
	  )
	  (Plet (
            result-of-calculation
	    (do-subgoal-calculation
	      pt
              (subgoal-calculation-of-experimental-rule ref-rule)
	    )
	   )
	  (<- ref-children (sequents-to-proofs result-of-calculation))
        )
     )
)


;-- Convert the sequents (declaration lists cross term) into proofs to
;-- be the subgoals of the refinement.  These children inherit the ref-hidden
;-- field from the parent.  Note the use of prl-term to coerce conclusion back
;-- from ml representation of terms.

(defun sequents-to-proofs (seq-list)
    (mapcar
     #'(lambda (s)
	 (proof-tree (car s) (cdr (prl-term s)) (list 'Ttree) nil nil 'INCOMPLETE ref-hidden)
	 )
      seq-list
    )
)

(defun do-subgoal-calculation (proof subgoal-function)
    (Plet (result
	   (apply-subgoal-calculation proof subgoal-function) ;-- ML side of interface
	 )
	 (Pif (eql (car result) 'SUCCESS) --> (cdr result)
	    
           || (eql (car result) 'FAILURE) -->       
	         (ref-error (implode
			      (compact-message 
                                (cdr result)
			      )
			    )
                 )
	       
                        
           || t -->
               (ref-error
		 (implode
		   (compact-message
		     (append
		       '#.(istring "[internal ML error!] ")
		       (istring (cdr result))
		     )
		   ) 
		 )
	       )
           fi)

     )
)

