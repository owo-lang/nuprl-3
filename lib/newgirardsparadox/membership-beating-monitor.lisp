;;; -*- Package: NUPRL; Mode: LISP; Syntax: Zetalisp -*-

(defun membership-beating-status ()
  (terpri)
  (mapc #'(lambda (x) (terpri) (princ (car x)) (princ (cdr x)))
	`(("Total number of membership goals: " . ,(length (get-ml-value '|postponed_membership_goals|)))
	  ("Number of membership goals processed: " . ,(1- (get-ml-value '|goal_index|)))
	  ("Number of completed proofs: " . ,(length (get-ml-value '|completed_proofs|)))
	  ("Number of partial proofs: " . ,(length (get-ml-value '|partial_results|)))))
  (terpri)
  t)