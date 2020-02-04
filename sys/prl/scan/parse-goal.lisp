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


(defun goal-body-to-proof-tree (Tt)

;;;;;;;;;WHAT ABOUT REFERENCES OF Tt?  KEEP THEM?  INTERACTION WITH CHECKING?

    (Plet (proof-tree nil    ;-- result proof-tree of parsing goal, or
                            ;--   (ERR message .. ..) if an error occurred
         )

        (<- proof-tree (catch 'process-err (parse-goal Tt)))
        (Pif (eql (car proof-tree) 'ERR) -->
            (display-message (append '#.(istring "Error in Main Goal: ")
                                     (istring (cadr proof-tree))
                             )
            )
            nil

         || t -->
            proof-tree

         fi)

    )
)


(defun parse-goal (Tt)

    (Plet (refd-defs nil     ;-- DEFinitions referenced from Tt
          assums    nil     ;-- Assumptions parsed from Tt
          concl     nil     ;-- Conclusion parsed from Tt
         )

        (<- refd-defs (scan-init Tt))

;-- no assumptions allowed              
;        ;-- process the assumptions: a list of comma separated terms
;            (Plet (assum nil         ;-- next assumption to add to assum-list
;                  assum-num  0      ;-- number of assum-form (1 is first assum)
;                 )
;
;                (Pif (not (equal (next-token) TGreater)) -->
;                    (<- assum (parse-declaration))
;                    (<- assum-num 1)
;                    (Pif (not (all-free-vars-declared (type-of-declaration assum) 
;                                                      assums
;                             )
;                        ) -->
;                       (goal-error$ (concat '|not all free vars in assumption|
;                                             assum-num '|have been declared|
;                                    )
;                        )
;                     fi)
;                    (<- assums (list assum))
;                    (Ploop
;                        (while (equal (next-token) TComma))
;                        (do
;                            (scan)                          
;                           (<- assum (parse-declaration))
;                            (<- assum-num (add1 *-*))
;                            (Pif (not (all-free-vars-declared 
;                                                    (type-of-declaration assum)
;                                                     assums
;                                     )
;                                ) -->
;                                (goal-error$ 
;                                      (concat '|not all free vars in assumption|
;                                              assum-num '|have been declared|
;                                      )
;                                )
;                             fi)
;                            (<- assums (append *-* (list assum)))
;                        )
;                    )
;                 fi)
;            )
;
        (scan)
        ;-- process the conclusion: >> formula
            (Pif (eql token-type TGreater) -->
                (scan)
                (Pif (eql token-type TGreater) -->
                    (scan)
                    (<- concl (parse-from-current-Ttree))              
                 || t -->
                    (goal-error$ '|missing '>>' in goal.|)
                 fi)

             || t -->
                (goal-error$ '|missing '>>' in goal.|)

             fi)

        (Pif (not (equal token-type TEndInput)) -->
            (goal-error$ '|unrecognized text beyond end of goal.|)
         fi)

        (Plet (undeclared-vars (free-vars-not-declared concl assums))
            (Pif undeclared-vars -->
                (goal-error$
                    (concat
                        '|Vars not declared in assumptions: |
                        (good-print-name undeclared-vars)
                    )
                )
             fi)
        )

        (proof-tree
            assums
            concl
            (copy raw-object-Ttree)
            nil
            nil
            'INCOMPLETE
            nil
        )
   )
)


(defun get-declared-vars (assums)
    (mapcar #'(lambda (assum) (id-of-declaration assum))
            assums
    )
)

(defun free-vars-not-declared (term assum-list)
    (Plet (declared-vars (get-declared-vars assum-list))
        (prl-set-difference (free-vars term) (list-to-set declared-vars))
    )
)

(defun all-free-vars-declared (term assums)
    (null (free-vars-not-declared term assums))
)

(defun good-print-name (vars)
  (intern
    (apply #'concatenate
	   (cons 'string
	   (mapcon
	     #'(lambda (tail)
		 (if (null (cdr tail))
		     (list (symbol-name (car tail)))
		     (list (symbol-name (car tail)) ", ")))
	     vars)))
    (find-package 'nuprl)))

;--
;-- goal-error$ (text:atom)
;--
;--     Throw a process-err from the goal parser with result
;--     (ERR  text)
;--

(defun goal-error$ (text)

    (throw 'process-err (list 'ERR text))

)
