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


(defun refine-eq-intro-axiom-equal ()
    (check-concl$ 'AXIOM 'EQUAL)
    (<- ref-children (list (make-child
                               ref-assums
                               (type-of-equal-term ref-concl)
                           )
                     )
    )
    nil
)                     

(defun refine-eq-intro-equal ()       
    (Plet (term-list-list nil)
        (check-concl$ 'EQUAL 'UNIVERSE)
        (<- ref-children 
            (list (make-child 
                      ref-assums
                      (equal-term
                          'EQUAL
                          nil
                          (type-of-equal-term ref-concl)
                          (mapcar #'type-of-equal-term
                                  (terms-of-equal-term ref-concl)
                          )
                      )
                  )
            )
        )                                                              
        (<- term-list-list (mapcar #'terms-of-equal-term
                                   (terms-of-equal-term ref-concl)
                           )
        )
        (Pif (not (apply 'n-equal 
                        (list (mapcar #'length term-list-list))
                 )
            ) -->
            (ref-error '|all equal-term term-lists must have equal lengths |)
         fi)                                                               
        (Ploop (local i (length (car term-list-list)))
              (while (plusp i))
              (do                                 
                 (<- ref-children
                     (append 
                       ref-children 
                       (list
                        (make-child
                            ref-assums 
                            (equal-term 
                                'EQUAL
                                nil
                                (type-of-equal-term 
                                     (car (terms-of-equal-term ref-concl))
                                )
                                (mapcar #'car term-list-list)
                            )
                        )
                       )
                     )
                 )
                 (<- term-list-list (mapcar #'cdr
                                            term-list-list
                                    )
                 )
                 (<- i (1- i))                                                  
              )
        )
    )
    nil
)

(defun refine-eq-intro-less ()
    (check-concl$ 'LESS 'UNIVERSE)
    (<- ref-children
        (list (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (int-term 'INT nil)
                        (mapcar #'leftterm-of-less-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
              (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (int-term 'INT nil)
                        (mapcar #'rightterm-of-less-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
        )
    )
    nil
)

(defun refine-eq-intro-axiom-less ()
    (check-concl$ 'AXIOM 'LESS)
    (<- ref-children (list (make-child
                               ref-assums
                               (type-of-equal-term ref-concl)
                           )
                     )
    )
    nil
)

(defun refine-eq-intro-bin-op ()
    (Pif (eql (kind-of-rule ref-rule) 'EQUAL-INTRO-ADD) -->
        (check-concl$ 'ADD 'INT)
     || (eql (kind-of-rule ref-rule) 'EQUAL-INTRO-SUB) -->
        (check-concl$ 'SUB 'INT)
     || (eql (kind-of-rule ref-rule) 'EQUAL-INTRO-MUL) -->
        (check-concl$ 'MUL 'INT)
     || (eql (kind-of-rule ref-rule) 'EQUAL-INTRO-DIV) -->
        (check-concl$ 'DIV 'INT)
     || (eql (kind-of-rule ref-rule) 'EQUAL-INTRO-MOD) -->
        (check-concl$ 'MOD 'INT)
     fi)
    (<- ref-children
        (list (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (int-term 'INT nil)
                        (mapcar #'leftterm-of-binary-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
              (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (int-term 'INT nil)
                        (mapcar #'rightterm-of-binary-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
        )
    )
    nil
)

(defun refine-eq-intro-void ()
    (check-concl$ 'VOID 'UNIVERSE)
    nil
)      

(defun refine-eq-intro-any ()
    (check-concl-kind$)
    (check-terms-kind$ 'ANY)
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (void-term 'VOID nil)
                                    (mapcar
                                            #'term-of-any-term
                                            (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                     )
    )
    nil
)      
       
(defun refine-eq-intro-atom ()
    (check-concl$ 'ATOM 'UNIVERSE)
    nil
)

(defun refine-eq-intro-token ()
    (check-concl$ 'TOKEN 'ATOM)
    (Pif (not (apply 'n-equal (list (mapcar #'atom-of-token-term
                                           (terms-of-equal-term ref-concl)
                                   )
                             )
             )
        ) -->
        (ref-error '|not all of the token terms are equal |)
     fi)
    nil
)

(defun refine-eq-intro-object ()
    (check-concl$ 'OBJECT 'UNIVERSE)
    nil)
    

(defun refine-eq-intro-int ()
    (check-concl$ 'INT 'UNIVERSE)
    nil
)      

(defun refine-eq-intro-ind ()
    (Plet (new-id1 nil
          new-id2 nil
          new-id-list nil
          over-id nil
          over-term nil
          new-assum1 nil                                  
          value      (value-of-ind-term (car (terms-of-equal-term ref-concl)))
          add1-term  nil
          sub1-term  nil
         )
        (check-concl-kind$)
        (check-terms-kind$ 'IND)
        (<- new-id-list
            (Pif (null (new-ids-of-equal-intro-rule-over ref-rule)) -->
                (bound-ids-of-bound-id-term 
                    (downterm-of-ind-term (car (terms-of-equal-term ref-concl)))
                )
             || t -->
                (new-ids-of-equal-intro-rule-over ref-rule)
             fi)
         )
        (Pif (null (over-pair-of-equal-intro-rule-over ref-rule)) -->
            (<- over-term (type-of-equal-term ref-concl))
         || t -->
            (<- over-id (car (over-pair-of-equal-intro-rule-over ref-rule)))
            (<- over-term (cdr (over-pair-of-equal-intro-rule-over ref-rule)))
            (Pif (not (equal-terms (type-of-equal-term ref-concl)
                                  (substitute over-term 
                                              (list (list over-id value))
                                  )
                     )
                ) -->
                (ref-error (concat '|the type of the equal term doesn't |
                                   '|properly match the term after 'over' |
                            )
                )
             fi)
         fi)
        (check-if-all-new$ new-id-list ref-assums)
        (<- new-id1 (car new-id-list))
        (<- add1-term (binary-term 'ADD nil (var-term 'VAR nil new-id1)
                                            (pos-number-term 'POS-NUMBER nil 1)
                      )
        )
        (<- sub1-term (binary-term 'SUB nil (var-term 'VAR nil new-id1)
                                         (pos-number-term 'POS-NUMBER nil 1)
                      )
        )
        (<- new-id2 (cadr new-id-list))
        (<- new-assum1 (declaration nil new-id1 (int-term 'INT nil)))
        (<- ref-children 
            (list (make-child
                      ref-assums
                      (equal-term
                          'EQUAL
                          nil
                          (int-term 'INT nil)
                          (mapcar #'value-of-ind-term
                                  (terms-of-equal-term ref-concl)
                          )
                      )
                  )
                  (make-child
                      (append ref-assums
                              (list new-assum1
                                    (declaration
                                       nil
                                       nil
                                       (less-term 
                                           'LESS 
                                           nil
                                           (var-term 'VAR nil new-id1)
                                           (pos-number-term 'POS-NUMBER nil 0)
                                       )
                                    )
                                    (declaration 
                                       nil
                                       new-id2
                                       (substitute 
                                          over-term
                                          (list (list over-id add1-term))
                                       )
                                     )
                              )
                      )
                      (equal-term
                          'EQUAL
                          nil
                          (substitute over-term
                                      (list (list over-id 
                                                  (var-term 'VAR nil new-id1)
                                            )
                                      )
                          )
                          (substitute-n-in-all-terms$
                                (list new-id1 new-id2)
                                (mapcar
                                    #'(lambda (x)                     
                                        (bound-ids-of-bound-id-term 
                                                     (downterm-of-ind-term x)
                                        )
                                     )
                                    (terms-of-equal-term ref-concl)
                                )
                                (mapcar
                                    #'(lambda (x) 
                                        (term-of-bound-id-term 
                                                      (downterm-of-ind-term x)
                                        )
                                      )
                                      (terms-of-equal-term ref-concl)
                                 )
                          )
                      )
                  )
                  (make-child
		      ref-assums
                      (equal-term
                          'EQUAL
                          nil
                          (substitute 
                              over-term
                              (list (list over-id 
                                          (pos-number-term 'POS-NUMBER nil 0)
                                    )
                              )
                          )
                          (mapcar #'baseterm-of-ind-term
                                  (terms-of-equal-term ref-concl)
                          )
                      )
                  )
                  (make-child
                      (append ref-assums
                              (list new-assum1
                                    (declaration
                                       nil
                                       nil
                                       (less-term 
                                           'LESS 
                                           nil
                                           (pos-number-term 'POS-NUMBER nil 0)
                                           (var-term 'VAR nil new-id1)
                                       )
                                    )
                                    (declaration 
                                       nil
                                       new-id2
                                       (substitute 
                                          over-term
                                          (list (list over-id sub1-term))
                                       )
                                     )
                              )
                      )
                      (equal-term
                          'EQUAL
                          nil
                          (substitute over-term
                                      (list (list over-id 
                                                  (var-term 'VAR nil new-id1)
                                            )
                                      )
                          )
                          (substitute-n-in-all-terms$
                                (list new-id1 new-id2)
                                (mapcar
                                    #'(lambda (x)                     
                                        (bound-ids-of-bound-id-term 
                                                     (upterm-of-ind-term x)
                                        )
                                     )
                                    (terms-of-equal-term ref-concl)
                                )
                                (mapcar
                                    #'(lambda (x) 
                                        (term-of-bound-id-term 
                                                      (upterm-of-ind-term x)
                                        )
                                      )
                                      (terms-of-equal-term ref-concl)
                                 )
                          )
                      )
                  )
            )
        )     
    )
    nil
)

(defun refine-eq-intro-list ()
    (check-concl$ 'LIST 'UNIVERSE)
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (type-of-equal-term ref-concl)
                                    (mapcar
                                           #'type-of-list-term
                                           (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                     )
    )
    nil
)      

(defun refine-eq-intro-nil ()
    (check-concl$ 'NIL 'LIST)
    (<- ref-children 
        (list (make-child ref-assums
                          (equal-term
                                'EQUAL
                                nil
                                (universe-term
                                    'UNIVERSE
                                    nil
                                    (level-of-equal-intro-rule-level ref-rule)
                                )
                                (list (type-of-list-term 
                                            (type-of-equal-term ref-concl)
                                      )
                                )
                          )
              )
        )
    )
    nil
)

(defun refine-eq-intro-cons ()
    (check-concl$ 'CONS 'LIST)
    (<- ref-children
        (list (make-child ref-assums
                          (equal-term
                              'EQUAL
                              nil
                              (type-of-list-term (type-of-equal-term ref-concl))
                              (mapcar #'head-of-cons-term
                                      (terms-of-equal-term ref-concl)
                              )
                          )
              )
              (make-child ref-assums
                          (equal-term
                              'EQUAL
                              nil
                              (type-of-equal-term ref-concl)
                              (mapcar #'tail-of-cons-term
                                      (terms-of-equal-term ref-concl)
                              )
                          )
              )
        )
    )
    nil
)

    
    
(defun refine-eq-intro-list-ind ()
    (Plet (new-id1    nil
          new-id2    nil    
          new-id3    nil
          new-id-list nil
          over-id    nil
          over-term  nil
          using-term (using-term-of-equal-intro-rule-using ref-rule)
          value      (value-of-list-ind-term 
                                  (car (terms-of-equal-term ref-concl))
                     )
          cons-term  nil
         )
        (check-concl-kind$)
        (check-terms-kind$ 'LIST-IND)                            
        (check-all-free-vars-declared using-term)
	(Pif (not (eql (kind-of-term using-term) 'LIST)) -->
	    (ref-error '|the using term must be a list term|)
	 fi)
        (<- new-id-list
            (Pif (null (new-ids-of-equal-intro-rule-using ref-rule)) -->
                (bound-ids-of-bound-id-term 
                 (upterm-of-list-ind-term (car (terms-of-equal-term ref-concl)))
                )
             || t -->
                (new-ids-of-equal-intro-rule-using ref-rule)
             fi)
        )
        (Pif (null (over-pair-of-equal-intro-rule-using ref-rule)) -->
            (<- over-term (type-of-equal-term ref-concl))
         || t -->
            (<- over-id (car (over-pair-of-equal-intro-rule-using ref-rule)))
            (<- over-term (cdr (over-pair-of-equal-intro-rule-using ref-rule)))
            (Pif (not (equal-terms (type-of-equal-term ref-concl)
                                  (substitute over-term 
                                              (list (list over-id value))
                                  )
                     )
                ) -->
                (ref-error (concat '|the type of the equal term doesn't |
                                   '|properly match the term after 'over' |
                            )
                )
             fi)
         fi)    
        (check-if-all-new$ 
                   new-id-list ref-assums
        )
        (<- new-id1 (car new-id-list))
        (<- new-id2 (cadr new-id-list))
        (<- cons-term (cons-term 'CONS nil (var-term 'VAR nil new-id1)
                                           (var-term 'VAR nil new-id2)
                     )                                            
        )
        (<- new-id3 (caddr new-id-list))
        (<- ref-children 
            (list (make-child
                      ref-assums
                      (equal-term
                          'EQUAL
                          nil
                          using-term
                          (mapcar #'value-of-list-ind-term
                                  (terms-of-equal-term ref-concl)
                          )
                      )
                  )
                  (make-child
		      ref-assums
                      (equal-term
                          'EQUAL nil
                          (substitute 
                              over-term
                              (list (list over-id 
                                          (nil-term 'NIL nil)
                                    )
                              )
                          )
                          (mapcar #'baseterm-of-list-ind-term
                                  (terms-of-equal-term ref-concl)
                          )
                      )
                  )
                  (make-child
                      (append ref-assums
                              (list (declaration
                                        nil
                                        new-id1
                                        (type-of-list-term using-term)
                                    )
                                    (declaration
                                       nil
                                       new-id2
                                       using-term
                                    )
                                    (declaration 
                                       nil
                                       new-id3
                                       (substitute 
                                         over-term
                                         (list (list over-id 
                                                     (var-term 'VAR nil new-id2)
                                               )
                                         )
                                       )
                                     )
                              )
                      )
                      (equal-term
                          'EQUAL
                          nil
                          (substitute over-term
                                      (list (list over-id 
                                                  cons-term
                                            )
                                      )
                          )
                          (substitute-n-in-all-terms$
                                (list new-id1 new-id2 new-id3)
                                (mapcar
                                    #'(lambda (x)
					(bound-ids-of-bound-id-term
					  (upterm-of-list-ind-term x)))
                                    (terms-of-equal-term ref-concl)
                                )
                                (mapcar
                                    #'(lambda (x) 
                                        (term-of-bound-id-term 
                                                     (upterm-of-list-ind-term x)
                                        )
                                      )
                                      (terms-of-equal-term ref-concl)
                                 )
                          )
                      )
                  )
            )
        )     
    )
    nil
)

(defun refine-eq-intro-union ()
    (check-concl$ 'UNION 'UNIVERSE)
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (type-of-equal-term ref-concl)
                                    (mapcar
                                        #'lefttype-of-union-term
                                        (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                           (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (type-of-equal-term ref-concl)
                                    (mapcar
                                       #'righttype-of-union-term
                                       (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                     )
    )
    nil
)
                                                                    
(defun refine-eq-intro-inl ()
    (check-concl$ 'INL 'UNION)
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (lefttype-of-union-term 
                                           (type-of-equal-term ref-concl)
                                    )
                                    (mapcar
                                        #'term-of-injection-term
                                        (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                           (make-child
                              ref-assums
                              (equal-term
                                 'EQUAL
                                 nil
                                 (universe-term 
                                    'UNIVERSE 
                                    nil 
                                    (level-of-equal-intro-rule-level ref-rule)
                                 )
                                 (list (righttype-of-union-term
                                                 (type-of-equal-term ref-concl)
                                       )
                                 )
                              )
                           )
                     )
    )
    nil
)

(defun refine-eq-intro-inr ()
    (check-concl$ 'INR 'UNION)
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (righttype-of-union-term 
                                           (type-of-equal-term ref-concl)
                                    )
                                    (mapcar
                                        #'term-of-injection-term
                                        (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                           (make-child
                              ref-assums
                              (equal-term
                                 'EQUAL
                                 nil
                                 (universe-term 
                                    'UNIVERSE 
                                    nil 
                                    (level-of-equal-intro-rule-level ref-rule)
                                 )
                                 (list (lefttype-of-union-term
                                                 (type-of-equal-term ref-concl)
                                       )
                                 )
                              )
                           )
                     )
    )
    nil
)

(defun refine-eq-intro-decide ()    
    (Plet (over-term nil
          over-id   nil
          new-id1   nil
          new-id2   nil
          new-id-list (new-ids-of-equal-intro-rule-using ref-rule)
          using-term (using-term-of-equal-intro-rule-using ref-rule)
          value     (value-of-decide-term (car (terms-of-equal-term ref-concl)))
         )
        (check-concl-kind$)
        (check-terms-kind$ 'DECIDE)
	(Pif (not (eql (kind-of-term using-term) 'UNION)) -->
	    (ref-error '|using term must be a union term|)
	 fi)
        (check-all-free-vars-declared using-term)
        (multiple-value-setq (new-id1 new-id2) (check-ids 0 2 new-id-list))
        (Pif (and (null new-id1) (null new-id2)) -->
	    (<- new-id1
		(car
		  (bound-ids-of-bound-id-term 
                        (leftterm-of-decide-term 
                            (car (terms-of-equal-term ref-concl))
                        )
                  )
		)
	    )
	    (<- new-id2
		(car
		  (bound-ids-of-bound-id-term 
                        (rightterm-of-decide-term 
                            (car (terms-of-equal-term ref-concl))
                        )
                  )
		)
	    )
            (check-if-new$ new-id1 ref-assums)
            (check-if-new$ new-id2 ref-assums)
         || (or (null new-id1) (null new-id2)) -->
            (ref-error '|two new ids must be given|)
         fi)
        
        (Pif (null (over-pair-of-equal-intro-rule-using ref-rule)) -->
            (<- over-term (type-of-equal-term ref-concl))

         || t -->
            (<- over-id (car (over-pair-of-equal-intro-rule-using ref-rule)))
            (<- over-term (cdr (over-pair-of-equal-intro-rule-using ref-rule)))
            (Pif (not (equal-terms (substitute over-term
                                              (list (list over-id value))
                                  )
                                  (type-of-equal-term ref-concl)
                     )
                ) -->
                (ref-error (concat '|the type of the equal-term doesn't |
                                   '|properly match the term after 'over' |
                           )
                )
             fi)
         fi)
        (<- ref-children 
            (list (make-child
                        ref-assums
                        (equal-term
                            'EQUAL
                            nil
                            using-term
                            (mapcar #'value-of-decide-term
                                    (terms-of-equal-term ref-concl)
                            )
                        )
                  )
                  (make-child
                        (append 
                            ref-assums                 
                            (list (declaration
                                       nil
                                       new-id1
                                       (lefttype-of-union-term using-term)            
                                  )
				  (declaration
				    nil nil
				    (equal-term
				      'EQUAL nil
				      using-term
				      (list
					(injection-term
					  'INL nil
					  (var-term 'VAR nil new-id1)
					)
					(value-of-decide-term
					  (car (terms-of-equal-term ref-concl))
					)
				      )
				    )
				  )
					  
                            )
                        )
                        (equal-term
                            'EQUAL
                            nil
                            (substitute over-term
                                        (list (list 
                                                 over-id
                                                 (injection-term 
                                                    'INL
                                                     nil
                                                     (var-term 'VAR nil new-id1)
                                                  )
                                              )
                                        )
                            )
                            (substitute-in-all-terms$ 
                                new-id1 
                                (mapcar #'(lambda (x)                   
                                            (car (bound-ids-of-bound-id-term
                                                    (leftterm-of-decide-term x)
                                                 )    
                                            )
                                         )
                                        (terms-of-equal-term ref-concl)
                                )
                                (mapcar #'(lambda (x) 
                                            (term-of-bound-id-term
                                                    (leftterm-of-decide-term x)
                                            )       
                                         )
                                        (terms-of-equal-term ref-concl)
                                )
                            )
                        )
                  )
                  (make-child
                        (append 
                            ref-assums                 
                            (list (declaration
                                       nil
                                       new-id2
                                       (righttype-of-union-term using-term)            
                                  )
				  (declaration
				    nil nil
				    (equal-term
				      'EQUAL nil
				      using-term
				      (list
					(injection-term
					  'INR nil
					  (var-term 'VAR nil new-id2)
					)
					(value-of-decide-term
					  (car (terms-of-equal-term ref-concl))
					)
				      )
				    )
				  )
                            )
                        )
                        (equal-term
                            'EQUAL
                            nil
                            (substitute over-term
                                        (list (list 
                                                 over-id
                                                 (injection-term 
                                                    'INR
                                                     nil
                                                     (var-term 'VAR nil new-id2)
                                                  )
                                              )
                                        )
                            )
                            (substitute-in-all-terms$ 
                                new-id2
                                (mapcar #'(lambda (x)                   
                                            (car (bound-ids-of-bound-id-term
                                                    (rightterm-of-decide-term x)
                                                 )    
                                            )
                                         )
                                        (terms-of-equal-term ref-concl)
                                )
                                (mapcar #'(lambda (x) 
                                            (term-of-bound-id-term
                                                    (rightterm-of-decide-term x)
                                            )       
                                         )
                                        (terms-of-equal-term ref-concl)
                                )
                            )
                        )
                  )
            )
        )
    )
    nil
)

(defun refine-eq-intro-product ()
    (check-concl$ 'PRODUCT 'UNIVERSE)
    (Plet (new-id
           (Pif (null (new-id-of-equal-intro-rule-new-id ref-rule)) -->
               (get-first-non-nil-id$ 
                    (mapcar #'bound-id-of-product-term
                        (terms-of-equal-term ref-concl)
                    )
               )
            || t -->
               (new-id-of-equal-intro-rule-new-id ref-rule)
            fi)
         )
        (check-if-new$ new-id ref-assums)
        (<- ref-children 
            (list (make-child
                        ref-assums
                        (equal-term
                              'EQUAL
                              nil
                              (type-of-equal-term ref-concl)
                              (mapcar #'lefttype-of-product-term
                                      (terms-of-equal-term ref-concl)
                              )
                        )
                  )
                  (make-child
                        (append ref-assums
                                (list
                                   (declaration 
                                      nil
                                      new-id
                                      (lefttype-of-product-term
                                               (car (terms-of-equal-term ref-concl))
                                      )
                                   )
                                 )
                        )
                        (equal-term
                            'EQUAL
                            nil
                            (type-of-equal-term ref-concl)
                            (substitute-in-all-terms$
                                new-id
                                (mapcar #'bound-id-of-product-term
                                        (terms-of-equal-term ref-concl)
                                )
                                (mapcar #'righttype-of-product-term
                                        (terms-of-equal-term ref-concl)
                                )
                            )
                        )
                   )
             )
        )
    )
    nil
)

(defun refine-eq-intro-pair ()
    (check-concl$ 'PAIR 'PRODUCT)
    (Plet (new-id
             (Pif (null (new-id-of-equal-intro-rule-level ref-rule)) -->
                 (bound-id-of-product-term (type-of-equal-term ref-concl))
              || t -->
                 (new-id-of-equal-intro-rule-level ref-rule)
              fi)
         )
        (check-if-new$ new-id ref-assums)
        (Pif (null new-id) -->
             (<- ref-children (list (make-child
                                       ref-assums
                                       (equal-term
                                           'EQUAL
                                           nil
                                           (lefttype-of-product-term 
                                                    (type-of-equal-term ref-concl)
                                           )
                                           (mapcar
                                             #'leftterm-of-pair-term
                                             (terms-of-equal-term ref-concl)
                                           )
                                       )
                                    )
                                    (make-child
                                       ref-assums
                                       (equal-term
                                           'EQUAL
                                           nil
                                           (righttype-of-product-term 
                                               (type-of-equal-term ref-concl)
                                           )
                                           (mapcar
                                            #'rightterm-of-pair-term
                                             (terms-of-equal-term ref-concl)
                                           )
                                       )
                                    )
                              )
             )
    
         || t -->
            (<- ref-children (list (make-child
                                      ref-assums
                                      (equal-term
                                          'EQUAL
                                          nil
                                          (lefttype-of-product-term 
                                                 (type-of-equal-term ref-concl)
                                          )
                                          (mapcar
                                             #'leftterm-of-pair-term
                                             (terms-of-equal-term ref-concl)
                                          )
                                      )
                                    )
                                    (make-child
                                       ref-assums
                                       (equal-term
                                          'EQUAL
                                          nil
                                          (substitute
                                              (righttype-of-product-term 
                                                     (type-of-equal-term ref-concl)
                                              )
                                              (list 
                                                (list
                                                   (bound-id-of-product-term
                                                      (type-of-equal-term ref-concl)
                                                   )
                                                   (leftterm-of-pair-term
                                                      (car (terms-of-equal-term
                                                                          ref-concl
                                                           )
                                                      )
                                                   )
                                                )
                                              )
                                          )
                                          (mapcar
                                            #'rightterm-of-pair-term
                                            (terms-of-equal-term ref-concl)
                                          )
                                       )
                                    )
                                    (make-child
                                      (append 
                                          ref-assums
                                          (list
                                              (declaration 
                                                 nil
                                                 new-id
                                                 (lefttype-of-product-term
                                                      (type-of-equal-term ref-concl)
                                                 )
                                               )
                                          )
                                      )
                                      (equal-term
                                         'EQUAL
                                         nil
                                         (universe-term 
                                           'UNIVERSE
                                           nil
                                           (level-of-equal-intro-rule-level ref-rule)
                                         )
                                         (list
                                          (substitute 
                                            (righttype-of-product-term
                                                    (type-of-equal-term ref-concl)
                                            )
                                            (list
                                              (list
                                                (bound-id-of-product-term
                                                     (type-of-equal-term ref-concl)
                                                )                                
                                                (var-term 'VAR nil new-id)
                                              )
                                            )
                                          )
                                         )
                                      )
                                    )
                              )
            )
         fi)
    )
    nil
)


;;;-
;;;- definitions for recursives ,partial funtion, fix, dom, rec_ind  begin here.
;;;-
;;;-

(defun refine-eq-intro-parfunction ()
    (check-concl$ 'PARFUNCTION 'UNIVERSE)
    (Plet (new-id
	     (Pif (null (new-id-of-equal-intro-rule-new-id ref-rule)) -->
		 (get-first-non-nil-id$
		     (mapcar #'bound-id-of-parfunction-term
			     (terms-of-equal-term ref-concl)
		     )
		 )
	      || t -->
	         (new-id-of-equal-intro-rule-new-id ref-rule)
	      fi)
	  )
	(check-if-new$ new-id ref-assums)
	(<- ref-children 
	    (list (make-child
			ref-assums
			(equal-term
			      'EQUAL
			      nil
			      (type-of-equal-term ref-concl)
			      (mapcar #'lefttype-of-parfunction-term
				      (terms-of-equal-term ref-concl)
			      )
			)
		  )
		  (make-child
			(append ref-assums
				(list
				   (declaration 
				      nil
				      new-id
				      (lefttype-of-parfunction-term
					       (car (terms-of-equal-term ref-concl))
				      )
				   )
				 )
			)
			(equal-term
			    'EQUAL
			    nil
			    (type-of-equal-term ref-concl)
			    (substitute-in-all-terms$
				new-id
				(mapcar #'bound-id-of-parfunction-term
					(terms-of-equal-term ref-concl)
				)
				(mapcar #'righttype-of-parfunction-term
					(terms-of-equal-term ref-concl)
				)
			    )
			)
		   )
	     )
	)
    )
    nil
)

(defun refine-eq-intro-dom ()
    (check-concl-kind$)
    (check-terms-kind$ 'DOM)                            
    (check-all-free-vars-declared 
        (using-term-of-equal-intro-rule-using ref-rule)
    )
    (Pif (not (and (eql 'FUNCTION
		      (kind-of-term (type-of-equal-term ref-concl)))
		  (eql 'UNIVERSE
		      (kind-of-term
			(righttype-of-function-term (type-of-equal-term ref-concl))))
	     )
        ) -->                 
        (ref-error '|type of the equal term must be of the form A->Uk |)

     fi)
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (using-term-of-equal-intro-rule-using ref-rule)
                                    (mapcar
                                      #'term-of-dom-term
                                      (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                           (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (righttype-of-function-term
				      (type-of-equal-term ref-concl)
				    )
				    (list
                                     (using-term-of-equal-intro-rule-using ref-rule)
				    ) 
                                )
                           )
                     )
    )
    nil
)

(defun refine-eq-intro-apply-partial ()
  (let* ((using-term (using-term-of-equal-intro-rule-using ref-rule)))
    (check-concl-kind$)
    (check-terms-kind$ 'APPLY-PARTIAL)
    (Pif (not (eql (kind-of-term using-term) 'PARFUNCTION)) -->
	(ref-error '|using term must be a partial function|) fi)
    (check-all-free-vars-declared  using-term)
    (Pif (not (= 1 (length (new-ids-of-equal-intro-rule-using ref-rule)))) -->
	(ref-error '|expecting one new id. |)
     fi)
    (check-if-new$ (car (new-ids-of-equal-intro-rule-using ref-rule)) ref-assums)
    (Pif (not (equal-terms (type-of-equal-term ref-concl)
                          (substitute                   
                            (righttype-of-parfunction-term 
                                using-term
                            )
                            (list
                             (list
                               (bound-id-of-parfunction-term
                                 using-term
                               )
                               (arg-of-apply-partial-term 
                                         (car (terms-of-equal-term ref-concl))
                               )
                             )
                            )
                          )
             )
        ) -->                 
        (ref-error (concat '|type of the equal term must correspond with the |
                           '|righttype of the partial function-term following 'using' |
                   )
        )
     fi)
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
				    using-term
                                    (mapcar
                                      #'function-of-apply-partial-term
                                      (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                           (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
				    (set-term
				      'SET
				      nil
				      (car (new-ids-of-equal-intro-rule-using ref-rule))
				      (lefttype-of-parfunction-term
					using-term
				      )
				      (apply-term
					'APPLY
					nil
					(dom-term
					  'DOM
					  nil
					  (function-of-apply-partial-term
					      (car (terms-of-equal-term ref-concl))
					  ) 
					)
					(var-term
					  'VAR
					  nil
					  (car (new-ids-of-equal-intro-rule-using ref-rule))
					)
				      )
				    )
                                     
                                    (mapcar #'arg-of-apply-partial-term
                                            (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                     )
    )
  )
  nil
)

(defun refine-eq-intro-fix ()
    (Plet (using-term-list (using-term-list-of-equal-intro-rule-fix ref-rule)
	  level           (level-of-equal-intro-rule-fix ref-rule)
	  fix-term1        nil
	  selecting-id    nil
	  term-list1      nil
	  term-list-list  nil
	  fix-ids         nil
	  ids1            nil
	 )
        (check-concl$ 'FIX 'PARFUNCTION)
	(<- fix-term1 (car (terms-of-equal-term ref-concl)))
	(<- term-list1
	    (term-list-of-bound-id-list-term (bound-id-list-term-of-fix-term fix-term1))
	)
	(<- fix-ids
	    (bound-ids-of-bound-id-list-term (bound-id-list-term-of-fix-term fix-term1))
	)
	(<- selecting-id (id-of-fix-term fix-term1))
	(Pif (not (eql (1- (length term-list1)) (length using-term-list))) -->
	    (ref-error '| using term list not of correct length |)
	 fi)
	(for (x in using-term-list)
	     (do
	       (Pif (not (eql (kind-of-term x) 'PARFUNCTION)) -->
		   (ref-error '|all terms of 'using' list should be of form w:A+>B |)
		fi)
	       (check-all-free-vars-declared x)
	     )
	)
	(for (z in (cdr (terms-of-equal-term ref-concl)))
	     (do
	       (Pif (not (eql (length term-list1)
			    (length
			      (term-list-of-bound-id-list-term
				(bound-id-list-term-of-fix-term z)
			      )
			    )
			 )
		   ) --> (ref-error '|fix must all have same number of subterms. |)

	       || (not (eql (selected-position fix-term1)
			   (selected-position z)
		       )
		  ) --> (ref-error
			 '|selected subterm must occur at the same position in each fix term.|
		        )

	       fi)
	     )
	)
	(Plet (n (selected-position fix-term1))
	     (<- using-term-list
		 (append (subseq using-term-list 0 n)
			 (list (type-of-equal-term ref-concl))
			 (nthcdr (- (length using-term-list)
				    (-  (length term-list1) (+ n 1))) using-term-list)
		 )
	     )
	)
	(<- ids1
	    (for (z in term-list1)
		 (save
		   (car (bound-ids-of-bound-id-term z))
		 )
	    )
	)
	(<- term-list-list
	    (make-term-list-list$
	      (mapcar #'bound-id-list-term-of-fix-term
		      (terms-of-equal-term ref-concl)
	      )
	    )
	)
        (<- ref-children 
          (append
	    (for (x in using-term-list)
		 (save
		   (make-child
		     ref-assums
		     (equal-term
		       'EQUAL
		       nil
		       (universe-term
			 'UNIVERSE
			 nil
			 level
		       )
		       (list x)
		     )
		   )
		 )
	    )
            (Plet (assum-segment
		   (for (y in using-term-list)
	                (z in (bound-ids-of-bound-id-list-term
				(bound-id-list-term-of-fix-term fix-term1)
			      )
			)
	                (save
	                  (declaration nil z y)
	                )
	           )
		 )
		 (append (for (z in term-list-list)
			      (y in using-term-list)
			      (w in ids1)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment
					  (list
					    (declaration nil
							 w
							 (lefttype-of-parfunction-term y)
					    )
					  )
				  )
				  (equal-term
				    'EQUAL
				    nil
				    (universe-term
				      'UNIVERSE
				      nil
				      level
				    )
				    (mapcar
				      #'(lambda (x)
					 (domain-transform
					   x
					   (pairlis
					     fix-ids
					     (mapcar
					      #'(lambda (i)
						 (dom-term 'DOM nil (var-term 'VAR  nil i))
					       )
					      fix-ids
					     )
					   )
					   nil)
					 )
				       z
				    )
				  )
				)
			      )
			 )
			 (for (z in term-list-list)
			      (y in using-term-list)
			      (w in ids1)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment
					  (list
					    (declaration nil
							 w
							 (lefttype-of-parfunction-term y)
					    )
					    (declaration
					      nil
					      nil
					      (domain-transform
						 (car z)
						 (pairlis
					           fix-ids
					           (mapcar
					            #'(lambda (i)
						       (dom-term
							 'DOM nil (var-term 'VAR  nil i))
					             )
					             fix-ids
					           )
					          )
						  nil
					       )
					     )
					  )
				  )
				  (equal-term
				    'EQUAL
				    nil
				    (substitute
				      (righttype-of-parfunction-term y)
				      (list
					(list
					  w
					  (var-term 'VAR nil (bound-id-of-parfunction-term y))
					)
				      )
				    )
				    z
				  )
				)
			      )
			 )
		 )

	    )
          )
        )
    )
    nil
)


(defun refine-eq-intro-rec-member ()       
    (Pif (not (eql 'RECURSIVE (kind-of-term (type-of-equal-term ref-concl)))) -->
	(ref-error '|Goal not of the right type. |)
     fi)
    (<- ref-children
	(Plet (selected-term
	       (nth
		 (position
		   (id-of-recursive-term (type-of-equal-term ref-concl))
		   (bound-ids-of-bound-id-list-term
		     (bound-id-list-term-of-recursive-term (type-of-equal-term ref-concl))
		   )
		 )
		 (term-list-of-bound-id-list-term
		   (bound-id-list-term-of-recursive-term (type-of-equal-term ref-concl))
		 )
	        )
	    )
	    (list
	        (make-child
		  ref-assums
		  (equal-term
		    'EQUAL
		    nil
		    (substitute
		       (term-of-bound-id-term selected-term)
		       (append
		        (list
		          (list
		             (car (bound-ids-of-bound-id-term selected-term))
		             (term-of-recursive-term (type-of-equal-term ref-concl))
		          )
		        )
		        (for (x1 in (bound-ids-of-bound-id-list-term
				      (bound-id-list-term-of-recursive-term
				        (type-of-equal-term ref-concl)
				      )
				    )
			     )
			     (x2 in (term-list-of-bound-id-list-term
				      (bound-id-list-term-of-recursive-term
				        (type-of-equal-term ref-concl)
				      )
				    )
			     )
			     (save
			       (list
			        x1
			        (lambda-term
			          'LAMBDA
			          nil
			          (car (bound-ids-of-bound-id-term x2))
			          (recursive-term
				    'RECURSIVE
				    nil
				    (bound-id-list-term-of-recursive-term
				      (type-of-equal-term ref-concl)
				    )
				    (fix-term-of-recursive-term
				      (type-of-equal-term ref-concl)
				    )
				    x1
				    (var-term 'VAR nil (car (bound-ids-of-bound-id-term x2)))
			          )
			        )
			      )
			    )
		         )
		        )
		     )
		     (terms-of-equal-term ref-concl)
		  )
		)
		(make-child 
		    ref-assums
		    (equal-term 
			'EQUAL
			nil               
			(universe-term
			    'UNIVERSE
			    nil
			    (level-of-equal-intro-rule-level ref-rule)
			)
			(list (type-of-equal-term ref-concl))
		    )
		)
	    )
       )
    )
    nil
)


(defun refine-eq-intro-simple-rec-member ()       
    (check-concl-kind$)
    (check-type-kind$ 'SIMPLE-REC)
    (let* ((rec-term (type-of-equal-term ref-concl))
	   (rec-term-term (term-of-simple-rec-term rec-term))
	   (id-of-rec-term (bound-id-of-simple-rec-term rec-term)))      
      (<- ref-children
	  (list
	    (make-child
	      ref-assums
	      (equal-term
		'EQUAL
		nil
		(substitute
		  rec-term-term
		  `((,id-of-rec-term ,rec-term)))
		(terms-of-equal-term ref-concl)))
	    (make-child 
	      ref-assums
	      (equal-term 
		'EQUAL
		nil               
		(universe-term
		  'UNIVERSE
		  nil
		  (level-of-equal-intro-rule-level ref-rule)
		  )
		(list rec-term))))))) 


(defun refine-eq-intro-rec-ind ()
    (let* ((level (level-of-equal-intro-rule-rec-ind ref-rule))
	   (over-pair-list (over-pair-list-of-equal-intro-rule-rec-ind ref-rule))
	   (using-term-list (using-term-list-of-equal-intro-rule-rec-ind ref-rule))
	   (using-term (car using-term-list)))
	(Pif (not (and (eql (kind-of-term using-term) 'BOUND-ID-TERM)
		      (= (length (bound-ids-of-bound-id-term using-term)) 1)
		      (eql (kind-of-term (term-of-bound-id-term using-term)) 'RECURSIVE)
		      (eql (kind-of-term
			    (term-of-recursive-term (term-of-bound-id-term using-term))
			  )
			  'VAR
		      )
		      (eql (car (bound-ids-of-bound-id-term using-term))
			  (id-of-var-term
			    (term-of-recursive-term (term-of-bound-id-term using-term))
			  )
		      )
		 )
	    ) --> (ref-error '|first term in 'using' list not of correct form. |)
	 fi)
	(Pif (fix-term-of-recursive-term (term-of-bound-id-term using-term)) -->
	    (refine-eq-intro-rec-ind-with-fix level over-pair-list using-term-list)
	 || t -->
	    (refine-eq-intro-rec-ind-without-fix level over-pair-list using-term-list)
	 fi)
    )
)

(defun refine-eq-intro-rec-ind-with-fix (level over-pair-list using-term-list)
    (Plet (id-rec-pair       (car using-term-list)
	  rec-ind-term      nil
	  rec-ind-term-list nil
	  term-list-list    nil
	  fix-term          nil
	  fix-term-list     nil
	  fix-id-list       nil
	  rec-term-list     nil
	  ids1              nil
	  ids2              nil
	  subst-list        nil
	  selected1         0
	  selected2         0
	)

	(for (x in using-term-list)
	     (do
	       (Pif (not (eql (kind-of-term x) 'PARFUNCTION)) -->
		   (ref-error '|all using terms must be partial function terms|) fi)
	       (check-all-free-vars-declared x)
	     )
	)
	(<- using-term-list (cdr using-term-list))
	(<- rec-ind-term (car (terms-of-equal-term ref-concl))) 
	(<- rec-ind-term-list (term-list-of-bound-id-list-term
				(bound-id-list-term-of-rec-ind-term rec-ind-term)
			      )
	)
	(<- ids2 (bound-ids-of-bound-id-list-term
		    (bound-id-list-term-of-rec-ind-term rec-ind-term)
		 )
	)
	(<- rec-term-list (term-list-of-bound-id-list-term
			    (bound-id-list-term-of-recursive-term
			      (term-of-bound-id-term id-rec-pair)
			    )
			  )
	)
	(<- ids1 (bound-ids-of-bound-id-list-term
		    (bound-id-list-term-of-recursive-term
		      (term-of-bound-id-term id-rec-pair)
		    )
		 )
	)
	(<- fix-term (fix-term-of-recursive-term (term-of-bound-id-term id-rec-pair)))
	(<- fix-term-list (term-list-of-bound-id-list-term
			     (bound-id-list-term-of-fix-term fix-term)
			  )
	)
	(<- fix-id-list (bound-ids-of-bound-id-list-term
		          (bound-id-list-term-of-fix-term fix-term)
		         )
	)
	(Pif (not (and (eql (length rec-ind-term-list) (length using-term-list))
		      (eql (length rec-ind-term-list) (length over-pair-list))
		      (eql (length rec-ind-term-list) (length rec-term-list))
		  )
	    ) -->
	    (ref-error '| term lists not all of same length. |)
	 fi)
	(<- selected1
	    (position
	      (id-of-rec-ind-term rec-ind-term) ids2
	    )
	)
	(<- selected2
	    (position
	      (id-of-recursive-term (term-of-bound-id-term id-rec-pair)) ids1
	    )
	)
	(Pif (not (eql selected1 selected2)) -->
	    (ref-error
	      (concat '| the selected ids of the rec and red_ind terms |
		      '|should occur at same position in term lists|
	      )
	    )
	 fi)
	;;- check over-pair-list for undeclared vars.
	(for (x in over-pair-list)
	     (do
	       (Pif (not (null (prl-set-difference
				(free-vars-not-declared (cdr x) ref-assums)
				(list-to-set (list (car x)))
			      )
			)
		   ) --> (ref-error '|all free vars of 'using' terms must be declared. |)
	       fi)
	     )
	)
	;;- check that Gi[t/pi] matches with ith term in over-pair-list.
	(Pif (not (equal-terms (substitute
				(cdr (nth selected1 over-pair-list))
                                (list
				  (list
				    (car (nth selected1 over-pair-list))
				    (term-of-rec-ind-term rec-ind-term)
				  )
				)
                               )
                              (type-of-equal-term ref-concl)
                     )
                ) -->
                (ref-error (concat '|the type of the equal-term doesn't |
                                   '|properly match the corresponding term |
				   '|in the 'over' list. |
                           )
                )
         fi)
	(<- subst-list (for (x in ids1)
			    (z in fix-id-list)
			    (save
			      (list x (dom-term 'DOM nil (var-term 'VAR nil z)))
			    )
		       )
	)
	(<- term-list-list
	    (make-term-list-list$
	      (mapcar #'bound-id-list-term-of-rec-ind-term
		      (terms-of-equal-term ref-concl)
	      )
	    )
	)
        (<- ref-children 
          (append
	    (for (x in using-term-list) ;;- 1
		 (save
		   (make-child
		     ref-assums
		     (equal-term
		       'EQUAL
		       nil
		       (universe-term 'UNIVERSE nil level)
		       (list x)
		     )
		   )
		 )
	    )
            (Plet (assum-segment1
		    (for (y in using-term-list)
	                 (z in fix-id-list)
	                 (save
	                   (declaration nil z y)
	                 )
	            )
		  assum-segment2
		                 (make-assum-segment2 using-term-list
					              over-pair-list
						      (bound-id-list-term-of-recursive-term
							(term-of-bound-id-term id-rec-pair)
						      )
					              (bound-id-list-term-of-fix-term
							fix-term
						      )
						      ids2
					              level
		                 )
		 )
		 (append (for (y in using-term-list) ;;- 2
			      (w in term-list-list)
			      (z in over-pair-list)
			      (v in rec-term-list)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment2
					  (list
					    (declaration
					      nil
					      (car z)
					      (product-term
						'PRODUCT
						nil
						(car (bound-ids-of-bound-id-term v))
						(lefttype-of-parfunction-term y)
						(substitute
						  (term-of-bound-id-term v)
						  (for (f in fix-id-list)
						       (save
							 (list
							  f
							  (fix-term
							    'FIX
							    nil
							    (bound-id-list-term-of-fix-term
							      fix-term
							    )
							    f
							  )
							 )
						       )
						  )	   
						)
					      )
					    )
					  )
				  )
				  (equal-term
				    'EQUAL
				    nil
				    (substitute
				      (cdr z)
				      (list
					(list (car z)
					      (var-term 'VAR
							nil
							(car (bound-ids-of-bound-id-term w))
					      )
					)
				      )
				    )
				    w
				  )
				)
			      )
			 )
			 (for (y in using-term-list) ;;- 3
			      (v in rec-term-list)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment1
					  (list
					    (declaration
					      nil
					      (car (bound-ids-of-bound-id-term v))
					      (lefttype-of-parfunction-term y)
					    )
					  )
				  )
				  (equal-term
				    'EQUAL
				    nil
				    (universe-term 'UNIVERSE nil level)
				    (list
				      (substitute
				         (term-of-bound-id-term v)
					 subst-list
				      )
				    )
				  )
				)
			      )
			 )
			 (for (z in fix-term-list)  ;;- 4
			      (w in rec-term-list)
			      (y in using-term-list)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment1
					  (list
					    (declaration nil
							 (car (bound-ids-of-bound-id-term z))
							 (lefttype-of-parfunction-term y)
					    )
					    (declaration nil
							 nil
							 (substitute
							   (term-of-bound-id-term w)
							   (cons
							     (list
							       (car
							        (bound-ids-of-bound-id-term w)
							       )
							       (var-term 'VAR nil
								(car
							        (bound-ids-of-bound-id-term z)
							        )
							       )
							     )
							     subst-list
							   )
							 )
					    )
					  )
				  )
				  (equal-term
				    'EQUAL
				    nil
				    (substitute
				      (righttype-of-parfunction-term y)
				      (list
					(list
					  (car (bound-ids-of-bound-id-term z))
					  (var-term 'VAR nil (bound-id-of-parfunction-term y))
					)
				      )
				    )
				    (list (term-of-bound-id-term z))
				  )
				)
			      )
			 )
			 (list
			   (make-child    ;;- 5
			     ref-assums
			     (equal-term
			       'EQUAL
			       nil
			       (product-term
				 'PRODUCT
				 nil
				 (car (bound-ids-of-bound-id-term id-rec-pair))
				 (lefttype-of-parfunction-term
				   (nth selected1 using-term-list)
				 )
				 (term-of-bound-id-term id-rec-pair)
			       )
			       (mapcar #'term-of-rec-ind-term
				       (terms-of-equal-term ref-concl)
			       )
			     )
			   )
			 )
		 )

	    )
          )
        )
    )
    nil
)

(defun refine-eq-intro-rec-ind-without-fix (level over-pair-list using-term-list)
    (Plet (id-rec-pair       (car using-term-list)
	  rec-ind-term      nil
	  rec-ind-term-list nil
	  rec-term-list     nil
	  term-list-list    nil
	  ids1              nil
	  ids2              nil
	  selected1         0
	  selected2         0
	)
	
	(<- using-term-list (cdr using-term-list))
	(check-all-free-vars-declared id-rec-pair)
	(for (x in using-term-list)
	     (do
	       (check-all-free-vars-declared x)
	     )
	)
	(<- rec-ind-term (car (terms-of-equal-term ref-concl))) 
	(<- rec-ind-term-list (term-list-of-bound-id-list-term
				(bound-id-list-term-of-rec-ind-term rec-ind-term)
			      )
	)
	(<- ids2 (bound-ids-of-bound-id-list-term
		    (bound-id-list-term-of-rec-ind-term rec-ind-term)
		 )
	)
	(<- rec-term-list (term-list-of-bound-id-list-term
			    (bound-id-list-term-of-recursive-term
			      (term-of-bound-id-term id-rec-pair)
			    )
			  )
	)
	(<- ids1 (bound-ids-of-bound-id-list-term
		    (bound-id-list-term-of-recursive-term
		      (term-of-bound-id-term id-rec-pair)
		    )
		 )
	)
	(Pif (not (and (eql (length rec-ind-term-list) (length using-term-list))
		      (eql (length rec-ind-term-list) (length over-pair-list))
		      (eql (length rec-ind-term-list) (length rec-term-list))
		  )
	    ) -->
	    (ref-error '| term lists not all of same length. |)
	 fi)
	(<- selected1 (selected-position rec-ind-term))
	(<- selected2 (selected-position (term-of-bound-id-term id-rec-pair)))
	(Pif (not (eql selected1 selected2)) -->
	    (ref-error
	      (concat '| the selected ids of the rec and red_ind terms |
		      '|should occur at same position in term lists|
	      )
	    )
	 fi)
	;;- check over-pair-list for undeclared vars.
	(for (x in over-pair-list)
	     (do
	       (Pif (not (null (prl-set-difference
				(free-vars-not-declared (cdr x) ref-assums)
				(list-to-set (list (car x)))
			      )
			)
		   ) --> (ref-error '|all free vars of 'using' terms must be declared. |)
	       fi)
	     )
	)
	;;- check that Gi[t/pi] matches with ith term in over-pair-list.
	(Pif (not (equal-terms (substitute
				(cdr (nth selected1 over-pair-list))
                                (list
				  (list
				    (car (nth selected1 over-pair-list))
				    (term-of-rec-ind-term rec-ind-term)
				  )
				)
                               )
                              (type-of-equal-term ref-concl)
                     )
                ) -->
                (ref-error (concat '|the type of the equal-term doesn't |
                                   '|properly match the corresponding term |
				   '|in the 'over' list. |
                           )
                )
         fi)
	(<- term-list-list
	    (make-term-list-list$
	      (mapcar #'bound-id-list-term-of-rec-ind-term
		      (terms-of-equal-term ref-concl)
	      )
	    )
	)
        (<- ref-children 
          (append
	    (for (x in using-term-list) ;;- 1
		 (save
		   (make-child
		     ref-assums
		     (equal-term
		       'EQUAL
		       nil
		       (universe-term 'UNIVERSE nil level)
		       (list x)
		     )
		   )
		 )
	    )
            (Plet (assum-segment1
		       (for (y in using-term-list)
	                    (g in ids1)
	                    (save
	                      (declaration nil
			                 g
			                 (function-term
				           'FUNCTION
				           nil
				           nil
					   y
				           (universe-term 'UNIVERSE nil level)
			                 )
	                      )  
	                   )
	                )
		  assum-segment3
		                 (make-assum-segment3
				   using-term-list
				   over-pair-list
				   (bound-id-list-term-of-recursive-term
				     (term-of-bound-id-term id-rec-pair)
				   )
				   ids2
				   level
		                 )
		 )
		 (append (for (y in using-term-list) ;;- 2
			      (w in term-list-list)
			      (z in over-pair-list)
			      (v in rec-term-list)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment3
					  (list
					    (declaration
					      nil
					      (car z)
					      (product-term
						'PRODUCT
						nil
						(car (bound-ids-of-bound-id-term v))
						y
						(term-of-bound-id-term v)
					      )
					    )
					  )
				  )
				  (equal-term
				    'EQUAL
				    nil
				    (substitute
				      (cdr z)
				      (list
					(list (car z)
					      (var-term 'VAR
							nil
							(car (bound-ids-of-bound-id-term w))
					      )
					)
				      )
				    )
				    w
				  )
				)
			      )
			 )
			 (for (y in using-term-list) ;;- 3
			      (v in rec-term-list)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment1
					  (list
					    (declaration
					      nil
					      (car (bound-ids-of-bound-id-term v))
					      y
					    )
					  )
				  )
				  (equal-term
				    'EQUAL
				    nil
				    (universe-term 'UNIVERSE nil level)
				    (list
				      (term-of-bound-id-term v)
				    )
				  )
				)
			      )
			 )
			 (list
			   (make-child    ;;- 4
			     ref-assums
			     (equal-term
			       'EQUAL
			       nil
			       (product-term
				 'PRODUCT
				 nil
				 (car (bound-ids-of-bound-id-term id-rec-pair))
				 (nth selected1 using-term-list)
				 (term-of-bound-id-term id-rec-pair)
			       )
			       (mapcar #'term-of-rec-ind-term
				       (terms-of-equal-term ref-concl)
			       )
			     )
			   )
			 )
		 )

	    )
          )
        )
    )
    nil
)

;(de refine-eq-intro-simple-rec-ind ()
;    (let* ((level (level-of-equal-intro-rule-simple-rec-ind ref-rule))
;	   (new-ids (let (new-ids (new-ids-of-equal-intro-rule-simple-rec-ind ref-rule))
;			 (for (i in (new-ids-of-equal-intro-rule-simple-rec-ind ref-rule))
;			      (do (check-if-new$ i ref-assums)))
;			 new-ids))
;	   (rec-type (let (rec-type
;			    (using-term-of-equal-intro-rule-simple-rec-ind ref-rule))
;			  (check-all-free-vars-declared rec-type)
;			  rec-type))
;	   (rec-ind (car (terms-of-equal-term ref-concl)))
;	   (rec-ind-arg (value-of-simple-rec-ind-term rec-ind))
;	   (rec-ind-bound-id-term (term-of-simple-rec-ind-term rec-ind))
;	   (rec-ind-h (first (bound-ids-of-bound-id-term rec-ind-bound-id-term)))
;	   (rec-ind-z (second (bound-ids-of-bound-id-term rec-ind-bound-id-term)))
;	   (rec-type-id (bound-id-of-simple-rec-term rec-type))
;	   (rec-type-term (term-of-simple-rec-term rec-type))
;	   (over-term (cdr (over-pair-of-equal-intro-rule-simple-rec-ind ref-rule)))
;	   (over-id (car (over-pair-of-equal-intro-rule-simple-rec-ind ref-rule)))
;	   (equality-type (type-of-equal-term ref-concl))
;	   (equands (terms-of-equal-term ref-concl))
;	   (recly-assumed-type-id
;	     (if (null new-ids)
;		 --> (progn (check-if-new$ rec-type-id ref-assums)
;			    rec-type-id)  ||
;		 t
;		 --> (first new-ids) fi))
;	   (induction-hyp-member
;	     (let (x (second new-ids))
;		  (if (null x)
;		      --> (progn (check-if-new$ rec-ind-h ref-assums)
;				 rec-ind-h)  ||
;		      t
;		      --> x fi)))
;	   (member-of-unrolling
;	     (let (x (third new-ids))
;		  (if (null x)
;		      --> (progn (check-if-new$ rec-ind-z ref-assums)
;				 rec-ind-z)  ||
;		      t
;		      --> x fi)))
;	   (adjusted-equality-type
;	     (if (null over-term)
;		 --> equality-type ||
;		 t
;		 -->
;		 (substitute
;		   over-term
;		   `((,over-id ,(var-term 'VAR nil member-of-unrolling)))) fi))
;	   (adjusted-rec-type-term
;	     (if (eql recly-assumed-type-id rec-type-id)
;		 --> rec-type-term  ||
;		 t
;		 --> (substitute
;		       rec-type-term
;		       `((,rec-type-id
;			  ,(var-term 'VAR nil recly-assumed-type-id)))) fi))
;	   (d-equands
;	     (mapcar
;	       #'(lambda (x)
;		   (substitute
;		     (term-of-bound-id-term (term-of-simple-rec-ind-term x))
;		     (dlet (((h z) (bound-ids-of-bound-id-term
;				     (term-of-simple-rec-ind-term x))))
;		       `((,h ,(var-term 'VAR nil induction-hyp-member))
;			 (,z ,(var-term 'VAR nil member-of-unrolling))))))
;	       equands))
;	   (value-equands
;	     (mapcar
;	       #'(lambda (x) (value-of-simple-rec-ind-term x))
;	       equands)))
;      (cond ((not (no-duplicates?
;		    (list induction-hyp-member member-of-unrolling recly-assumed-type-id)))
;	     (ref-error '|need 3 distinct new ids|)))
;      (if (and (not (null over-term))
;	       (not (equal-terms
;		      equality-type
;		      (substitute over-term `((,over-id ,rec-ind-arg))))))
;	  --> (ref-error '|over-term does not match conclusion|) fi)
;      (<- ref-children 
;	  (list
;	    (make-child
;	      (append 
;		ref-assums
;		(list
;		  (declaration
;		    nil
;		    recly-assumed-type-id
;		    (universe-term 'UNIVERSE nil level))
;		  (declaration
;		    nil
;		    nil
;		    (function-term
;		      'FUNCTION
;		      nil
;		      member-of-unrolling
;		      (var-term 'VAR nil recly-assumed-type-id)
;		      (equal-term
;			'EQUAL
;			nil
;			rec-type
;			(list (var-term 'VAR nil member-of-unrolling)))))
;		  (declaration
;		    nil
;		    induction-hyp-member
;		    (function-term
;		      'FUNCTION
;		      nil
;		      member-of-unrolling
;		      (var-term 'VAR nil recly-assumed-type-id)
;		      adjusted-equality-type))
;		  (declaration
;		    nil
;		    member-of-unrolling
;		    adjusted-rec-type-term)))
;	      (equal-term
;		'EQUAL
;		nil
;		adjusted-equality-type
;		d-equands))
;	    (make-child
;	      ref-assums
;	      (equal-term
;		'EQUAL
;		nil
;		rec-type
;		value-equands))))))

(defun refine-eq-intro-simple-rec-ind ()
    (check-concl-kind$)
    (check-terms-kind$ 'SIMPLE-REC-IND)
    (let* ((Ui (universe-term
		 'UNIVERSE nil (level-of-equal-intro-rule-simple-rec-ind ref-rule)))
	   (new-ids (Plet (new-ids (new-ids-of-equal-intro-rule-simple-rec-ind ref-rule))
		      (for (id in (new-ids-of-equal-intro-rule-simple-rec-ind ref-rule))
			   (do (check-if-new$ id ref-assums)))
		      new-ids))
	   (using-term (using-term-of-equal-intro-rule-simple-rec-ind ref-rule))
	   (phi (progn
		  (cond ((not (eql (kind-of-term using-term) 'SIMPLE-REC))
			 (ref-error '|the using term must be a simple-rec term|)))
		  (check-all-free-vars-declared using-term)
		  (using-term-of-equal-intro-rule-simple-rec-ind ref-rule)))
	   (omega (car (terms-of-equal-term ref-concl)))
	   (omega-arg (value-of-simple-rec-ind-term omega))
	   (omega-bound-id-term (term-of-simple-rec-ind-term omega))
	   (omega-h (first (bound-ids-of-bound-id-term omega-bound-id-term)))
	   (omega-z (second (bound-ids-of-bound-id-term omega-bound-id-term)))
	   (phi-id (bound-id-of-simple-rec-term phi))
	   (phi-body (term-of-simple-rec-term phi))
	   (v (car (over-pair-of-equal-intro-rule-simple-rec-ind ref-rule)))
	   (G-of-v (and v (cdr (over-pair-of-equal-intro-rule-simple-rec-ind ref-rule))))
	   (G (type-of-equal-term ref-concl))
	   (equands (terms-of-equal-term ref-concl))
	   (p (cond ((null new-ids) (check-if-new$ phi-id ref-assums) phi-id)
		    (t (first new-ids))))
	   (h (cond ((null (second new-ids)) (check-if-new$ omega-h ref-assums) omega-h)
		    (t (second new-ids))))
	   (z (cond ((null (third new-ids)) (check-if-new$ omega-z ref-assums) omega-z)
		    (t (third new-ids))))
	   (adjusted-G (cond ((null G-of-v) G)
			     (t (substitute G-of-v
					    (list (list v (var-term 'VAR nil z)))))))
	   (phi-subset (set-term
			 'SET nil z phi
			 (apply-term
			   'APPLY nil (var-term 'VAR nil p) (var-term 'VAR nil z))))

	   (d-equands  (mapcar
			 #'(lambda (x)
			     (substitute
			       (term-of-bound-id-term (term-of-simple-rec-ind-term x))
			       (let ((hh (first (bound-ids-of-bound-id-term
						  (term-of-simple-rec-ind-term x))))
				     (zz (second (bound-ids-of-bound-id-term
						   (term-of-simple-rec-ind-term x)))))
				 (list (list hh (var-term 'VAR nil h))
				       (list zz (var-term 'VAR nil z))))))
			 equands))
	   (t-equands (mapcar #'(lambda (x) (value-of-simple-rec-ind-term x))
			      equands)))
      (cond ((not (no-duplicates?
		    (remove '() (list h z p))))
	     (ref-error '|need 3 distinct new ids|)))
      (cond ((and (not (null G-of-v))
		  (not (equal-terms
			 G
			 (substitute G-of-v `((,v ,omega-arg))))))
	     (ref-error '|over term does not match conclusion|)))
      (<- ref-children 
	  (list
	    (make-child
	      (append 
		ref-assums
		(list (declaration
			nil p
			(function-term
			  'FUNCTION nil nil phi Ui))
		      (declaration
			nil h
			(function-term
			  'FUNCTION nil z phi-subset adjusted-G))
		      (declaration
			nil z
			(substitute
			  phi-body
			  (list (list phi-id phi-subset))))))
	      (equal-term 'EQUAL nil adjusted-G	d-equands))
	    (make-child
	      ref-assums
	      (equal-term
		'EQUAL nil phi t-equands))
	    (make-child
	      ref-assums
	      (equal-term 'EQUAL nil Ui (list phi))))))) 



(defun refine-eq-intro-recursive ()
    (let* ((using-term-list (using-term-list-of-equal-intro-rule-recursive ref-rule)))
      (check-concl$ 'RECURSIVE 'UNIVERSE)
      (Pif (fix-term-of-recursive-term (car (terms-of-equal-term ref-concl))) -->
	  (refine-eq-intro-recursive-with-fix using-term-list)
       || t -->
          (refine-eq-intro-recursive-without-fix using-term-list)
       fi)
    )
)

(defun refine-eq-intro-recursive-with-fix (using-term-list)
    (Plet (level           nil
	  rec-term-list   nil
	  fix-term-list   nil
	  term-list-list1 nil
	  term-list-list2 nil
	  bound-ids1      nil
	  fix-ids         nil
	  rec-ids         nil
	  subst-list      nil
	  rec-term        nil
	  selected        0
	 )
	(<- level (level-of-universe-term (type-of-equal-term ref-concl)))
	(<- rec-term (car (terms-of-equal-term ref-concl)))
	(<- rec-term-list (term-list-of-bound-id-list-term
			    (bound-id-list-term-of-recursive-term rec-term)
			  )
	)
	(<- fix-term-list (term-list-of-bound-id-list-term
			    (bound-id-list-term-of-fix-term
			      (fix-term-of-recursive-term rec-term)
			    )
			  )
	)
	(Pif (not (eql (length rec-term-list) (length using-term-list))) -->
	    (ref-error '| using term list not of correct length |)
	 fi)
	(for (x in using-term-list)
	     (do
	       (Pif (not (eql (kind-of-term x) 'PARFUNCTION)) -->
		   (ref-error '|terms in 'using' list must all be of form w:A+>B |)
	        fi)
	       (check-all-free-vars-declared x)
	     )
	)
	(<- selected (selected-position rec-term))
	(for (z in (cdr (terms-of-equal-term ref-concl)))
	     (do
	       (Pif (not (eql selected (selected-position z))) -->
		   (ref-error (concat '|The selecting ids must occur at the same|
				      '| relative position in all rec terms. |
			      )
		   )
	       fi)
	       (Pif (not (eql (length using-term-list)
			    (length
			      (bound-ids-of-bound-id-list-term
				(bound-id-list-term-of-recursive-term z)
			      )
			    )
			)
		   ) --> (ref-error '|all rec terms must have the same number if subterms. |)
		fi)
	     )
	)
	(<- rec-ids (bound-ids-of-bound-id-list-term
		      (bound-id-list-term-of-recursive-term rec-term)
	            )
	)
	(<- fix-ids (bound-ids-of-bound-id-list-term
		      (bound-id-list-term-of-fix-term (fix-term-of-recursive-term rec-term))
	            )
	)
	(<- bound-ids1
	    (for (x in rec-term-list)
		 (save
		   (car (bound-ids-of-bound-id-term x))
		 )
	    )
	)
	(<- subst-list (for (x in rec-ids)
			    (z in fix-ids)
			    (save
			      (list x (dom-term 'DOM nil (var-term 'VAR nil z)))
			    )
		       )
	)
	(<- term-list-list1
	    (make-term-list-list$
	      (mapcar #'bound-id-list-term-of-recursive-term
		      (terms-of-equal-term ref-concl)
	      )
	    )
	)
	(<- term-list-list2
	    (make-term-list-list$
	      (mapcar #'bound-id-list-term-of-fix-term
		      (terms-of-equal-term ref-concl)
	      )
	    )
	)
	(<- term-list-list1
	    (for (z in term-list-list1)
		 (save
	           (mapcar #'(lambda (x) (substitute x subst-list)) z)
		 )
	    )
	)
        (<- ref-children 
          (append
	    (for (x in using-term-list)
		 (save
		   (make-child
		     ref-assums
		     (equal-term
		       'EQUAL
		       nil
		       (type-of-equal-term ref-concl)
		       (list x)
		     )
		   )
		 )
	    )
            (Plet (assum-segment
		   (for (y in using-term-list)
	                (z in (bound-ids-of-bound-id-list-term
				(bound-id-list-term-of-fix-term
				  (fix-term-of-recursive-term rec-term)
				)
			      )
			)
	                (save
	                   (declaration nil z y)
 	                )
	            )
		 )
		 (append (for (y in using-term-list)
			      (w in term-list-list1)
			      (x in bound-ids1)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment
					  (list
					    (declaration
					      nil x (lefttype-of-parfunction-term y)
					    )
					  )
				  )
				  (equal-term 'EQUAL nil (type-of-equal-term ref-concl) w)
				)
			      )
			 )
			 (for (z in fix-term-list)
			      (w in term-list-list2)
			      (r in rec-term-list)
			      (y in using-term-list)
			      (x in bound-ids1)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment
					  (list
					    (declaration nil
							 (car (bound-ids-of-bound-id-term z))
							 (lefttype-of-parfunction-term y)
					    )
					    (declaration nil
							 nil
							 (substitute
							   (term-of-bound-id-term r)
							   (cons
							     (list
							      x
							      (var-term 'VAR nil
								(car (bound-ids-of-bound-id-term z))
							      )
							     )
							     subst-list
							   )
							 )
					    )
					  )
				  )
				  (equal-term
				    'EQUAL
				    nil
				    (substitute
				      (righttype-of-parfunction-term y)
				      (list
					(list
					  (car (bound-ids-of-bound-id-term z))
					  (var-term 'VAR nil (bound-id-of-parfunction-term y))
					)
				      )
				    )
				    w
				  )
				)
			      )
			 )
			 (list
			   (make-child
			     ref-assums
			     (equal-term
			       'EQUAL
			       nil
			       (lefttype-of-parfunction-term
				 (nth selected using-term-list)
			       )
			       (mapcar #'term-of-recursive-term
				       (terms-of-equal-term ref-concl)
			       )
			     )
			   )
			 )
		 )

	    )
          )
        )
    )
    nil
)

(defun refine-eq-intro-recursive-without-fix (using-term-list)
    (Plet (level           nil
	  rec-term-list   nil
	  term-list-list1 nil
	  bound-ids1      nil
	  ids             nil
	  rec-term        nil
	  selected        0
	 )
	(<- level (level-of-universe-term (type-of-equal-term ref-concl)))
	(<- rec-term (car (terms-of-equal-term ref-concl)))
	(<- rec-term-list (term-list-of-bound-id-list-term
			    (bound-id-list-term-of-recursive-term rec-term)
			  )
	)
	(Pif (not (eql (length rec-term-list) (length using-term-list))) -->
	    (ref-error '| using term list not of correct length |)
	 fi)
	(for (x in using-term-list)
	     (do
	       (check-all-free-vars-declared x)
	     )
	)
	(<- selected (selected-position rec-term))
	(for (z in (cdr (terms-of-equal-term ref-concl)))
	     (do
	       (Pif (not (eql selected (selected-position z))) -->
		   (ref-error (concat '|The selecting ids must occur at the same|
				      '| relative position in all rec terms. |
			      )
		   )
	       fi)
	       (Pif (not (eql (length using-term-list)
			    (length
			      (bound-ids-of-bound-id-list-term
				(bound-id-list-term-of-recursive-term z)
			      )
			    )
			)
		   ) --> (ref-error '|all rec terms must have the same number if subterms. |)
		fi)
	     )
	)
	(<- ids (bound-ids-of-bound-id-list-term
		  (bound-id-list-term-of-recursive-term rec-term)
	        )
	)
	(<- bound-ids1
	    (for (x in rec-term-list)
		 (save
		   (car (bound-ids-of-bound-id-term x))
		 )
	    )
	)
	(<- term-list-list1
	    (make-term-list-list$
	      (mapcar #'bound-id-list-term-of-recursive-term
		      (terms-of-equal-term ref-concl)
	      )
	    )
	)
        (<- ref-children 
          (append
	    (for (x in using-term-list)
		 (save
		   (make-child
		     ref-assums
		     (equal-term
		       'EQUAL
		       nil
		       (type-of-equal-term ref-concl)
		       (list x)
		     )
		   )
		 )
	    )
            (Plet (assum-segment
		   (for (y in using-term-list)
	                (g in ids)
	                (save
	                   (declaration
			     nil
			     g
			     (function-term
				'FUNCTION nil nil y (universe-term 'UNIVERSE nil level)
			     )
	                    )  
	                 )
	           )
		 )
		 (append (for (y in using-term-list)
			      (w in term-list-list1)
			      (x in bound-ids1)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment
					  (list
					    (declaration nil x y)
					  )
				  )
				  (equal-term 'EQUAL nil (type-of-equal-term ref-concl) w)
				)
			      )
			 )
			 (list
			   (make-child
			     ref-assums
			     (equal-term
			       'EQUAL
			       nil
			       (nth selected using-term-list)
			       (mapcar #'term-of-recursive-term
				       (terms-of-equal-term ref-concl)
			       )
			     )
			   )
			 )
		 )

	    )
          )
        )
    )
    nil
)






(defun refine-eq-intro-simple-rec ()
    (check-concl$ 'SIMPLE-REC 'UNIVERSE)
    (let* ((equands (terms-of-equal-term ref-concl))
	   (universe (type-of-equal-term ref-concl))
	   (rec-type (first equands))
	   (hyp-tag (or (new-id-of-equal-intro-rule-simple-rec ref-rule)
			(bound-id-of-simple-rec-term rec-type)))
	   (hyp-tag-var (var-term 'VAR nil hyp-tag))
	   (new-equands
	     (mapcar
	       #'(lambda (x)
		   (substitute (term-of-simple-rec-term x)
			       `((,(bound-id-of-simple-rec-term x) ,hyp-tag-var))))
	       equands)))
      (mapc #'(lambda (x)
		(cond ((not (occurs-positively (bound-id-of-simple-rec-term x)
					       (term-of-simple-rec-term x)))
		       (ref-error '|body of recursive type is illegal|))))
	    equands)
      (<- ref-children
	  (list
	    (make-child
	      (append
		ref-assums
		(list (declaration nil hyp-tag universe)))
	      (equal-term 'EQUAL nil universe new-equands)))))) 





(defun selected-position (term)
    (Pif (eql (kind-of-term term) 'FIX) -->
	(position
	  (id-of-fix-term term)
	  (bound-ids-of-bound-id-list-term (bound-id-list-term-of-fix-term term))
	)

     || (eql (kind-of-term term) 'RECURSIVE) -->
        (position
	  (id-of-recursive-term term)
	  (bound-ids-of-bound-id-list-term (bound-id-list-term-of-recursive-term term))
	)

     || (eql (kind-of-term term) 'REC-IND) -->
        (position
	  (id-of-rec-ind-term term)
	  (bound-ids-of-bound-id-list-term (bound-id-list-term-of-rec-ind-term term))
	)
      
     fi)
)


;;-
(defun make-term-list-list$ (bound-id-list-term-list)
    (Plet (term-list1 (term-list-of-bound-id-list-term (car bound-id-list-term-list))
	  bound-ids1 (bound-ids-of-bound-id-list-term (car bound-id-list-term-list))
	  ids1       nil
         )
	 (<- ids1 (for (z in term-list1)
		       (save
			 (car (bound-ids-of-bound-id-term z))
		       )
		  )
	 )
	 (match-ordered-terms$
            (cons
	       (mapcar #'term-of-bound-id-term term-list1)
	       (for (z in (cdr bound-id-list-term-list))
		    (save
		      (for (y in ids1)
			   (w in (term-list-of-bound-id-list-term z))
			   (save
			     (substitute
			       (term-of-bound-id-term w)
			       (make-bindings$
			          (cons y bound-ids1)
			          (cons (car (bound-ids-of-bound-id-term w))
				        (bound-ids-of-bound-id-list-term z)
			          )
			       )
			     )
		           )
		      )
		    )
	       )
	    )
	 )
    )
)

(defun match-ordered-terms$ (term-list-list)
    (Pif (null (car term-list-list)) -->
	nil
     || t -->
        (cons (mapcar #'car term-list-list)
	      (match-ordered-terms$ (mapcar #'cdr term-list-list))
        )
     fi)
)

(defun make-assum-segment1 (using-term-list bound-id-list-term new-ids level)
    (Plet (term-list (term-list-of-bound-id-list-term bound-id-list-term)
	  ids       (bound-ids-of-bound-id-list-term bound-id-list-term)
	 )
    (append
       (for (y in using-term-list)
	    (z in ids)
	    (save
	      (declaration nil z y)
	    )
	)
	(for (y in using-term-list)
	     (g in new-ids)
	     (save
	       (declaration nil
			    g
			    (function-term
				'FUNCTION
				 nil
				 nil
				 (lefttype-of-parfunction-term y)
				 (universe-term
				     'UNIVERSE
				      nil
				      level
				 )
			     )
	       )  
	     )
	)

	(for (y in using-term-list)
	     (z in term-list)
	     (g in new-ids)
	     (f in ids)
	     (save
	       (declaration
		 nil
		 nil
		 (function-term
		   'FUNCTION
		   nil
		   (car (bound-ids-of-bound-id-term z))
		   (lefttype-of-parfunction-term y)
		   (function-term
		     'FUNCTION
		     nil
		     nil
		     (apply-term
		       'APPLY
		       nil
		       (var-term 'VAR nil g)
		       (var-term 'VAR
				 nil
				 (car
				   (bound-ids-of-bound-id-term z)
				   )
				 )
		       )
		     (equal-term
		       'EQUAL
		       nil
		       (substitute
			 (righttype-of-parfunction-term y)
			 (list
			   (list
			     (car (bound-ids-of-bound-id-term z))
			     (var-term 'VAR nil (bound-id-of-parfunction-term y))
			     )
			   )
			 )
		       (list
			 (apply-partial-term
			   'APPLY-PARTIAL
			   nil
			   (var-term 'VAR nil f)
			   (var-term 'VAR
				     nil
				     (car
				       (bound-ids-of-bound-id-term z)
				       )
				     )
			   )
			 )
		       )
		     
		     )
		   
		   )
		 )
	       )
	     )
       )
    )
)

(defun make-assum-segment2 (using-term-list
			 over-pair-list
			 rec-term-list
			 fix-term-list
			 rec-ind-id-list
			 level
			)
    (append
      (for (w in using-term-list)
	   (v in (bound-ids-of-bound-id-list-term rec-term-list))
	 (save
	   (declaration
	     nil
	     v
	     (function-term
	       'FUNCTION
	       nil
	       nil
	       (righttype-of-parfunction-term w)
	       (universe-term 'UNIVERSE nil level)
	     )
	   )
	 )
      )
      (for (w in using-term-list)
	   (v1 in (bound-ids-of-bound-id-list-term rec-term-list))
	   (v2 in (term-list-of-bound-id-list-term rec-term-list))
	   (z in over-pair-list)
	   (x in (bound-ids-of-bound-id-list-term fix-term-list))
	   (save
	     (declaration
	       nil
	       nil
	       (function-term
		 'FUNCTION
		 nil
		 (car z)
		 (product-term
		   'PRODUCT
		   nil
		   (car (bound-ids-of-bound-id-term v2))
		   (lefttype-of-parfunction-term w)
		   (apply-term
		     'APPLY
		     nil
		     (var-term 'VAR nil v1)
		     (var-term 'VAR nil (car (bound-ids-of-bound-id-term v2)))
		   )
		 )
		 (equal-term
		   'EQUAL
		   nil
		   (product-term
		     'PRODUCT
		     nil
		     (car (bound-ids-of-bound-id-term v2))
		     (lefttype-of-parfunction-term w)
		     (recursive-term
		       'RECURSIVE
		       nil
		       rec-term-list
		       (fix-term
			 'FIX
			 nil
			 fix-term-list
			 x
		       )
		       v1
		       (var-term 'VAR nil (car (bound-ids-of-bound-id-term v2)))
		     )
		   )
		   (list (var-term 'VAR nil (car z)))
		 )
	       )
	     )
	   )
      )
      (for (v in (bound-ids-of-bound-id-list-term rec-term-list))
	   (z in using-term-list)
	   (x1 in (bound-ids-of-bound-id-list-term fix-term-list))
	   (x2 in (term-list-of-bound-id-list-term fix-term-list))
	   (save
	     (declaration
	       nil
	       nil
	       (function-term
		 'FUNCTION
		 nil
		 nil
		 (function-term
		   'FUNCTION
		   nil
		   (car (bound-ids-of-bound-id-term x2))
		   (lefttype-of-parfunction-term z)
		   (apply-term
		     'APPLY
		     nil
		     (var-term 'VAR nil v)
		     (var-term 'VAR nil (car (bound-ids-of-bound-id-term x2)))
		   )
		 )
		 (equal-term
		   'EQUAL
		   nil
		   (substitute
		     (righttype-of-parfunction-term z)
		     (list
		       (list (bound-id-of-parfunction-term z)
			     (var-term 'VAR nil (car (bound-ids-of-bound-id-term x2)))
		       )
		     )
		   )
		   (list
		     (apply-partial-term
		       'APPLY-PARTIAL
		       nil
		       (fix-term
		         'FIX
		         nil
		         fix-term-list
		         x1
		       )
		       (var-term 'VAR nil (car (bound-ids-of-bound-id-term x2)))
		     )
		   )
		 )
	       )
	     )
	   )
      )
      (for (v1 in (bound-ids-of-bound-id-list-term rec-term-list))
	   (v2 in (term-list-of-bound-id-list-term rec-term-list))
	   (z in over-pair-list)
	   (w in using-term-list)
	   (x in rec-ind-id-list)
	   (save
	     (declaration
	       nil
	       x
	       (function-term
		 'FUNCTION
		 nil
		 (car z)
		 (product-term
		   'PRODUCT
		   nil
		   (car (bound-ids-of-bound-id-term v2))
		   (lefttype-of-parfunction-term w)
		   (apply-term
		     'APPLY
		     nil
		     (var-term 'VAR nil v1)
		     (var-term 'VAR nil (car (bound-ids-of-bound-id-term v2)))
		   )
		 )
		 (cdr z)
	       )
	     )
	   )
      )
    )
)

(defun make-assum-segment3 (using-term-list
			 over-pair-list
			 rec-term-list
			 rec-ind-id-list
			 level
			)
    (append
      (for (w in using-term-list)
	   (v in (bound-ids-of-bound-id-list-term rec-term-list))
	 (save
	   (declaration
	     nil
	     v
	     (function-term
	       'FUNCTION
	       nil
	       nil
	       w
	       (universe-term 'UNIVERSE nil level)
	     )
	   )
	 )
      )
      (for (w in using-term-list)
	   (v1 in (bound-ids-of-bound-id-list-term rec-term-list))
	   (v2 in (term-list-of-bound-id-list-term rec-term-list))
	   (z in over-pair-list)
	   (save
	     (declaration
	       nil
	       nil
	       (function-term
		 'FUNCTION
		 nil
		 (car z)
		 (product-term
		   'PRODUCT
		   nil
		   (car (bound-ids-of-bound-id-term v2))
		   w
		   (apply-term
		     'APPLY
		     nil
		     (var-term 'VAR nil v1)
		     (var-term 'VAR nil (car (bound-ids-of-bound-id-term v2)))
		   )
		 )
		 (equal-term
		   'EQUAL
		   nil
		   (product-term
		     'PRODUCT
		     nil
		     (car (bound-ids-of-bound-id-term v2))
		     w
		     (recursive-term
		       'RECURSIVE
		       nil
		       rec-term-list
		       nil
		       v1
		       (var-term 'VAR nil (car (bound-ids-of-bound-id-term v2)))
		     )
		   )
		   (list (var-term 'VAR nil (car z)))
		 )
	       )
	     )
	   )
      )
      
      (for (v1 in (bound-ids-of-bound-id-list-term rec-term-list))
	   (v2 in (term-list-of-bound-id-list-term rec-term-list))
	   (z in over-pair-list)
	   (w in using-term-list)
	   (x in rec-ind-id-list)
	   (save
	     (declaration
	       nil
	       x
	       (function-term
		 'FUNCTION
		 nil
		 (car z)
		 (product-term
		   'PRODUCT
		   nil
		   (car (bound-ids-of-bound-id-term v2))
		   w
		   (apply-term
		     'APPLY
		     nil
		     (var-term 'VAR nil v1)
		     (var-term 'VAR nil (car (bound-ids-of-bound-id-term v2)))
		   )
		 )
		 (cdr z)
	       )
	     )
	   )
      )
    )
)



(defun refine-eq-intro-object-member ()
    (check-concl-kind$)
    (check-type-kind$ 'OBJECT)
    (let* ((using (using-term-of-equal-intro-rule-using ref-rule))
	   (equands (terms-of-equal-term ref-concl)))
      (cond ((Pevery #'(lambda (x) (member (kind-of-term x) canonical-terms)) equands)
	     (<- ref-children nil))
	    ((< 1 (length equands))
	     (<- ref-children
		 (mapcar #'(lambda (equand)
			     (make-child ref-assums
					 (equal-term 'EQUAL nil (object-term 'OBJECT nil) (list equand))))
			 equands)))
	    ((null using)
	     (ref-error '|Need a using term.|))
	    (t
	     (<- ref-children (list (make-child ref-assums (equal-term 'EQUAL nil using equands))))))))
