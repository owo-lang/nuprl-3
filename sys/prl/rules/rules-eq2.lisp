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


(defun refine-eq-intro-spread ()    
    (Plet (over-term nil
          over-id   nil
          new-id1   nil
          new-id2   nil
	  new-id-list (new-ids-of-equal-intro-rule-using ref-rule)
          using-term (using-term-of-equal-intro-rule-using ref-rule)
          using-bound-id nil
          value     (value-of-spread-term (car (terms-of-equal-term ref-concl)))
         )
        (check-concl-kind$)
        (check-terms-kind$ 'SPREAD)
	(Pif (not (eql (kind-of-term using-term) 'PRODUCT)) -->
	    (ref-error '|using term must be a product term|) fi)
        (check-all-free-vars-declared using-term)
	(multiple-value-setq (new-id1 new-id2) (check-ids 0 2 new-id-list))
	(Pif (and (null new-id1) (null new-id2)) -->
	    (multiple-value-setq (new-id1 new-id2)
	        (values-list
		    (bound-ids-of-bound-id-term 
		        (term-of-spread-term (car (terms-of-equal-term ref-concl)))
                    )
		)
	    )
	    (check-if-new$ new-id1 ref-assums)
	    (check-if-new$ new-id2 ref-assums)	
	 || (or (null new-id1) (null new-id2)) -->
	    (ref-error '|two new ids must be given|)
	 fi)

        (<- using-bound-id (bound-id-of-product-term using-term))
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
                            (mapcar #'value-of-spread-term
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
                                       (lefttype-of-product-term using-term)            
                                  )
                                  (declaration
                                       nil
                                       new-id2
                                       (substitute
                                         (righttype-of-product-term using-term)
                                         (list (list using-bound-id
                                                     (var-term
                                                        'VAR
                                                        nil
                                                        new-id1
                                                     )
                                               )
                                         )
                                       )
                                  )
				  (declaration
				    nil nil
				    (equal-term
				      'EQUAL nil
				      using-term
				      (list
					(pair-term
					  'PAIR nil
					  (var-term 'VAR nil new-id1)
					  (var-term 'VAR nil new-id2)
					)
					(value-of-spread-term
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
                                                 (pair-term 
                                                    'PAIR
                                                     nil
                                                     (var-term 'VAR nil new-id1)
                                                     (var-term 'VAR nil new-id2)
                                                  )
                                              )
                                        )
                            )
                            (substitute-n-in-all-terms$ 
                                (list new-id1 new-id2)
                                (mapcar #'(lambda (x)                   
                                            (bound-ids-of-bound-id-term
                                                    (term-of-spread-term x)
                                            )
                                         )
                                        (terms-of-equal-term ref-concl)
                                )
                                (mapcar #'(lambda (x) 
                                            (term-of-bound-id-term
                                                    (term-of-spread-term x)
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

(defun refine-eq-intro-function ()
    (check-concl$ 'FUNCTION 'UNIVERSE)
    (Plet (new-id
	     (Pif (null (new-id-of-equal-intro-rule-new-id ref-rule)) -->
		 (get-first-non-nil-id$
		     (mapcar #'bound-id-of-function-term
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
			      (mapcar #'lefttype-of-function-term
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
				      (lefttype-of-function-term
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
				(mapcar #'bound-id-of-function-term
					(terms-of-equal-term ref-concl)
				)
				(mapcar #'righttype-of-function-term
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



(defun refine-eq-intro-lambda ()
    (check-concl$ 'LAMBDA 'FUNCTION)
    (Plet (new-id
	     (Pif (null (new-id-of-equal-intro-rule-level ref-rule)) -->
		 (bound-id-of-lambda-term (car (terms-of-equal-term ref-concl)))
	      || t -->
	         (new-id-of-equal-intro-rule-level ref-rule)
	      fi)
	  )
	(check-if-new$ new-id ref-assums)
	(<- ref-children (list (make-child
				  (append 
				     ref-assums
				     (list
				       (declaration 
					 nil
					 new-id
					 (lefttype-of-function-term
						     (type-of-equal-term ref-concl)
					 )
				       )
				     )
				  )
				  (equal-term
				     'EQUAL
				     nil
				     (substitute
					  (righttype-of-function-term 
						     (type-of-equal-term ref-concl)
					  )
					  (list (list
						  (bound-id-of-function-term
							(type-of-equal-term ref-concl)
						  )                                 
						  (var-term 'VAR nil new-id) 
						)
					  )
				     )
				     (substitute-in-all-terms$     
				       new-id
				       (mapcar 
					   #'bound-id-of-lambda-term
					   (terms-of-equal-term ref-concl)
				       )
				       (mapcar
					   #'term-of-lambda-term
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
					(universe-term
					  'UNIVERSE
					  nil
					  (level-of-equal-intro-rule-level ref-rule)
					)
					(list (lefttype-of-function-term 
						     (type-of-equal-term ref-concl)
					      )
					)
				    )
			       )
			 )
	)
    )
    nil
)


;;; The new extensionality rule (works for n equands, n1):
;;; 
;;; >> f = g in x:A->B  BY extensionality [at Ui] [using x':A'->B', x'':A''->B''] [new z]
;;;   z:A >> f(z) = g(z) in B[z/x]
;;;       >> A in Ui
;;;       >> f in x':A'->B''
;;;       >> g in x'':A''->B''
;;;
;;;
(defun refine-extensionality ()
    (cond ((or (not (eql (kind-of-term ref-concl) 'EQUAL))
	       (not (eql (kind-of-term (type-of-equal-term ref-concl)) 'FUNCTION)))
	   (ref-error '|Extensionality only works for equalities over function types|)))
    (let*
      ((equands (terms-of-equal-term ref-concl))
       (new-id
	 (cond ((null (new-id-of-extensionality-rule ref-rule))
		(bound-id-of-function-term (type-of-equal-term ref-concl)))
	       (t
		(new-id-of-extensionality-rule ref-rule))))
       (function-type (type-of-equal-term ref-concl))
       (using-terms
	 (or (using-terms-of-extensionality-rule ref-rule)
	     (mapcar #'(lambda (x) function-type) equands)))
       (level (level-of-extensionality-rule ref-rule))
       (concl-of-main-subgoal
	 (equal-term
	   'EQUAL nil
	   (substitute (righttype-of-function-term function-type)
		       (list (list
			       (bound-id-of-function-term function-type)
			       (var-term 'VAR nil new-id))))
	   (mapcar #'(lambda (term) (apply-term 'APPLY nil
						term (var-term 'VAR nil new-id)))
		   equands)))
       (main-subgoal
	 (make-child
	   (append ref-assums
		   (list (declaration nil new-id
				      (lefttype-of-function-term function-type))))
	   concl-of-main-subgoal))
       (wf-subgoal
	 (make-child ref-assums
		     (equal-term 'EQUAL nil (universe-term 'UNIVERSE nil level)
				 (list (lefttype-of-function-term function-type)))))
       (membership-subgoals
	 (mapcar #'(lambda (f using)
		     (make-child ref-assums
				 (equal-term 'EQUAL nil using (list f))))
		 equands
		 using-terms)))
      (cond ((null new-id)
	     (ref-error '|A new id must be given|)))
      (cond ((find-if #'(lambda (term) (not (eql (kind-of-term term) 'FUNCTION))) using-terms)
	     (ref-error '|Using terms must be function types.|)))
      (check-if-new$ new-id ref-assums)
      (cond ((not (eql (length using-terms)
		       (length (terms-of-equal-term ref-concl))))
	     (ref-error '|Number of using terms must match number of equands.|)))
      (<- ref-children
	  `(,main-subgoal
	    ,wf-subgoal
	    ,@membership-subgoals))))


;(defun refine-extensionality ()
;    (Pif (or
;	    (not (eql (kind-of-term ref-concl) 'EQUAL))
;	    (not (eql (kind-of-term (type-of-equal-term ref-concl)) 'FUNCTION))
;	) -->
;	(ref-error '|Extensionality only works for equalities over function types|)
;     fi)
;    (Plet (new-id
;	    (Pif (null (new-id-of-extensionality-rule ref-rule)) -->
;		(bound-id-of-function-term
;		    (type-of-equal-term ref-concl)
;		)
;	     || t -->
;	        (new-id-of-extensionality-rule ref-rule)
;	     fi)
;	  function-type (type-of-equal-term ref-concl)
;	 )
;        (Pif (null new-id) --> (ref-error '|A new id must be given|) fi)
;        (check-if-new$ new-id ref-assums)
;	(<- ref-children
;	    (cons
;	        (make-child
;		    (append
;		        ref-assums
;			(list
;			    (declaration
;			        nil
;				new-id
;				(lefttype-of-function-term function-type)
;			     )
;			 )
;		     )
;		     (equal-term
;		         'EQUAL nil
;			 (substitute
;			     (righttype-of-function-term function-type)
;			     (list
;			         (list
;				     (bound-id-of-function-term function-type)
;				     (var-term 'VAR nil new-id)
;				 )
;			      )
;			  )
;			  (mapcar
;			      #'(lambda (term)
;				  (apply-term 'APPLY nil
;				     term (var-term 'VAR nil new-id)
;				  )
;				)
;			      (terms-of-equal-term ref-concl)
;			  )
;		      )
;		 )
;		(mapcar
;		  #'(lambda (f)
;		      (make-child
;			ref-assums
;			(equal-term 'EQUAL nil
;			  (type-of-equal-term ref-concl)
;			  (list f))))
;		  (terms-of-equal-term ref-concl)))
;	)
;    )
;)

(defun refine-eq-intro-apply ()
  (let* ((using-term (using-term-of-equal-intro-rule-using ref-rule)))
    (check-concl-kind$)
    (check-terms-kind$ 'APPLY)
    (Pif (not (eql (kind-of-term using-term) 'FUNCTION)) -->
	(ref-error '|using term must be a function term|) fi)
    (check-all-free-vars-declared using-term)
    (Pif (not (equal-terms (type-of-equal-term ref-concl)
                          (substitute                   
                            (righttype-of-function-term 
                                using-term
                            )
                            (list
                             (list
                               (bound-id-of-function-term
                                 using-term
                               )
                               (arg-of-apply-term 
                                         (car (terms-of-equal-term ref-concl))
                               )
                             )
                            )
                          )
             )
        ) -->                 
        (ref-error (concat '|type of the equal term must correspond with the |
                           '|righttype of the function-term following 'using' |
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
                                      #'function-of-apply-term
                                      (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                           (make-child
                                ref-assums
                                (equal-term
                                    'EQUAL
                                    nil
                                    (lefttype-of-function-term 
                                        (using-term-of-equal-intro-rule-using
                                                                        ref-rule
                                        )
                                    ) 
                                    (mapcar #'arg-of-apply-term
                                            (terms-of-equal-term ref-concl)
                                    )
                                )
                           )
                     )
    )
  )
  nil
)




(defun refine-eq-intro-quotient ()
    (Plet (new-ids (new-ids-of-equal-intro-rule-quotient ref-rule)
          terms   nil
          type    nil
         )
        (check-concl$ 'QUOTIENT 'UNIVERSE)
        (<- terms (terms-of-equal-term ref-concl))
        (<- type (type-of-equal-term ref-concl))
        (Pif (onep (length terms)) -->
            (<- ref-children 
                (children-for-unary$ new-ids (car terms) type)
            )

         || t -->
            (<- ref-children (children-for-n-ary$ new-ids terms type))

         fi)
    )                
    nil
)

(defun children-for-unary$ (new-ids term type)
    (Plet (lefttype  (lefttype-of-quotient-term term)
          new-id1 nil
          new-id2 nil
          new-id3 nil
          decl1   nil
          decl2   nil
          decl3   nil
         )           
        (Pif (not (= (length new-ids) 3)) -->
            (ref-error '|must give 3 new ids for this rule|)
         fi)      
        (check-if-all-new$ new-ids ref-assums)
        (<- new-id1 (car new-ids))
        (<- new-id2 (cadr new-ids))
        (<- new-id3 (caddr new-ids))                  
        (<- decl1 (declaration nil new-id1 lefttype))
        (<- decl2 (declaration nil new-id2 lefttype))
        (<- decl3 (declaration nil new-id3 lefttype))
        (list (make-child
                    ref-assums
                    (equal-term 'EQUAL nil type (list lefttype))
              )
              (make-child                  
                    (append ref-assums (list decl1 decl2))
                    (equal-term 'EQUAL
                                nil
                                type
                                (list (quo-sub$ term new-id1 new-id2))
                    )
              )
              (make-child
                    (append ref-assums (list decl1))
                    (quo-sub$ term new-id1 new-id1)
              )
              (make-child 
                    (append ref-assums 
                            (list decl1 
                                  decl2
                                  (declaration
                                      nil nil (quo-sub$ term new-id1 new-id2)
                                  )
                            )
                    )
                    (quo-sub$ term new-id2 new-id1)
              )
              (make-child
                    (append ref-assums
                            (list decl1
                                  decl2
                                  decl3
                                  (declaration
                                    nil nil (quo-sub$ term new-id1 new-id2)
                                  )
                                  (declaration
                                    nil nil (quo-sub$ term new-id2 new-id3)
                                  )
                            )
                    )
                    (quo-sub$ term new-id1 new-id3)
              )
        )
    )
)

(defun children-for-n-ary$ (new-ids terms type)
    (Plet (new-id1      nil
          new-id2      nil
          leftterms    (mapcar #'lefttype-of-quotient-term
                               terms
                       )
          leftterm     (lefttype-of-quotient-term (car terms))
          children     nil
         )
        (Pif (not (= (length new-ids) 2)) -->
            (ref-error '|must give 2 new-ids for this rule|)
         fi)           
        (check-if-all-new$ new-ids ref-assums)
        (<- new-id1 (car new-ids))
        (<- new-id2 (cadr new-ids))
        (Ploop (local tempterms terms)
              (while (cdr tempterms))
              (do     
                 (<- children 
                     (cons (make-child
                               (append ref-assums
                                       (list (declaration nil 
                                                          nil 
                                                          (equal-term
                                                                'EQUAL
                                                                nil
                                                                type
                                                                leftterms
                                                          )
                                             )
                                             (declaration nil new-id1 leftterm)
                                             (declaration nil new-id2 leftterm)
                                       )
                               )          
                               (function-term 
                                    'FUNCTION
                                    nil
                                    nil
                                    (quo-sub$ (car tempterms) new-id1 new-id2)
                                    (quo-sub$ (cadr tempterms) new-id1 new-id2)
                               )
                           )
                           children 
                     )
                 )
                 (<- tempterms (cdr tempterms))
              )
              (result (<- children
                          (cons (make-child
                                  (append 
                                       ref-assums
                                       (list (declaration nil 
                                                          nil 
                                                          (equal-term
                                                                'EQUAL
                                                                nil
                                                                type
                                                                leftterms
                                                          )
                                             )
                                             (declaration nil new-id1 leftterm)
                                             (declaration nil new-id2 leftterm)
                                       )
                                  )          
                                  (function-term 
                                    'FUNCTION
                                    nil
                                    nil
                                    (quo-sub$ (car tempterms) new-id1 new-id2)
                                    (quo-sub$ (car terms) new-id1 new-id2)
                                  )
                                )
                                children
                          )
                      )
              )
        )
        (for (term in terms)
             (do
                (<- children 
                    (cons (make-child
                                ref-assums             
                                (equal-term 'EQUAL
                                            nil
                                            type
                                            (list term)
                                )
                          )
                          children
                    )
                )
             ) 
        )      
        (<- children (cons (make-child
                                ref-assums
                                (equal-term 'EQUAL
                                            nil
                                            type
                                            leftterms
                                )
                           )
                           children
                     )
        )
  
        children
    )
)

(defun quo-sub$ (term sub1 sub2)
    (substitute (righttype-of-quotient-term term)
                (list (list
                        (car (bound-ids-of-quotient-term term))
                        (var-term 'VAR nil sub1)
                      )
                      (list
                        (cadr (bound-ids-of-quotient-term term))
                        (var-term 'VAR nil sub2)
                      )
                )
    )
)

(defun refine-eq-intro-quotient-elem ()       
    (Plet (level     (level-of-equal-intro-rule-level ref-rule)
          lefttype  nil
          bound-id1 nil
          bound-id2 nil
         )
        (check-concl-kind$)
        (check-type-kind$ 'QUOTIENT)
        (<- lefttype (lefttype-of-quotient-term (type-of-equal-term ref-concl)))
        (<- bound-id1 
            (car (bound-ids-of-quotient-term (type-of-equal-term ref-concl)))
        )
        (<- bound-id2 
            (cadr (bound-ids-of-quotient-term (type-of-equal-term ref-concl)))
        )
        (<- ref-children nil)                     
                                              
        (Ploop (local terms (terms-of-equal-term ref-concl))
              (while (cdr terms))
              (do
                (<- ref-children
                    (cons (make-child 
                                ref-assums
                                (substitute (righttype-of-quotient-term
                                                (type-of-equal-term ref-concl)
                                            )                                 
                                            (list (list bound-id1 (car terms))
                                                  (list bound-id2 (cadr terms))
                                            )
                                )
                          )
                          ref-children
                    )
                )
                (<- terms (cdr terms))
              )
        )
        (for (term in (terms-of-equal-term ref-concl))
             (do
                (<- ref-children 
                    (cons (make-child 
                                ref-assums
                                (equal-term 'EQUAL
                                            nil
                                            lefttype
                                            (list term)
                                )
                          )
                          ref-children
                    )
                )
             )
        )
        (<- ref-children 
            (cons (make-child 
                        ref-assums
                        (equal-term 'EQUAL
                                    nil
                                    (universe-term 'UNIVERSE nil level)
                                    (list (type-of-equal-term ref-concl))
                        )
                  )
                  ref-children
            )
        )
    )
    nil
)

(defun refine-eq-intro-set ()
  (declare (special *use-new-set-rules-p*))
    (Plet (new-id (new-id-of-equal-intro-rule-new-id ref-rule)
         )                                     
        (check-concl$ 'SET 'UNIVERSE)
        (Pif (null new-id) -->
            (<- new-id
                (get-first-non-nil-id$
                    (mapcar #'bound-id-of-set-term
                            (terms-of-equal-term ref-concl)
                    )
                )
            )
         fi)
        (check-if-new$ new-id ref-assums)
	(<- ref-children
	    (Pif (onep (length (terms-of-equal-term ref-concl))) -->
		(make-children-for-set-formation new-id)
	     || t -->
		(cond (*use-new-set-rules-p*
		       (make-children-for-new-set-equality new-id))
		      (t
		       (make-children-for-set-equality new-id)))
	     fi)
	)
	nil
    )
)

(defun make-children-for-set-formation (new-id)
    (Plet (set      (car (terms-of-equal-term ref-concl))
	  universe (type-of-equal-term ref-concl)
	 )
      (list
	(make-child
	  ref-assums
	  (equal-term
	    'EQUAL nil
	    universe
	    (list (lefttype-of-set-term set))
	  )
	)
	(make-child
	  (Pif (bound-id-of-set-term set) -->
	      (append1
		ref-assums
		(declaration nil new-id (lefttype-of-set-term set))
	      )
	   || t -->
	      ref-assums
	   fi)
	  (equal-term
	    'EQUAL nil
	    universe
	    (list
	      (substitute
	        (righttype-of-set-term set)
	        `((,(bound-id-of-set-term set) ,(var-term 'VAR nil new-id)))
	      )
	    )
	  )
	)
      )
    )
)

(defun make-children-for-set-equality (new-id)
    (Plet (new-assums
	   (Pif new-id -->
	       (append1
		 ref-assums
		 (declaration nil new-id
		   (lefttype-of-set-term (car (terms-of-equal-term ref-concl)))
		 )
	       )
	    || t -->
	       ref-assums
	    fi)
	  new-id-term (var-term 'VAR nil new-id)
	 )
       (cons
	 (make-child
	   ref-assums
	   (equal-term 
	     'EQUAL nil
	     (type-of-equal-term ref-concl)
	     (mapcar #'lefttype-of-set-term (terms-of-equal-term ref-concl))
	   )
	 )
	 (Ploop
	   (local
	     value     nil
	     to-do     (terms-of-equal-term ref-concl)
	   )
	   (while (not (null (cdr to-do))))
	   (do
	     (<- value
		 (cons
		   (make-child
		     new-assums
		     (make-function-term-for-set-equality
		       new-id-term (car to-do) (cadr to-do)
		     )
		   )
		   value
		 )
	     )
	     (<- to-do (cdr to-do))
	   )
	   (result
	     (nreverse
	       (cons
		 (make-child
		   new-assums
		   (make-function-term-for-set-equality
		     new-id-term (car to-do) (car (terms-of-equal-term ref-concl))
		   )
		 )
		 value
	       )
	     )
	   )
	 )
       )
     )
)

(defun make-children-for-new-set-equality (new-id)
    (Plet (new-assums
	   (Pif new-id -->
	       (append1
		 ref-assums
		 (declaration nil new-id
		   (lefttype-of-set-term (car (terms-of-equal-term ref-concl)))
		 )
	       )
	    || t -->
	       ref-assums
	    fi)
	  new-id-term (var-term 'VAR nil new-id)
	 )
       (list
	 (make-child
	   ref-assums
	   (equal-term 
	     'EQUAL nil
	     (type-of-equal-term ref-concl)
	     (mapcar #'lefttype-of-set-term (terms-of-equal-term ref-concl))
	   )
	 )
	 (make-child
	   new-assums
	   (equal-term 'EQUAL nil
		       (type-of-equal-term ref-concl) 
		       (mapcar
			 #'(lambda (x)
			     (substitute
			       (righttype-of-set-term x)
			       `((,(bound-id-of-set-term x) ,new-id-term))))
			 (terms-of-equal-term ref-concl))))
       )
     )
)

(defun make-function-term-for-set-equality (new-id-term term1 term2)
    (function-term
      'FUNCTION nil nil
      (substitute
	(righttype-of-set-term term1)
	`((,(bound-id-of-set-term term1) ,new-id-term))
      )
      (substitute
	(righttype-of-set-term term2)
	`((,(bound-id-of-set-term term2) ,new-id-term))
      )
    )
)

(defun refine-eq-intro-set-elem ()
    (check-concl-kind$)
    (check-type-kind$ 'SET)
    (let* ((terms  (terms-of-equal-term ref-concl))
           (type   (type-of-equal-term ref-concl))
           (level  (level-of-equal-intro-rule-level ref-rule))
	   (new-id (Pif (new-id-of-equal-intro-rule-level ref-rule) -->
		       (new-id-of-equal-intro-rule-level ref-rule)
		    || t -->
		       (bound-id-of-set-term type)
		    fi)))
      (check-if-new$ new-id ref-assums)
      (<- ref-children
	  (append
	    (list
	      (make-child
		ref-assums
		(equal-term
		  'EQUAL nil
		  (lefttype-of-set-term type)
		  terms))
	      (make-child
		ref-assums 
		(substitute
		  (righttype-of-set-term type)
		  (list (list (bound-id-of-set-term type) (car terms))))))
	    (Pif (bound-id-of-set-term type) -->
		(list
		  (make-child
		    (append1
		      ref-assums
		      (declaration nil new-id (lefttype-of-set-term type)))
		    (equal-term
		      'EQUAL nil
		      (universe-term 'UNIVERSE nil level)
		      (list
			(substitute
			  (righttype-of-set-term type)
			  `((,(bound-id-of-set-term type)
			     ,(var-term 'VAR nil new-id))))))))
	     || t -->
	        nil
	     fi)))
      nil
    )
)


(defun refine-eq-intro-universe ()
    (check-concl$ 'UNIVERSE 'UNIVERSE)
    (Pif (not (apply 'n-equal (list
                               (mapcar #'level-of-universe-term  
                                       (terms-of-equal-term ref-concl)
                               )
                             )
             )
        ) -->
        (ref-error
                '|not all of the levels of the U terms before 'in' are equal |
        )
     fi)
    (Pif (not (<
                 (level-of-universe-term (car (terms-of-equal-term ref-concl)))
                 (level-of-universe-term (type-of-equal-term ref-concl))
             )
        ) -->
        (ref-error (concat '|the level of the universe subterms in the |
                          '|equal-term must be less than the level of the type |
                   )
        )
     fi)
    nil
)

(defun refine-eq-intro-var ()
    (check-concl-kind$)
    (check-terms-kind$ 'VAR)
    (Pif (not (equal-terms 
                (type-of-declaration          
                    (car (nthcdr (1- (assum-id-to-assum-num 
                                         (id-of-var-term 
                                           (car (terms-of-equal-term ref-concl))
                                         )
                                         ref-assums
                                       )
                                  )
                                  ref-assums
                         )
                    )
                )
                (type-of-equal-term ref-concl)
             )
        ) -->
        (ref-error '|no assum declares the vars to be of the equal term's type|)
     fi)
    (Pif (not (n-equal (mapcar #'id-of-var-term 
                              (terms-of-equal-term ref-concl)
                      )
             )
        ) -->
        (ref-error 
            '|all of the terms of the equal term must be the same variable |
        )

     fi)     
)

(defun refine-eq-intro-pos-number ()
    (check-concl$ 'POS-NUMBER 'INT)
    (Pif (not (n-equal (mapcar #'number-of-pos-number-term
                              (terms-of-equal-term ref-concl)
                      )
             )
        ) -->
        (ref-error '|all of the number terms must be equal |)

     fi)
)

(defun refine-eq-intro-minus ()
    (check-concl$ 'MINUS 'INT)
    (<- ref-children 
        (list (make-child ref-assums             
                          (equal-term
                                'EQUAL
                                nil
                                (type-of-equal-term ref-concl)
                                (mapcar #'term-of-minus-term
                                        (terms-of-equal-term ref-concl)
                                )
                          )
              )
        )
    )
    nil
)

(defun refine-eq-intro-atomeq ()         
    (check-concl-kind$)
    (check-terms-kind$ 'ATOMEQ) 
    (<- ref-children 
        (list (make-child
                    ref-assums
                    (equal-term 
                        'EQUAL
                        nil
                        (atom-term 'ATOM nil)
                        (mapcar #'leftterm-of-decision-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )               
              (make-child                 
                    ref-assums
                    (equal-term 
                        'EQUAL
                        nil
                        (atom-term 'ATOM nil)
                        (mapcar #'rightterm-of-decision-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
              (make-child
                    (append ref-assums
                            (list 
                              (declaration
                                  nil
                                  nil
                                  (equal-term 
                                    'EQUAL
                                    nil
                                    (atom-term 'ATOM nil)
                                    (list
                                      (leftterm-of-decision-term
                                         (car (terms-of-equal-term ref-concl))
                                      )
                                      (rightterm-of-decision-term
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
                        (type-of-equal-term ref-concl)
                        (mapcar #'if-term-of-decision-term
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
                             nil
                             (function-term
                                'FUNCTION
                                nil
                                nil
                                (equal-term          
                                    'EQUAL
                                    nil
                                    (atom-term 'ATOM nil)
                                    (list
                                      (leftterm-of-decision-term             
                                        (car (terms-of-equal-term ref-concl))
                                      )
                                      (rightterm-of-decision-term
                                        (car (terms-of-equal-term ref-concl))
                                      )
                                    )
                                )
                                (void-term 'VOID nil)
                             )
                         )  
                       )
                    )
                    (equal-term
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (mapcar #'else-term-of-decision-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
        )
    )
)

(defun refine-eq-intro-inteq ()         
    (check-concl-kind$)
    (check-terms-kind$ 'INTEQ) 
    (<- ref-children 
        (list (make-child
                    ref-assums
                    (equal-term 
                        'EQUAL
                        nil
                        (int-term 'INT nil)
                        (mapcar #'leftterm-of-decision-term
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
                        (mapcar #'rightterm-of-decision-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
              (make-child
                    (append ref-assums
                            (list 
                              (declaration
                                  nil
                                  nil
                                  (equal-term 
                                    'EQUAL
                                    nil
                                    (int-term 'INT nil)
                                    (list
                                      (leftterm-of-decision-term
                                         (car (terms-of-equal-term ref-concl))
                                      )
                                      (rightterm-of-decision-term
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
                        (type-of-equal-term ref-concl)
                        (mapcar #'if-term-of-decision-term
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
                             nil
                             (function-term
                                'FUNCTION
                                nil
                                nil
                                (equal-term          
                                    'EQUAL
                                    nil
                                    (int-term 'INT nil)
                                    (list
                                      (leftterm-of-decision-term             
                                        (car (terms-of-equal-term ref-concl))
                                      )
                                      (rightterm-of-decision-term
                                        (car (terms-of-equal-term ref-concl))
                                      )
                                    )
                                )
                                (void-term 'VOID nil)
                             )
                         )  
                       )
                    )
                    (equal-term
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (mapcar #'else-term-of-decision-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
        )
    )
)
(defun refine-eq-intro-intless ()         
    (check-concl-kind$)
    (check-terms-kind$ 'INTLESS) 
    (<- ref-children 
        (list (make-child
                    ref-assums
                    (equal-term 
                        'EQUAL
                        nil
                        (int-term 'INT nil)
                        (mapcar #'leftterm-of-decision-term
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
                        (mapcar #'rightterm-of-decision-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
              (make-child
                    (append ref-assums
                            (list 
                              (declaration
                                  nil
                                  nil
                                  (less-term 
                                    'LESS
                                    nil
                                    (leftterm-of-decision-term
                                         (car (terms-of-equal-term ref-concl))
                                    )
                                    (rightterm-of-decision-term
                                         (car (terms-of-equal-term ref-concl))
                                    )
                                  )
                              )
                            )
                    )
                    (equal-term 
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (mapcar #'if-term-of-decision-term
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
                             nil
                             (function-term
                                'FUNCTION
                                nil
                                nil
                                (less-term          
                                    'LESS
                                    nil
                                    (leftterm-of-decision-term             
                                        (car (terms-of-equal-term ref-concl))
                                    )
                                    (rightterm-of-decision-term
                                        (car (terms-of-equal-term ref-concl))
                                    )
                                )
                                (void-term 'VOID nil)
                             )  
                         )
                       )
                    )
                    (equal-term
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (mapcar #'else-term-of-decision-term
                                (terms-of-equal-term ref-concl)
                        )
                    )
              )
        )
    )
)




(defun check-concl$ (terms-kind-needed type-kind-needed)
    (check-concl-kind$)
    (check-terms-kind$ terms-kind-needed)
    (check-type-kind$ type-kind-needed)
)

(defun check-concl-kind$ ()
    (Pif (not (eql (kind-of-term ref-concl) 'EQUAL)) -->
        (ref-error '| conclusion must be an equal-term |)
     fi)
)                              

(defun check-terms-kind$ (kind-needed) 
    (Plet (kind (terms-kind (terms-of-equal-term ref-concl))
         )
        (Pif (not (eql kind kind-needed)) -->
            (ref-error  (concat '|the terms of the equal-term are not of |
                                '| the right type for this rule |
                        )
            )
         fi)                                             
    )
)

(defun check-type-kind$ (kind-needed)
    (Pif (not (eql (kind-of-term (type-of-equal-term ref-concl)) kind-needed)) -->
        (ref-error (concat '|the type of the equal-term is not of the |
                           '|right type for this rule |
                   )
        )
     fi)
)

(defun get-subterms$ (selector terms)
    (Pif (null terms) -->
        nil
     || t -->
        (cons (funcall selector (car terms))
              (get-subterms$ selector (cdr terms))
        )
     fi)
)

(defun n-equal (term-list)
    (n-equal$ (car term-list) (cdr term-list))
)                                             

(defun n-equal$ (head tail)
    (Pif (null tail) -->
        t

     || (not (equal head (car tail))) -->
        nil

     || t -->
        (n-equal$ head (cdr tail))
 
     fi)
)

(defun substitute-in-all-terms$ (new-id old-id-list old-term-list)
    (substitute-n-in-all-terms$ 
         (list new-id) (make-lists-list$ old-id-list) old-term-list
    )
)

(defun substitute-n-in-all-terms$ (new-id-list old-id-lists-list old-term-list)
    (Pif (null old-id-lists-list) -->
        nil

     || t -->          
        (cons (substitute (car old-term-list)
                          (make-bindings$ new-id-list (car old-id-lists-list))
              )
              (substitute-n-in-all-terms$
                      new-id-list (cdr old-id-lists-list) (cdr old-term-list)
              )
        )      

     fi)
)
                                         
(defun make-lists-list$ (id-list)
    (Pif (null id-list) -->
        nil
     || t -->
        (cons (list (car id-list))
              (make-lists-list$ (cdr id-list))
        )
     fi)
)

(defun make-bindings$ (new-id-list old-id-list)
    (Pif (null new-id-list) -->
        nil

     || t -->
        (cons (list (car old-id-list) (var-term 'VAR nil (car new-id-list)))
              (make-bindings$ (cdr new-id-list) (cdr old-id-list))
        )

     fi)
) 

(defun check-if-all-new$ (ids assums)
    (Plet (assums-to-check assums
         )
        (for (id in ids)
            (do
                (check-if-new$ id assums-to-check)
                (<- assums-to-check (cons (declaration nil id nil) 
                                          assums-to-check
                                    )
                )
            )
        )
    )
)

(defun get-first-non-nil-id$ (id-list)
    (Pif (onep (length id-list)) -->
        (car id-list)
     || (not (eql (car id-list) nil)) -->
        (car id-list)
     || t -->
        (get-first-non-nil-id$ (cdr id-list))
     fi)
)

(defun check-all-free-vars-declared (using-term)
    (Pif (not (all-free-vars-declared using-term ref-assums)) -->
        (ref-error '|not all free vars. of the using term have been declared. |)
     fi)
)

 
