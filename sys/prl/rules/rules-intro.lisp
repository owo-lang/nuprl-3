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


(defun refine-atom-intro ()
    (check-intro-concl$ 'ATOM)
    nil
)

(defun refine-int-intro-number ()
    (check-intro-concl$ 'INT)
    nil
)      

(defun refine-int-intro-op ()   
    (check-intro-concl$ 'INT)
    (<- ref-children (list (make-child
                                ref-assums
                                ref-concl
                           )
                           (make-child
                                ref-assums
                                ref-concl
                           )              
                     )
    )                
    nil
)      

(defun refine-list-intro-cons ()
    (check-intro-concl$ 'LIST)
    (<- ref-children (list (make-child
                                ref-assums
                                (type-of-list-term ref-concl)
                           )
                           (make-child
                                ref-assums
                                ref-concl
                           )
                     )
    )                                    
    nil
)      

(defun refine-list-intro-nil ()  
    (check-intro-concl$ 'LIST)
    (<- ref-children
        (list (make-child     
                ref-assums
                (equal-term
                    'EQUAL
                    nil
                    (universe-term 
                        'UNIVERSE nil (level-of-list-intro-rule ref-rule)
                    )
                    (list (type-of-list-term ref-concl))
                )
              )
        )
    )
    nil
)

(defun refine-product-intro ()   
    (check-intro-concl$ 'PRODUCT)
    (Plet (new-id nil)
        (Pif (null (leftterm-of-product-intro-rule ref-rule)) -->
	    (Pif (not (null (bound-id-of-product-term ref-concl)))
		--> (ref-error '|need a term|) fi)
            (<- ref-children 
                        (list
                           (make-child
                                ref-assums
                                (lefttype-of-product-term ref-concl)
                           )
                           (make-child
                                ref-assums
                                (righttype-of-product-term ref-concl)
                           )
                        )
            )
         || (all-free-vars-declared (leftterm-of-product-intro-rule ref-rule)
                                   ref-assums
            ) -->   
            (Pif (null (new-id-of-product-intro-rule ref-rule)) -->
                (<- new-id (bound-id-of-product-term ref-concl))
	     || t -->
	        (<- new-id (new-id-of-product-intro-rule ref-rule))
             fi)
            (check-if-new$ new-id ref-assums)
            (<- ref-children 
                (list
                    (make-child
                        ref-assums              
                        (equal-term
                            'EQUAL
                            nil
                            (lefttype-of-product-term ref-concl)
                            (list 
                                (leftterm-of-product-intro-rule ref-rule)
                            )
                        )
                    )
                    (make-child
                        ref-assums
                        (substitute 
                            (righttype-of-product-term ref-concl)
                            (list 
                                (list
                                    (bound-id-of-product-term ref-concl)
                                    (leftterm-of-product-intro-rule ref-rule)
                                )
                            )
                        )
                    )
                    (make-child
                        (append 
                            ref-assums
                            (list (declaration
                                      nil
                                      new-id
                                      (lefttype-of-product-term ref-concl)
                                  )
                            )
                        )
                        (equal-term
                            'EQUAL
                             nil
                             (universe-term 
                                 'UNIVERSE
                                 nil
                                 (level-of-product-intro-rule ref-rule)
                             )
                             (list 
                                 (substitute
                                     (righttype-of-product-term ref-concl)
                                     (list (list
                                               (bound-id-of-product-term ref-concl)
                                               (var-term 'VAR nil new-id)
                                           )
                                     )
                                 )
                             )
                        )
                    )
                )
            )

         || t -->
            (ref-error 
                '|some vars in the term being introced haven't been declared |
            )
         fi)
    )
    nil
)            

(defun refine-union-intro ()
    (Plet (type1 nil
          type2 nil
         )                       
        (check-intro-concl$ 'UNION)
        (Pif (eql (selector-of-union-intro-rule ref-rule) TLeft) -->
            (<- type1 (lefttype-of-union-term ref-concl))
            (<- type2 (righttype-of-union-term ref-concl))
         || t -->
            (<- type1 (righttype-of-union-term ref-concl))
            (<- type2 (lefttype-of-union-term ref-concl))
         fi)
  
         (<- ref-children
             (list
                 (make-child
                     ref-assums
                     type1
                 )
                 (make-child
                     ref-assums
                     (equal-term
                         'EQUAL
                         nil
                         (universe-term 
                             'UNIVERSE
                             nil
                             (level-of-union-intro-rule ref-rule)
                         )
                         (list type2)
                     )
                 )
             )
         )
    )
    nil
)

(defun refine-function-intro ()       
    (check-intro-concl$ 'FUNCTION)
    (Plet (new-id
           (Pif (null (new-id-of-function-intro-rule ref-rule)) -->
               (bound-id-of-function-term ref-concl)
	    || t -->
	       (new-id-of-function-intro-rule ref-rule)
	    fi)
	 )
	(check-if-new$ new-id ref-assums)
	(<- ref-children
	    (list
		(Plet
		    (concl
			(substitute
			    (righttype-of-function-term ref-concl)
			    (list
				(list
				    (bound-id-of-function-term ref-concl)
				    (var-term 'VAR nil new-id)
				)
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
				    (lefttype-of-function-term ref-concl)
				)
			    )
			)
			concl
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
			    (level-of-function-intro-rule ref-rule)
			)
			(list (lefttype-of-function-term ref-concl))
		    )
		)
	    )
	)
    )
    nil
)

(defun refine-recursive-intro ()       
    (check-intro-concl$ 'RECURSIVE)
    (<- ref-children
	(Plet (selected-term
	       (nth
		 (position
		   (id-of-recursive-term ref-concl)
		   (bound-ids-of-bound-id-list-term
		     (bound-id-list-term-of-recursive-term ref-concl)
		   )
		 )
		 (term-list-of-bound-id-list-term
		   (bound-id-list-term-of-recursive-term ref-concl)
		 )
	       )
	    )
	    (list
	        (make-child
		  ref-assums
		  (substitute
		    (term-of-bound-id-term selected-term)
		    (append
		     (list
		       (list
		          (car (bound-ids-of-bound-id-term selected-term))
		          (term-of-recursive-term ref-concl)
		       )
		     )
		     (for (x in (term-list-of-bound-id-list-term
				  (bound-id-list-term-of-recursive-term ref-concl)
				)
			  )
			  (z in (bound-ids-of-bound-id-list-term
				  (bound-id-list-term-of-recursive-term ref-concl)
				)
			  )
			 (save
			   (list
			     z
			     (lambda-term
			       'LAMBDA
			       nil
			       (car (bound-ids-of-bound-id-term x))
			       (recursive-term
				 'RECURSIVE
				 nil
				 (bound-id-list-term-of-recursive-term ref-concl)
				 (fix-term-of-recursive-term ref-concl)
				 z
				 (var-term 'VAR nil (car (bound-ids-of-bound-id-term x)))
			       )
			     )
			   )
			 )
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
			    (level-of-recursive-intro-rule ref-rule)
			)
			(list ref-concl)
		    )
		)
	    )
       )
    )
    nil
)






(defun refine-simple-rec-intro ()
  (check-intro-concl$ 'SIMPLE-REC)
  (<- ref-children
      (list
	(make-child
	  ref-assums
	  (substitute
	    (term-of-simple-rec-term ref-concl)
	    `((,(bound-id-of-simple-rec-term ref-concl) ,ref-concl))))
	(make-child
	  ref-assums
	  (equal-term
	    'EQUAL
	    nil
	    (universe-term 'UNIVERSE nil (level-of-simple-rec-intro-rule ref-rule))
	    (list ref-concl))))))









(defun refine-quotient-intro ()
    (Plet (level (level-of-quotient-intro-rule ref-rule))
        (check-intro-concl$ 'QUOTIENT)
        (<- ref-children
            (list (make-child
                        ref-assums
                        (equal-term 'EQUAL
                                    nil
                                    (universe-term 'UNIVERSE nil level)
                                    (list ref-concl)
                        )
                  )
                  (make-child                  
                        ref-assums
                        (lefttype-of-quotient-term ref-concl)
                  )
            )
        )
    )        
    nil
)

(defun refine-set-intro ()
    (check-intro-concl$ 'SET)
    (Pif (null (bound-id-of-set-term ref-concl)) -->
	(<- ref-children
	    (list
		(make-child
		    ref-assums
		    (lefttype-of-set-term ref-concl)
		)
		(make-child
		    ref-assums
		    (righttype-of-set-term ref-concl)
		    t nil
		)
	    )
	)
     || t -->

        (Pif (and (leftterm-of-set-intro-rule ref-rule)
		  (not (all-free-vars-declared
			 (leftterm-of-set-intro-rule ref-rule)
			 ref-assums))
	    ) -->
	    (ref-error '|all vars in term not declared|)
	 fi)
        (Plet (new-id (Pif (new-id-of-set-intro-rule ref-rule) -->
			 (new-id-of-set-intro-rule ref-rule)
		      || t -->
			 (bound-id-of-set-term ref-concl)
		      fi)
	     )
	  (check-if-new$ new-id ref-assums)
	  (Pif (null (leftterm-of-set-intro-rule ref-rule))
	      --> (ref-error '|need a term|) fi)
	  (<- ref-children 
	      (list
		  (make-child
		      ref-assums              
		      (equal-term
			  'EQUAL
			  nil
			  (lefttype-of-set-term ref-concl)
			  (list (leftterm-of-set-intro-rule ref-rule))
		      )
		  )
		  (make-child
		      ref-assums
		      (substitute 
			  (righttype-of-set-term ref-concl)
			  (list 
			      (list
				  (bound-id-of-set-term ref-concl)
				  (leftterm-of-set-intro-rule ref-rule)
			      )
			  )
		      )
		      t nil
		  )
		  (make-child
		    (append1
		      ref-assums
		      (declaration nil new-id (lefttype-of-set-term ref-concl)))
		    (equal-term
		      'EQUAL nil
		      (universe-term 'UNIVERSE nil (level-of-set-intro-rule ref-rule))
		      (list
			(substitute
			  (righttype-of-set-term ref-concl)
			  `((,(bound-id-of-set-term ref-concl) ,(var-term 'VAR nil new-id)))
			)
		      )
		    )
		  )
	      )
	  )
       )
    fi)
  nil            
)



(defun refine-ui-union ()
    (check-intro-concl$ 'UNIVERSE)
    (<- ref-children
        (list
            (make-child 
                ref-assums
                (universe-term 'UNIVERSE
                    nil
                    (level-of-universe-term ref-concl)
                )
            )
            (make-child
                ref-assums
                (universe-term 'UNIVERSE
                    nil
                    (level-of-universe-term ref-concl)
                )
            )
        )
    )
    nil
)

(defun refine-ui-set ()
    (Plet (base-type (type-of-univ-intro-rule-set ref-rule)
	  x         (id-of-univ-intro-rule-set ref-rule)
	 )
	(Pif x -->
	    (<- ref-children
		(list
		  (make-child
		    ref-assums
		    (equal-term 'EQUAL nil ref-concl (list base-type))
		  )
		  (make-child
		    (append1
		      ref-assums
		      (declaration nil x base-type)
		    )
		    ref-concl
		  )
		)
	    )
	 || t -->
	    (<- ref-children
		(list
		  (make-child ref-assums ref-concl)
		  (make-child ref-assums ref-concl)
		)
	    )
	 fi)
    )
    nil
)
		      
(defun refine-ui-quotient ()
    (Plet (base-type (term-of-univ-intro-rule-quotient ref-rule)
	  equiv-rel (term2-of-univ-intro-rule-quotient ref-rule)
	  new-ids   (new-ids-of-univ-intro-rule-quotient ref-rule)
	 )
       (check-intro-concl$ 'UNIVERSE)
       (check-if-all-new$ new-ids ref-assums)
       (multiple-value-bind (x y z)
	  (values-list new-ids)
	 (Pif (not (and x y z)) -->
	     (ref-error '|3 new ids must be provided|)
	  fi)
	 (Pif (not (all-free-vars-declared base-type ref-assums)) -->
	     (ref-error
	       '|not all vars in the base type have been declared|
	     )
	  fi)
	 (Pif (not
	       (null
		 (prl-set-difference
		   (free-vars-not-declared equiv-rel ref-assums)
		   (list x y)
		 )
	       )
	     ) -->
	     (ref-error
	       '|not all vars in the equivalence relation have been declared|
	     )
	  fi)
	 (Plet (x-decl (declaration nil x base-type)
	       y-decl (declaration nil y base-type)
	       z-decl (declaration nil z base-type)
	       x-term (var-term 'VAR nil x)
	       y-term (var-term 'VAR nil y)
	       z-term (var-term 'VAR nil z)
	      )
	   (<- ref-children
		(list
		  (make-child
		    ref-assums
		    (equal-term 'EQUAL nil
		       ref-concl
		       (list base-type)
		    )
		  )
		  (make-child
		    (append
		      ref-assums
		      (list x-decl y-decl)
		    )
		    (equal-term
		      'EQUAL nil
		      ref-concl
		      (list equiv-rel)
		    )
		  )
		  (make-child
		    (append1 ref-assums x-decl)
		    (substitute
		      equiv-rel
		      `((,y ,x-term))
		    )
		  )
		  (make-child
		    (append
		      ref-assums
		      (list x-decl y-decl (declaration nil nil equiv-rel))
		    )
		    (substitute
		      equiv-rel
		      `((,x ,y-term)
			(,y ,x-term)
		       )
		    )
		  )
		  (make-child
		    (append
		      ref-assums
		      (list
			x-decl
			y-decl
			z-decl
			(declaration nil nil equiv-rel)
			(declaration
			  nil nil
			  (substitute
			    equiv-rel
			    `((,x ,y-term)
			      (,y ,z-term)
			     )
			  )
			)
		      )
		    )
		    (substitute
		      equiv-rel
		      `((,y ,z-term))
		    )
		  )
		)
	    )
	 )
       )
     )
    nil
)

(defun refine-ui-product ()                         
    (Plet (id   (id-of-univ-intro-rule-product ref-rule)
          type (type-of-univ-intro-rule-product ref-rule)
         )                        
        (check-intro-concl$ 'UNIVERSE)
        (check-if-new$ id ref-assums)
        (Pif (and type (not (all-free-vars-declared type ref-assums))) -->
            (ref-error 
                '|not all vars. in the introduced term have been declared. |
            )
         fi)
        (Pif (null (id-of-univ-intro-rule-product ref-rule)) -->
            (<- ref-children 
                (list
                    (make-child
                        ref-assums
                        (universe-term 'UNIVERSE
                            nil
                            (level-of-universe-term ref-concl)
                        )
                    )
                    (make-child
                        ref-assums
                        (universe-term 'UNIVERSE
                            nil
                            (level-of-universe-term ref-concl)
                        )
                    )
                )
            )
         || t -->
            (<- ref-children
                (list
                    (make-child
                        ref-assums
                        (equal-term 
                            'EQUAL 
                            nil
                            (universe-term 
                                'UNIVERSE
                                nil
                                (level-of-universe-term ref-concl)
                            )
                            (list type)
                        )
                    )
                    (make-child   
                        (append ref-assums 
                            (list (declaration nil id type))
                        )
                        (universe-term 
                            'UNIVERSE
                            nil
                            (level-of-universe-term ref-concl)
                        )
                    )
                )
            )
        fi)
       nil
    )
)

(defun refine-ui-function ()                          
    (Plet (id   (id-of-univ-intro-rule-function ref-rule)
          type (type-of-univ-intro-rule-function ref-rule)
         )                        
        (check-intro-concl$ 'UNIVERSE)
        (check-if-new$ id ref-assums)
        (Pif (and type (not (all-free-vars-declared type ref-assums))) -->
            (ref-error 
                '|not all vars. in the introduced term have been declared. |
            )
         fi)
        (Pif (null (id-of-univ-intro-rule-function ref-rule)) -->
            (<- ref-children 
                (list
                    (make-child
                        ref-assums
                        (universe-term 'UNIVERSE
                            nil
                            (level-of-universe-term ref-concl)
                        )
                    )
                    (make-child
                        ref-assums
                        (universe-term 'UNIVERSE
                            nil
                            (level-of-universe-term ref-concl)
                        )
                    )
                )
            )
         || t -->
            (<- ref-children
                (list
                    (make-child
                        ref-assums
                        (equal-term 
                            'EQUAL 
                            nil
                            (universe-term 
                                'UNIVERSE
                                nil
                                (level-of-universe-term ref-concl)
                            )
                            (list type)
                        )
                    )
                    (make-child   
                        (append ref-assums 
                            (list (declaration nil id type))
                        )
                        (universe-term 
                            'UNIVERSE
                            nil
                            (level-of-universe-term ref-concl)
                        )
                    )
                )
            )
        fi)
       nil
    )
)

(defun refine-ui-int ()                  
    (check-intro-concl$ 'UNIVERSE)
    nil
)

(defun refine-ui-less ()
    (check-intro-concl$ 'UNIVERSE)
    (<- ref-children
	(list
	  (make-child ref-assums (int-term 'INT nil))
	  (make-child ref-assums (int-term 'INT nil))
	)
    )
    nil
)

(defun refine-ui-atom ()
    (check-intro-concl$ 'UNIVERSE)
    nil
)

(defun refine-ui-void ()
    (check-intro-concl$ 'UNIVERSE)
    nil
)

(defun refine-ui-universe ()         
    (check-intro-concl$ 'UNIVERSE)
    (Pif (not (< (level-of-univ-intro-rule-universe ref-rule)
                    (level-of-universe-term ref-concl)
             )
        ) -->
        (ref-error (concat '|level of universe term being introduced must |
                           '|be less than that of the conclusion |
                   )
        )
     fi)
    nil
)

(defun refine-ui-equal ()
    (check-intro-concl$ 'UNIVERSE)
    (<- ref-children
	(cons
	  (make-child
	    ref-assums
	    (equal-term
	      'EQUAL nil
	      ref-concl
	      (list (type-of-univ-intro-rule-equal ref-rule))
	    )
	  )
	  (Ploop
	    (local
	      value    nil
	      i          0
	    )
	    (while (< i (num-terms-of-univ-intro-rule-equal ref-rule)))
	    (do
	      (<- value
		  (cons
		    (make-child
		      ref-assums
		      (type-of-univ-intro-rule-equal ref-rule)
		    )
		    value
		  )
	      )
	      (<- i (1+ i))
	    )
	    (result value)
	  )
	)
    )
    nil
)

(defun refine-ui-list ()    
    (check-intro-concl$ 'UNIVERSE)
    (<- ref-children (list (make-child ref-assums ref-concl)))
    nil
)

(defun refine-less-intro ()
    (ref-error '|not done yet |)
)

(defun check-intro-concl$ (kind-needed)
    (Pif (not (eql (kind-of-term ref-concl) kind-needed)) -->
        (ref-error '|conclusion not appropriate for this rule |)
     fi)
)
