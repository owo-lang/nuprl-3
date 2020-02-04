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


(defun refine-void-elim ()
    (Plet (assum-num (assum-num-of-void-elim-rule ref-rule)
         )
        (check-assum-type$ 'VOID assum-num ref-assums)
        nil
    )
)

(defun refine-int-elim ()
    (Plet (assum-num (assum-num-of-int-elim-rule ref-rule)
          assum     nil
          ids       (new-ids-of-int-elim-rule ref-rule)
         )             
        (<- assum (check-assum-type$ 'INT assum-num ref-assums))
        (Pif (null (id-of-declaration assum)) -->
            (ref-error '|in int elim the assum must be labelled by an id |)
         fi)
        (multiple-value-bind
            (ind-hyp ind-var) (check-ids 1 2 ids)
            (check-distinct ind-hyp ind-var)
            (Plet (decl-id-is-free
                    (occurs-free-in-assumption-list
                        (id-of-declaration assum)
                        (nthcdr assum-num ref-assums)
                    )
                 ) 
                (Pif (not ind-var) -->
                    (Pif  decl-id-is-free -->
                        (ref-error '|Two new ids must be given|)
                     || t -->
                        (<- ind-var (id-of-declaration assum))
                     fi)
                 fi)
            )
            (<- ref-children
                (list
                    (make-child
                        (append      
                            ref-assums
                            (Pif (not (eql ind-var (id-of-declaration assum))) -->
                                (list
                                    (declaration 
                                        nil
                                        ind-var
                                        (int-term 'INT nil)
                                    )
                                )
                             || t --> nil
                             fi)
                            (list
                                (declaration
                                    nil
                                    nil
                                    (less-term 
                                        'LESS
                                        nil
                                        (var-term 'VAR nil ind-var)
                                        (pos-number-term 'POS-NUMBER nil 0)
                                    )
                                )
                                (declaration
                                    nil
                                    ind-hyp
                                    (substitute
                                        ref-concl
                                        (list
                                            (list
                                                (id-of-declaration assum)
                                                (binary-term
                                                    'ADD
                                                    nil
                                                    (var-term 'VAR nil ind-var)
                                                    (pos-number-term
                                                        'POS-NUMBER nil 1
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                        (substitute 
                            ref-concl
                            (list
                                (list 
                                    (id-of-declaration assum)
                                    (var-term 'VAR nil ind-var)
                                )
                            )
                        )
                    )
                    (make-child
			ref-assums
                        (substitute 
                            ref-concl  
                            (list
                                (list
                                    (id-of-declaration assum)
                                    (pos-number-term 'POS-NUMBER nil 0)
                                )
                            )
                        )
                    )
                    (make-child
                        (append 
                            ref-assums
                            (Pif (not (eql ind-var (id-of-declaration assum))) -->
                                (list
                                    (declaration
                                        nil
                                        ind-var
                                        (int-term 'INT nil)
                                    )
                                )
                             || t --> nil
                             fi)
                            (list
                                (declaration
                                    nil
                                    nil
                                    (less-term 
                                        'LESS
                                        nil
                                        (pos-number-term 'POS-NUMBER nil 0)
                                        (var-term 'VAR nil ind-var)
                                    )
                                )
                                (declaration                
                                    nil
                                    ind-hyp
                                    (substitute
                                        ref-concl
                                        (list
                                            (list
                                                (id-of-declaration assum)
                                                (binary-term
                                                    'SUB
                                                    nil
                                                    (var-term 'VAR nil ind-var)
                                                    (pos-number-term
                                                        'POS-NUMBER nil 1
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                        (substitute 
                            ref-concl
                            (list
                                (list 
                                    (id-of-declaration assum)
                                    (var-term 'VAR nil ind-var)
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


(defun refine-list-elim ()
    (Plet (assum-num (assum-num-of-list-elim-rule ref-rule)
          assum     nil
          assum-id  nil
          ids       (new-ids-of-list-elim-rule ref-rule)
         )             
        (<- assum (check-assum-type$ 'LIST assum-num ref-assums))
        (<- assum-id (id-of-declaration assum))
        (Pif (null assum-id) -->
            (ref-error '|in list elim the assum must be labelled by an id |)
         fi)
        (multiple-value-bind
            (ind-hyp hd-var tl-var) (check-ids 2 3 ids)
            (check-distinct ind-hyp hd-var tl-var)
	    (cond ((not hd-var) (ref-error '|must supply head var.|)))
            (Pif (not tl-var) -->
                (Pif (occurs-free-in-assumption-list
                        assum-id
                        (nthcdr assum-num ref-assums)
                    ) -->
                    (ref-error '|three new ids must be given|)
                 || t -->
                    (<- tl-var assum-id)
                 fi)
             fi)
            (<- ref-children
                (list
                    (make-child
			ref-assums
                        (substitute 
                            ref-concl  
                            (list
                                (list
                                    assum-id
                                    (nil-term 'NIL nil)
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
                                    hd-var
                                    (type-of-list-term
                                        (type-of-declaration assum)
                                    )
                                )
                            )
                            (Pif (not (eql tl-var assum-id)) -->
                                (list
                                    (declaration
                                        nil
                                        tl-var
                                        (type-of-declaration assum)
                                    )
				)
			     || t --> nil
			     fi)
                            (list
                                (declaration 
                                    nil
                                    ind-hyp
                                    (substitute
                                        ref-concl
                                        (list
                                            (list
                                                assum-id
                                                (var-term 'VAR nil tl-var)
                                            )
                                        )
                                    )
                                )
                            )
                        )
                        (substitute
                            ref-concl
                            (list
                                (list
                                    assum-id
                                    (cons-term
                                        'CONS
                                        nil
                                        (var-term 'VAR nil hd-var)
                                        (var-term 'VAR nil tl-var)
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

(defun refine-union-elim ()
    (Plet (assum-num (assum-num-of-union-elim-rule ref-rule)
          assum     nil
          ids       (new-ids-of-union-elim-rule ref-rule)
          sub1      nil
          sub2      nil
          eq-assum1 nil
          eq-assum2 nil
         )
        (<- assum (check-assum-type$ 'UNION assum-num ref-assums))
        (multiple-value-bind
            (left-var right-var) (check-ids 0 2 ids)
            (Pif (and
		    (member (id-of-declaration assum) (free-vars ref-concl))
                    (not (and left-var right-var))
                ) -->
                (ref-error '|must provide 2 new ids. |)
             fi)
            (Pif left-var -->
                (<- sub1
                    (list
                        (list
                            (id-of-declaration assum) 
                            (injection-term 'INL
                                nil
                                (var-term 'VAR nil left-var)
                            )
                        )
                    )
                )
                (Pif (id-of-declaration assum) -->
                    (<- eq-assum1 
                        (declaration
                            nil nil
                            (equal-term
                                'EQUAL nil
                                (type-of-declaration assum)
                                (list
                                    (var-term
                                        'VAR nil
                                        (id-of-declaration assum)
                                    )
                                    (cadar sub1)
                                )
                            )
                        )
                    )
                 fi)
             fi)
            (Pif right-var -->
                (<- sub2
                    (list
                        (list
                            (id-of-declaration assum) 
                            (injection-term
                                'INR nil
                                (var-term 'VAR nil right-var)
                            )
                        )
                    )
                )
                (Pif (id-of-declaration assum) -->
                    (<- eq-assum2 
                        (declaration
                            nil nil
                            (equal-term
                                'EQUAL nil
                                (type-of-declaration assum)
                                (list
                                    (var-term
                                        'VAR nil
                                        (id-of-declaration assum)
                                    )
                                    (cadar sub2)
                                )
                            )
                        )
                    )
                 fi)
             fi)
            (<- ref-children
                (list
                    (make-child 
                        (append
                            ref-assums
                            (cons
                                (declaration
                                    nil
                                    left-var
                                    (lefttype-of-union-term 
                                        (type-of-declaration assum)
                                    )
                                )
                                (Pif eq-assum1 --> (list eq-assum1)
                                 || t --> nil
                                 fi)
                            )
                        )
                        (substitute ref-concl sub1)
                    )
                    (make-child 
                        (append
                            ref-assums
                            (cons
                                (declaration 
                                    nil
                                    right-var
                                    (righttype-of-union-term 
                                        (type-of-declaration assum)
                                    )
                                )
                                (Pif eq-assum2 --> (list eq-assum2)
                                 || t --> nil
                                 fi)
                            )
                        )
                        (substitute ref-concl sub2)
                    )
                )
            )
        )
    )
    nil
)
   
(defun refine-product-elim ()
    (Plet (assum-num (assum-num-of-product-elim-rule ref-rule)
          assum     nil
          ids       (new-ids-of-product-elim-rule ref-rule)
          sub       nil                                    
          bound-id  nil
          eq-assum  nil
         )                                                              
        (<- assum (check-assum-type$ 'PRODUCT assum-num ref-assums))
        (multiple-value-bind
            (1st-var 2nd-var) (check-ids 0 2 ids)
            (check-distinct 1st-var 2nd-var)
            (Pif (null 1st-var) -->
                (Pif (member
                        (bound-id-of-product-term (type-of-declaration assum))
                        (free-vars
                            (righttype-of-product-term
                                (type-of-declaration assum)
                            )
                        )
                    ) -->
                    (ref-error
                        '|second new assum would not have all vars declared |
                    )
                    
                 || (member (id-of-declaration assum) (free-vars ref-concl)) -->
                    (ref-error '|must give two new ids. |)
                 fi)
             fi)
            (Pif (and 1st-var 2nd-var) -->
                (<- sub
                    (list
                        (list
                            (id-of-declaration assum) 
                            (pair-term 'PAIR nil
                                (var-term 'VAR nil 1st-var)
                                (var-term 'VAR nil 2nd-var)
                            )
                        )
                    )
                )
                (Pif (id-of-declaration assum) -->
                    (<- eq-assum 
                        (declaration
                            nil nil
                            (equal-term
                                'EQUAL nil
                                (type-of-declaration assum)
                                (list
                                    (var-term
                                        'VAR nil
                                        (id-of-declaration assum)
                                    )
                                    (cadar sub)
                                )
                            )
                        )
                    )
                 fi)
             fi)
            (<- bound-id
                (bound-id-of-product-term (type-of-declaration assum))
            )
            (<- ref-children
                (list
                    (make-child    
                        (append
                            ref-assums
                            (cons
                                (declaration
                                    nil 1st-var
                                    (lefttype-of-product-term 
                                        (type-of-declaration assum)
                                    )
                                )
                                (cons
                                    (declaration
                                        nil 2nd-var
                                        (substitute
                                            (righttype-of-product-term 
                                                (type-of-declaration assum)
                                            )
                                            (list 
                                                (list 
                                                    bound-id              
                                                    (var-term 'VAR nil 1st-var)
                                                )
                                            )
                                        )
                                    )
                                    (Pif eq-assum --> (list eq-assum)
                                     || t --> nil
                                     fi)
                                )
                            )
                        )
                        (substitute ref-concl sub)
                    )
                )
            )
        )
    )
    nil
)

(defun refine-function-elim ()
    (Plet (assum-num (assum-num-of-function-elim-rule ref-rule)
          assum     nil
          term      (leftterm-of-function-elim-rule ref-rule)
          ids       (new-ids-of-function-elim-rule ref-rule)
          eq-assum  nil
	  righttype nil
         )                                                              
        (<- assum (check-assum-type$ 'FUNCTION assum-num ref-assums))
        (multiple-value-bind
            (new-id) (check-ids 0 1 ids)
            (Pif (and
		    (null term)
                    (not
		        (occurs-free-in-term
                            (bound-id-of-function-term 
                                (type-of-declaration assum)
                            )
			    (righttype-of-function-term
			        (type-of-declaration assum)
			    )
			)
                    )
                ) -->
                (<- ref-children
                    (list
                        (make-child
                            ref-assums
                            (lefttype-of-function-term
                                (type-of-declaration assum)
                            )
                        )
                        (make-child
                            (append 
                                ref-assums  
                                (list   
                                    (declaration
                                        nil
                                        new-id
                                        (righttype-of-function-term
                                            (type-of-declaration assum)
                                        )
                                    )
                                )
                            )
                            ref-concl
                        )
                    )
                )

	     || (null term) -->
	        (ref-error '|a term must be provided|)
                
             || (all-free-vars-declared term ref-assums) -->
	        (<- righttype
		    (Pif (is-dependent-product (type-of-declaration assum)) -->
			(substitute
			    (righttype-of-function-term
				(type-of-declaration assum)
			    )
			    (list
				(list
				    (bound-id-of-function-term
					(type-of-declaration assum)
				    )
				    term
				)
			    )
			)
		     || t -->
		        (righttype-of-function-term
			    (type-of-declaration assum)
			)
		     fi)
		)
                (Pif (and (id-of-declaration assum) new-id) -->
                    (<- eq-assum
                        (declaration
                            nil nil
                            (equal-term
                                'EQUAL nil
				righttype
                                (list
                                    (apply-term 
                                        'APPLY
                                        nil
                                        (var-term 
                                            'VAR nil
                                            (id-of-declaration assum)
                                        )
                                        term
                                    )
                                    (var-term 'VAR nil new-id)
                                )
                            )
                        )
                    )
                 fi)
                (<- ref-children
                    (list
                        (make-child    
                            ref-assums
                            (equal-term 
                                'EQUAL nil
                                (lefttype-of-function-term
                                    (type-of-declaration assum)
                                )
                                (list term)
                            )
                        )
                        (make-child
                            (append 
                                ref-assums
                                (cons
                                    (declaration
                                        nil
                                        new-id
					righttype
                                    )
                                    (Pif eq-assum --> (list eq-assum)
                                     || t --> nil
                                     fi)
                                )
                            )
                            ref-concl
                        )
                    )
                )
                
             || t -->
                (ref-error '|term given does not have all vars. properly declared |)
             fi)
        )
    )
    nil
)

;;-
;;-  H,t:w:A+>B,H' >> G       by elim t on a new y,x
;;-      >> a in {x:A|dom)(t)(x)}
;;-      y:B[a/x],y=t[a] in B[a/x] >> G
;;-
(defun refine-parfunction-elim ()
    (Plet (assum-num (assum-num-of-parfunction-elim-rule ref-rule)
	  term      (leftterm-of-parfunction-elim-rule ref-rule)
	  ids       (new-ids-of-parfunction-elim-rule ref-rule)
	  assum     nil
	  lefttype  nil
	  righttype nil
	 )
	 (<- assum (check-assum-type$ 'PARFUNCTION assum-num ref-assums))
	 (check-all-free-vars-declared term)
	 (Pif (or (null ids)
		 (not (= (length ids) 2))
	     ) --> (ref-error '|expecting 2 new ids.  |)
	  fi)
	 (check-if-new$ (car ids) ref-assums)
	 (<- lefttype (lefttype-of-parfunction-term (type-of-declaration assum)))
	 (<- righttype (righttype-of-parfunction-term (type-of-declaration assum)))
	 (<- ref-children
	     (list
	       (make-child
		ref-assums
		(equal-term
		    'EQUAL
		    nil
		    (set-term
		        'SET
		        nil
		        (cadr ids)
		        lefttype
		        (apply-term
		            'APPLY
		            nil
		            (dom-term
			        'DOM
			        nil
			        (var-term 'VAR nil (id-of-declaration assum))
		            )
		            (var-term 'VAR nil (cadr ids))
		        )
		    )
		    (list term)
		 )
	       )
	       (make-child
		 (append ref-assums
			 (list
			   (declaration
			     nil
			     (car ids)
			     (substitute
			       righttype
			       (list
				 (list
				   (id-of-declaration assum)
				   term
				 )
			       )
			     )
			   )
			   (declaration
			     nil
			     nil
			     (equal-term
			       'EQUAL
			       nil
			       (substitute
			          righttype
			          (list
				    (list
				      (id-of-declaration assum)
				      term
				    )
			          )
			        )
			       (list
				 (var-term 'VAR nil (car ids))
				 (apply-partial-term
				   'APPLY-PARTIAL
				   nil
				   (var-term 'VAR nil (id-of-declaration assum))
				   term
				 )
			       )
			     )
			   )
			 )
		 )
		 ref-concl
	       )
	     )
	 )
    )
)

(defun refine-quotient-elim ()
    (Plet (level  (level-of-quotient-elim-rule ref-rule)
          ids    (new-ids-of-quotient-elim-rule ref-rule)
          assum-num (assum-num-of-quotient-elim-rule ref-rule)
          assum  nil
          bound-id1 nil
          bound-id2 nil
          new-id1   nil
          new-id2   nil
	  left-term nil
	  right-term nil
         )
        (<- assum (check-assum-type$ 'QUOTIENT assum-num ref-assums))
        (<- bound-id1 
            (car (bound-ids-of-quotient-term (type-of-declaration assum)))
        )
        (<- bound-id2
            (cadr (bound-ids-of-quotient-term (type-of-declaration assum)))
        )
        (Plet (l (length ids))
            (<- new-id1 (Pif (> l 0) --> (car ids) || t --> bound-id1 fi))
            (<- new-id2 (Pif (> l 1) --> (cadr ids) || t --> bound-id2 fi))
        )
        (check-if-new$ new-id1 ref-assums)
        (check-if-new$ new-id2 ref-assums)
        (check-distinct new-id1 new-id2) 

        (Pif (not (and (eql (kind-of-term ref-concl) 'EQUAL)
                      (<= (length (terms-of-equal-term ref-concl)) 2)
                 )
            ) -->
            (ref-error '| conclusion not appropriate for quotient elim rule |)

	 || (= (length (terms-of-equal-term ref-concl)) 1) -->
	    (<- left-term (car (terms-of-equal-term ref-concl)))
	    (<- right-term left-term)

	 || t -->  ;-- (= (length (terms-of-equal-term ref-concl)) 2)
	    (<- left-term (car (terms-of-equal-term ref-concl)))
	    (<- right-term (cadr (terms-of-equal-term ref-concl)))
         fi)

        (<- ref-children
            (list
                  (make-child
                      (append
                          ref-assums
                          (list
                              (declaration nil
                                  new-id1
                                  (lefttype-of-quotient-term
                                      (type-of-declaration assum)
                                  )
                              )
                              (declaration nil
                                  new-id2
                                  (lefttype-of-quotient-term
                                      (type-of-declaration assum)
                                  )
                              )
                          )
                      )
                      (equal-term 'EQUAL nil
                          (universe-term 'UNIVERSE nil level)
                          (list
                              (substitute
                                  (righttype-of-quotient-term
                                      (type-of-declaration assum)
                                  )
                                  (list
                                      (list
                                          bound-id1
                                          (var-term 'VAR nil new-id1)
                                      )
                                      (list
                                          bound-id2
                                          (var-term 'VAR nil new-id2)
                                      )
                                  )
                              )
                          )
                      )
                  )
                  (make-child
                        ref-assums             
                        (equal-term 'EQUAL
                                    nil
                                    (universe-term 'UNIVERSE nil level)
                                    (list (type-of-equal-term ref-concl))
                        )
                  )
                  (make-child
                      (append ref-assums
                              (list
                                 (declaration
                                    nil
                                    new-id1
                                    (lefttype-of-quotient-term
                                        (type-of-declaration assum)
                                    )
                                 )
                                 (declaration                      
                                    nil
                                    new-id2
                                    (lefttype-of-quotient-term
                                        (type-of-declaration assum)
                                    )
                                 )   
                                 (declaration 
                                    nil
                                    nil
                                    (substitute 
                                        (righttype-of-quotient-term
                                            (type-of-declaration assum)
                                        )                              
                                        (list (list
                                                 bound-id1
                                                 (var-term 'VAR nil new-id1)
                                              )
                                              (list
                                                 bound-id2
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
                            (substitute 
                                (type-of-equal-term ref-concl)
                                (list (list
                                           (id-of-declaration assum)
                                           (var-term 'VAR nil new-id1)
                                      )
                                )
                            ) 
                            (list (substitute
                                      left-term
                                      (list (list
                                                (id-of-declaration assum)
                                                (var-term 'VAR nil new-id1)
                                            )
                                      )
                                  )
                                  (substitute
                                      right-term
                                      (list (list
                                                (id-of-declaration assum)
                                                (var-term 'VAR nil new-id2)
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

(defun refine-set-elim ()
  (declare (special *use-new-set-rules-p*))
    (cond
      (*use-new-set-rules-p*
       (refine-new-set-elim))
      (t
       (;; indenting is screwed because c-m-q was used on prl macros.
	Plet (level  (level-of-set-elim-rule ref-rule)
		    assum-num (assum-num-of-set-elim-rule ref-rule)
		    assum  nil
		    eq-assum nil
		    ids    (new-ids-of-set-elim-rule ref-rule)
		    righttype nil
		    )          
	    (<- assum (check-assum-type$ 'SET assum-num ref-assums))
	    (multiple-value-bind
	      (new-id) (check-ids 0 1 ids)
	      (Pif (null new-id) -->
		  (Pif (occurs-free-in-term
			(bound-id-of-set-term (type-of-declaration assum))
			(righttype-of-set-term (type-of-declaration assum))
			) -->
		      (<- new-id
			  (bound-id-of-set-term (type-of-declaration assum))
			  )
		      (Pif (already-declared new-id ref-assums) -->
			  (ref-error '|a new id must be given|)
			  fi)
		      fi)
		  fi)
	      (<- righttype
		  (Pif (bound-id-of-set-term (type-of-declaration assum)) -->
		      (substitute
		        (righttype-of-set-term
			  (type-of-declaration assum)
			  )
			(list
			  (list
			    (bound-id-of-set-term
			      (type-of-declaration assum)
			      )
			    (var-term 'VAR nil new-id)
			    )
			  )
			)
		      || t -->
		      (righttype-of-set-term (type-of-declaration assum))
		      fi)
		  )
	      (Pif (and
		    new-id
		    (id-of-declaration assum)
		    (occurs-free-in-assumption-list
		      (id-of-declaration assum)
		      (nthcdr assum-num ref-assums)
		      )
		    ) -->
		  (<- eq-assum
		      (declaration
		        nil nil
			(equal-term
			  'EQUAL nil
			  (lefttype-of-set-term (type-of-declaration assum))
			  (list
			    (var-term 'VAR nil new-id)
			    (var-term 'VAR nil (id-of-declaration assum))
			    )
			  )
			)
		      )
		  fi)
	      (<- ref-children
		  (list
                    (make-child
		      (append1
			ref-assums
			(declaration
			  nil new-id
			  (lefttype-of-set-term (type-of-declaration assum))
			  )
                        )
		      (equal-term
			'EQUAL nil
			(universe-term 'UNIVERSE nil level)
			(list
			  righttype
			  )
                        )
		      )
                    (make-child
		      (append
			ref-assums
			(list
			  (declaration 
			    nil new-id
			    (lefttype-of-set-term
			      (type-of-declaration assum)
			      )
			    )
			  (declaration 
			    nil nil
			    righttype
			    )
			  )
			(Pif eq-assum -->
			    (list eq-assum)
			    || t -->
			    nil
			    fi)
                        )
		      (Pif (and new-id (id-of-declaration assum)) -->
			  (substitute
			    ref-concl
			    (list
			      (list
				(id-of-declaration assum)
				(var-term 'VAR nil new-id)
				)
			      )
			    )
			  || t -->
			  ref-concl
			  fi)
		      t (cons (+ 2 (length ref-assums)) ref-hidden)
		      )
		    )
		  )
	      )
	    )))
    nil
)

(defun make-var-term (x) (var-term 'var nil x))

(defun refine-new-set-elim ()
    (let* ((i (assum-num-of-set-elim-rule ref-rule))
	   (assum (check-assum-type$ 'SET i ref-assums))
	   (ids (new-ids-of-set-elim-rule ref-rule))
	   (set-bound-id (bound-id-of-set-term (type-of-declaration assum)))
	   (declared-id (id-of-declaration assum))
	   (new-id (multiple-value-bind
		     (new-id) (check-ids 0 1 ids)
		     (cond ((and (null new-id)
				 (null declared-id)
				 (not (null set-bound-id))    
				 (already-declared set-bound-id ref-assums))
			    (ref-error '|a new id must be given|))
			   ((null new-id)
			    set-bound-id)
			   (t
			    new-id))))
	   (left-type (lefttype-of-set-term (type-of-declaration assum)))
	   (right-type (righttype-of-set-term (type-of-declaration assum)))
	   (new-assum-list (cond (declared-id
				  (append
				    (subseq ref-assums 0 (1- i))
				    (list (declaration nil declared-id left-type))
				    (list (declaration
					    nil nil
					    (substitute right-type `((,set-bound-id ,(make-var-term declared-id))))))
				    (nthcdr i ref-assums)))
				 (t
				  (append
				    ref-assums
				    (list (declaration nil new-id left-type))
				    (list (declaration
					    nil nil
					    (cond ((eql new-id set-bound-id) right-type)
						  (t (substitute right-type `((,set-bound-id ,(make-var-term new-id))))))))))))
	   (new-hidden-list (cond (declared-id
				   (cons (1+ i)
					 (mapcar #'(lambda (j) (cond ((> j i) (1+ j)) (t j)))
						 ref-hidden)))
				  (t
				   (cons (+ 2 (length ref-assums)) ref-hidden)))))
      (<- ref-hidden new-hidden-list)
      (<- ref-children
	  (list (make-child new-assum-list ref-concl)))))

(defun refine-recursive-unroll-elim ()
	(Plet (assum         nil
	      assum-num     (assum-num-of-recursive-unroll-elim-rule ref-rule)
	      new-ids       (new-ids-of-recursive-unroll-elim-rule ref-rule)
	      rec-term      nil
	      selected-term nil
	      new-term      nil
	      ids           nil
	      term-list     nil
	     )
	     (<- assum (check-assum-type$ 'RECURSIVE assum-num ref-assums))
	     (Pif (null (id-of-declaration assum)) -->
                 (ref-error '| the assum must be labelled by an id |)
              fi)
	     (Pif (not (= (length new-ids) 1)) -->
		 (ref-error '|expecting one new id. |)
	      fi)
	     (check-if-new$ (car new-ids) ref-assums)
	     (<- rec-term (type-of-declaration assum))
	     (<- term-list (term-list-of-bound-id-list-term
			     (bound-id-list-term-of-recursive-term rec-term)
			   )
	     )
	     (<- ids (bound-ids-of-bound-id-list-term
		       (bound-id-list-term-of-recursive-term rec-term)
		     )
	     )
	     (<- selected-term
		 (nth
		   (position (id-of-recursive-term rec-term) ids)
		   term-list
		 )
	     )
	     (<- new-term
		 (substitute
		    (term-of-bound-id-term selected-term)
		    (append
		     (list
		       (list
		          (car (bound-ids-of-bound-id-term selected-term))
		          (term-of-recursive-term rec-term)
		       )
		     )
		     (for (x in term-list)
			  (z in ids)
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
				 (bound-id-list-term-of-recursive-term rec-term)
				 (fix-term-of-recursive-term rec-term)
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
	     (<- ref-children
		 (list
		   (make-child
		     (append
		       ref-assums      ;;;;- check with nax on this.
		       (list
			 (declaration
			   nil
			   (car new-ids)
			   new-term
			 )
			 (declaration
			   nil
			   nil
			   (equal-term
			     'EQUAL
			     nil
			     new-term
			     (list (var-term 'VAR nil (id-of-declaration assum))
				   (var-term 'VAR nil (car new-ids))
			     )
			   )
			 )
		       )
		     )
		     (substitute
		       ref-concl
		       (list
			 (list
			   (id-of-declaration assum)
			   (var-term 'VAR nil (car new-ids))
			 )
		       )
		     )
		   )
		 )
	     )
	)
)


(defun refine-simple-rec-unroll-elim ()
    (let* ((assum-num (assum-num-of-simple-rec-unroll-elim-rule ref-rule))
	   (assum (check-assum-type$ 'SIMPLE-REC assum-num ref-assums))
	   (elim-id (id-of-declaration assum))
	   (new-id (Plet (new-id
			  (new-id-of-simple-rec-unroll-elim-rule ref-rule))
			(Pif (and (not (null elim-id)) (null new-id))
			    --> (ref-error '|expecting one new id. |) fi)
			(check-if-new$ new-id ref-assums)
			new-id))
	   (rec-term (type-of-declaration assum))
	   (id (bound-id-of-simple-rec-term rec-term))
	   (term (term-of-simple-rec-term rec-term))
	   (new-term (substitute term `((,id ,rec-term)))))
	 (<- ref-children
	     (list
	       (make-child
		 (append
		   ref-assums
		   (list (declaration nil new-id new-term))
		   (Pif (null elim-id)
		       --> nil ||
		       t
		       --> (list (declaration
				   nil
				   nil
				   (equal-term
				     'EQUAL
				     nil
				     new-term
				     (list
				       (var-term 'VAR nil elim-id)
				       (var-term 'VAR nil new-id))))) fi))
		 (Pif (null elim-id)
		     --> ref-concl  ||
		     t
		     --> (substitute
			   ref-concl
			   (list
			     (list
			       elim-id
			       (var-term 'VAR nil new-id)))) fi))))))



(defun refine-recursive-elim ()
    (let* ((assum-num (assum-num-of-recursive-elim-rule ref-rule))
	   (level (level-of-recursive-elim-rule ref-rule))
	   (over-pair-list (over-pair-list-of-recursive-elim-rule ref-rule))
	   (using-list (using-term-list-of-recursive-elim-rule ref-rule))
	   (new-ids (new-ids-of-recursive-elim-rule ref-rule)))
      (Pif (fix-term-of-recursive-term
	    (type-of-declaration (nthelem assum-num ref-assums))) -->
	  (refine-recursive-with-fix-elim
	    assum-num level over-pair-list using-list new-ids)
       || t -->
          (refine-recursive-without-fix-elim
	    assum-num level over-pair-list using-list new-ids)
       fi)
    )
)

(defun refine-recursive-with-fix-elim (assum-num level over-pair-list using-term-list ids2)
    (Plet (assum             nil
	  rec-term          nil
	  fix-term          nil
	  rec-term-list     nil
	  fix-id-list       nil
	  fix-term-list     nil
	  ids1              nil
	  subst-list        nil
	  selected          0
	)
        (<- assum (check-assum-type$ 'RECURSIVE assum-num ref-assums))
	(Pif (null (id-of-declaration assum)) -->
            (ref-error '| the assum must be labelled by an id |)
         fi)
	(for (x in using-term-list)
	     (do
	       (Pif (not (eql (kind-of-term x) 'PARFUNCTION)) -->
		   (ref-error '|unexpected term kind in using list. |)
	        fi)
	       (check-all-free-vars-declared x)
	     )
	)
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
	(<- rec-term (type-of-declaration assum)) 
	(<- rec-term-list (term-list-of-bound-id-list-term
			    (bound-id-list-term-of-recursive-term rec-term)
			  )
	)
	(<- fix-term (fix-term-of-recursive-term rec-term))
	(<- fix-term-list (term-list-of-bound-id-list-term
			    (bound-id-list-term-of-fix-term fix-term)
			  )
	)
	(<- fix-id-list (bound-ids-of-bound-id-list-term
		          (bound-id-list-term-of-fix-term fix-term)
		        )
	)
	(<- ids1 (bound-ids-of-bound-id-list-term
		  (bound-id-list-term-of-recursive-term rec-term)
		)
	)
	(Pif (not (and (eql (length rec-term-list) (length using-term-list))
		      (eql (length rec-term-list) (length over-pair-list))
		      (eql (length rec-term-list) (length ids2))
		  )
	    ) -->
	    (ref-error '| term lists not all of same length. |)
	 fi)
	(<- selected
	    (position
	      (id-of-recursive-term rec-term) ids1
	    )
	)
	(for (x in using-term-list)
	     (do
	       (check-all-free-vars-declared x)
	     )
	)
      	(Pif (not (equal-terms (substitute
				(cdr (nth selected over-pair-list))
                                (list
				  (list
				    (car (nth selected over-pair-list))
				    (pair-term
				      'PAIR
				      nil
				      (term-of-recursive-term rec-term)
				      (var-term
					'VAR
					nil
					(id-of-declaration assum)
				      )
				    )
				  )
				)
                               )
                              ref-concl
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
        (<- ref-children
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
							rec-term
						      )
						      (bound-id-list-term-of-fix-term
							(fix-term-of-recursive-term rec-term)
						      )
						      ids2
					              level
		                 )
		 )
		 (append 
		         (for (y in using-term-list)
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
						(cdr (bound-ids-of-bound-id-term v))
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
				  (cdr z)
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
			       (list (term-of-recursive-term rec-term))
			     )
			   )
			 )
			 (for (x in using-term-list) 
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
			 (for (y in using-term-list) 
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
			 (for (z in fix-term-list)  
			      (w in rec-term-list)
			      (y in using-term-list)
			      (save
				(make-child
				  (append ref-assums
					  assum-segment1
					  (list
					    (declaration
					      nil
					      (car (bound-ids-of-bound-id-term z))
					      (lefttype-of-parfunction-term y)
					    )
					    (declaration
					      nil
					      nil
					      (substitute
						  (term-of-bound-id-term w)
						    (cons
						      (list
							(car (bound-ids-of-bound-id-term w))
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
				    (list (term-of-bound-id-term z))
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

(defun refine-recursive-without-fix-elim (assum-num level over-pair-list using-term-list ids2)
    (Plet (assum             nil
	  rec-term          nil
	  rec-term-list     nil
	  ids1              nil
	  selected          0
	)
        (<- assum (check-assum-type$ 'RECURSIVE assum-num ref-assums))
	(Pif (null (id-of-declaration assum)) -->
            (ref-error '| the assum must be labelled by an id |)
         fi)
	(for (x in using-term-list)
	     (do
	       (check-all-free-vars-declared x)
	     )
	)
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
	(<- rec-term (type-of-declaration assum)) 
	(<- rec-term-list (term-list-of-bound-id-list-term
			    (bound-id-list-term-of-recursive-term rec-term)
			  )
	)
	(<- ids1 (bound-ids-of-bound-id-list-term
		  (bound-id-list-term-of-recursive-term rec-term)
		)
	)
	(Pif (not (and (eql (length rec-term-list) (length using-term-list))
		      (eql (length rec-term-list) (length over-pair-list))
		      (eql (length rec-term-list) (length ids2))
		  )
	    ) -->
	    (ref-error '| term lists not all of same length. |)
	 fi)
	(<- selected
	    (position
	      (id-of-recursive-term rec-term) ids1
	    )
	)
      	(Pif (not (equal-terms (substitute
				(cdr (nth selected over-pair-list))
                                (list
				  (list
				    (car (nth selected over-pair-list))
				    (pair-term
				      'PAIR
				      nil
				      (term-of-recursive-term rec-term)
				      (var-term
					'VAR
					nil
					(id-of-declaration assum)
				      )
				    )
				  )
				)
                               )
                              ref-concl
                     )
                ) -->
                (ref-error (concat '|the type of the equal-term doesn't |
                                   '|properly match the corresponding term |
				   '|in the 'over' list. |
                           )
                )
         fi)
        (<- ref-children
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
				 (universe-term
				     'UNIVERSE
				      nil
				      level
				 )
			     )
	                  )  
	              )
	            )
		  assum-segment2
		                 (make-assum-segment3 using-term-list
					              over-pair-list
						      (bound-id-list-term-of-recursive-term
							rec-term
						      )
						      ids2
					              level
		                 )
		 )
		 (append (for (y in using-term-list) 
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
						(cdr (bound-ids-of-bound-id-term v))
						y
						(term-of-bound-id-term v)
					      )
					    )
					  )
				  )
				  (cdr z)
				)
			      )
			 )
			 (for (x in using-term-list) 
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
			 (list
			   (make-child   
			     ref-assums
			     (equal-term
			       'EQUAL
			       nil
			       (nth selected using-term-list)
			       (list (term-of-recursive-term rec-term))
			     )
			   )
			 )
			 (for (y in using-term-list) 
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
			 
		 )

	    )
        )
    )
    nil
)



(defun refine-simple-rec-elim ()
    (let* ((i (assum-num-of-simple-rec-elim-rule ref-rule))
	   (assum (check-assum-type$ 'SIMPLE-REC i ref-assums))
	   (level (level-of-simple-rec-elim-rule ref-rule))
	   (new-ids (new-ids-of-simple-rec-elim-rule ref-rule))
	   (x (or (second new-ids) (fourth new-ids)))
	   (h (third new-ids))
	   (z (fourth new-ids))
	   (r (id-of-declaration assum))	
	   (phi (type-of-declaration assum))
	   (phi-id (bound-id-of-simple-rec-term phi))
	   (phi-body (term-of-simple-rec-term phi))
	   (p (cond ((null (first new-ids))
		     (check-if-new$ phi-id ref-assums)
		     phi-id)
		    (t
		     (first new-ids))))
	   (Ui (universe-term 'UNIVERSE nil level))
	   (phi-subset (set-term
			 'SET nil x phi
			 (apply-term
			   'APPLY nil (var-term 'VAR nil p) (var-term 'VAR nil x))))
	   (adjusted-concl
	     (cond ((null r) ref-concl)
		   (t (substitute
			ref-concl
			(list (list r (var-term 'VAR nil z))))))))
      (for (id in (list h z p)) (do (check-if-new$ id ref-assums)))
      (cond ((not (no-duplicates? (remove 'nil (list h z p))))
	     (ref-error '|new ids must be distinct.|)))
      (cond ((or (null x)
		 (and r
		      (member r (free-vars ref-concl))
		      (null z)))
	     (ref-error '|not enough new ids supplied|)))
      (<- ref-children 
	  (list
	    (make-child
	      (append
		ref-assums
		(list
		  (declaration
		    nil p
		    (function-term
		      'FUNCTION nil nil phi Ui))
		  (declaration
		    nil h
		    (function-term
		      'FUNCTION nil r phi-subset ref-concl))
		  (declaration
		    nil z
		    (substitute
		      phi-body
		      (list (list phi-id phi-subset))))))
	      adjusted-concl)
	    (make-child
	      ref-assums
	      (equal-term 'EQUAL nil Ui (list phi)))))))


; (defun refine-simple-rec-elim ()
;    (let* ((i (assum-num-of-simple-rec-elim-rule ref-rule))
;	   (assum (check-assum-type$ 'SIMPLE-REC i ref-assums))
;	   (level (level-of-simple-rec-elim-rule ref-rule))
;	   (new-ids (Plet (new-ids (new-ids-of-simple-rec-elim-rule ref-rule))
;			 (for (id in new-ids) (do (check-if-new$ id ref-assums)))
;			 new-ids))
;	   (h (second new-ids))
;	   (z (third new-ids))
;	   (r (or (id-of-declaration assum) z))	;r is also the b.v. of the set type
;	   (phi (type-of-declaration assum))
;	   (phi-id (bound-id-of-simple-rec-term phi))
;	   (phi-body (term-of-simple-rec-term phi))
;	   (p (cond ((null new-ids)
;		     (check-if-new$ phi-id ref-assums)
;		     phi-id)
;		    (t
;		     (first new-ids))))
;	   (Ui (universe-term 'UNIVERSE nil level))
;	   (phi-subset (set-term
;			 'SET nil r phi
;			 (apply-term
;			   'APPLY nil (var-term 'VAR nil p) (var-term 'VAR nil r))))
;	   (adjusted-concl
;	     (cond ((null r) ref-concl)
;		   (t (substitute
;			ref-concl
;			(list (list r (var-term 'VAR nil z))))))))
;      ;; Check that enough ids are around.  (This check imposes silly
;      ;; restrictions and is due in part to a library-preserving
;      ;; bug-fix.)
;      (cond ((or (and r
;		      (member r (free-vars ref-concl))
;		      (null z))
;		 (and (null r) (null z)))
;	     (ref-error '|must give three new ids|)))
;      (cond ((not (no-duplicates? (remove 'nil (list h z p))))
;	     (ref-error '|new ids must be distinct.|)))
;      (<- ref-children 
;	  (list
;	    (make-child
;	      (append
;		ref-assums
;		(list
;		  (declaration
;		    nil p
;		    (function-term
;		      'FUNCTION nil nil phi Ui))
;		  (declaration
;		    nil h
;		    (function-term
;		      'FUNCTION nil r phi-subset ref-concl))
;		  (declaration
;		    nil z
;		    (substitute
;		      phi-body
;		      (list (list phi-id phi-subset))))))
;	      adjusted-concl)
;	    (make-child
;	      ref-assums
;	      (equal-term 'EQUAL nil Ui (list phi)))))))


;(de refine-simple-rec-elim ()
;    (let* ((assum-num (assum-num-of-simple-rec-elim-rule ref-rule))
;	   (assum (let (assum (check-assum-type$ 'SIMPLE-REC assum-num ref-assums))
;		       (if (null (id-of-declaration assum)) 
;			   --> (ref-error '| the assum must be labelled by an id |) fi)
;		       assum))
;	   (level (level-of-simple-rec-elim-rule ref-rule))
;	   (elim-id (id-of-declaration assum))
;	   (new-ids (let (new-ids (new-ids-of-simple-rec-elim-rule ref-rule))
;			 (for (i in new-ids) (do (check-if-new$ i ref-assums)))
;			 new-ids))
;	   (rec-term (type-of-declaration assum))
;	   (id-of-rec-term (bound-id-of-simple-rec-term rec-term))
;	   (rec-term-term (term-of-simple-rec-term rec-term))
;	   (recly-assumed-type-id
;		(if (null new-ids)
;		    --> (progn (check-if-new$ id-of-rec-term ref-assums)
;			       id-of-rec-term)  ||
;		    t
;		    --> (first new-ids) fi))
;	   (ind-hyp-member  (progn
;			      (or (null elim-id)
;			              (not (memq elim-id (free-vars ref-concl)))
;			              (not (null (third new-ids)))
;			              (ref-error '|must give three new ids|))
;			          (check-if-new$ (second new-ids) ref-assums)
;			          (second new-ids)))
;	   (member-of-unrolling (progn (check-if-new$ (third new-ids) ref-assums)
;					(third new-ids)))
;	   (adjusted-concl
;	     (if (null elim-id)
;		 --> ref-concl ||
;		 t
;		 --> (substitute
;		       ref-concl
;		       `((,elim-id
;			  ,(var-term
;			     'VAR
;			     nil
;			     member-of-unrolling)))) fi)))
;      (cond ((not (no-duplicates?
;		    (list ind-hyp-member member-of-unrolling recly-assumed-type-id)))
;	     (ref-error '|need 3 distinct new ids|)))
;      (<- ref-children 
;          (list
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
;		      elim-id
;		      (var-term 'VAR nil recly-assumed-type-id)
;		      (equal-term
;			'EQUAL
;			nil
;			rec-term
;			(list (var-term 'VAR nil elim-id)))))
;		  (declaration
;		    nil
;		    ind-hyp-member
;		    (function-term
;		      'FUNCTION
;		      nil
;		      elim-id
;		      (var-term 'VAR nil recly-assumed-type-id)
;		      ref-concl))
;		  (declaration
;		    nil
;		    member-of-unrolling
;		    (if (null new-ids)
;			--> rec-term-term  ||
;			t
;			--> (substitute
;			      rec-term-term
;			      (list (list id-of-rec-term
;					  (var-term
;					    'VAR
;					    nil
;					    recly-assumed-type-id)))) fi))))
;	      adjusted-concl)))))







(defun add-declaration-to-prefix (assum-num assum-list new-assum)
    (add-decls-to-prefix$ 1 assum-num assum-list (list new-assum))
)

(defun add-declarations-to-prefix (assum-num assum-list new-assums)
    (add-decls-to-prefix$ 1 assum-num assum-list new-assums)
)

(defun add-decls-to-prefix$ (current-assum assum-num assum-list new-assums)
    (Pif (= current-assum assum-num) -->
        new-assums
     || t -->
        (cons
            (car assum-list)
            (add-decls-to-prefix$
                (1+ current-assum) assum-num (cdr assum-list) new-assums
            )
        )
     fi)
)

(defun check-assum-type$ (elim-type assum-num assum-list)
    (Plet (assum (get-assum$ assum-num assum-list)   
         )
        (Pif (not (eql (kind-of-term (type-of-declaration assum)) elim-type)) -->
            (ref-error '|assumption is not of proper type|)

         || t -->
            assum

         fi)
    )
)

(defun get-assum$ (assum-num assum-list)
    (Pif (member assum-num ref-hidden) -->
        (ref-error '|That assumption is hidden now|)

     || (or
            (< assum-num 1)
            (> assum-num (length assum-list))
        ) -->
        (ref-error '|assumption number is out of range |)

     || t -->
        (nthelem assum-num assum-list)
     fi)
)

(defun check-if-new$ (id assums)
    (Pif (not (null id)) -->
        (for (assum in assums)
             (do
                (Pif (eql id (id-of-declaration assum)) -->
                    (ref-error '|id already occurs in assumptions|)
                 fi)
             )
        )
     fi)
)

(defun check-no-occurrence (id assums)
    (Pif (or (null id) (null assums)) --> 
        t
     || (member id (free-vars (type-of-declaration (car assums)))) -->
        (ref-error '|id of assum being elim-ed occurs in later assums |)
     || t -->
        (check-no-occurrence id (cdr assums))
     fi)
)

(defun check-distinct (&rest id-list)
    (Ploop
        (local len (length id-list))
        (while (> len 1))
        (do
            (Pif (and
                    (not (null (car id-list)))
                    (member (car id-list) (cdr id-list))
                ) -->
                (ref-error '|all new ids provided must be distinct |)
             fi)
            (<- id-list (cdr id-list))
            (<- len (1- len))
        )
    )
)

;-- check-ids (min max id-list)
;-- 
;-- Checks that there are at least min and at most max ids in id-list.  An
;-- error is reported if there less than the min, while extra ids are
;-- ignored.  IT IS ASSUMED THAT max IS ALWAYS LESS THAN 4.  Also makes sure 
;-- that the ids are new.  Returns as multiple values the ids in id-list.
;-- 
(defun check-ids (min max id-list)
    (Plet (len (length id-list))
        (Pif (< len min) -->
            (ref-error (concat "At least " min "new ids must be given"))
         || (> len max) -->
            (display-message '#.(istring "Extra ids being ignored"))
            (<- len max)
         fi)
        (Ploop
            (while (> len 0))
            (do
                (check-if-new$ (nthelem len id-list) ref-assums)
                (<- len (1- len))
            )
        )
        (values
            (nthelem 1 id-list)
            (nthelem 2 id-list)
            (nthelem 3 id-list)
        )
    )
)

(defun occurs-free-in-assumption-list (id assum-list)
    (Ploop
        (local
            assumption                nil
            free-occurrence-found     nil
        )
        (while (and (not (null assum-list)) (not free-occurrence-found)))
        (do
            (<- assumption (car assum-list))
            (<- free-occurrence-found
                (occurs-free-in-term
                    id
                    (type-of-declaration assumption)
                )
            )
            (<- assum-list (cdr assum-list))
        )
        (result free-occurrence-found)
    )
)

(defun occurs-free-in-term (id term)
    (member id (free-vars term))
)

(defun already-declared (id assums)
    (Ploop
	(while (and
		   (not (null assums))
		   (not (eql id (id-of-declaration (car assums))))
	       )
	)
	(do (<- assums (cdr assums)))
	(result (not (null assums)))
    )
)
