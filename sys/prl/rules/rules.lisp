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


(defun refine-hyp ()
    (Plet (assum-num (assum-num-of-hyp-rule ref-rule)
          assum     nil
         )
        (<- assum (get-assum$ assum-num ref-assums))
        (Pif (not (equal-terms ref-concl (type-of-declaration assum))) -->
            (ref-error '|assum indicated does not properly match conclusion |)
         fi)
        nil
    )
)

;--
;-- refine-lemma ()
;--
;--     Do work of refine for LEMMA reference rule.
;--

(defun refine-lemma ()

    (Plet (lemma     (lemma-of-lemma-rule ref-rule)
                            ;-- name of lemma being referenced
          new-id    (new-id-of-lemma-rule ref-rule)
          obj       nil     ;-- the object associated with the name OBJ-lemma
          proof     nil     ;-- the proof-tree of the lemma 
          assum-map nil     ;-- for each assumption, number i, of proof,
                            ;--   assum-map(i) is the assum number of the
                            ;--   matching assumption in this goal
          a-num     0       ;-- num of assum in lemma     -+
          ra-num    0       ;-- num of assum in ref-assum  | used in
          r-assums  nil     ;-- unexamined assumptions     | Ploop below
          found     nil     ;-- true when a is found      -+
         )

        (Pif (not (lib-member lemma)) -->
            (ref-error '|Named lemma not present in the library.|)
         fi)

        (<- obj (library-object lemma))

        (Pif (not (equal (sel (object obj) kind) 'THM)) -->
            (ref-error '|Named entity is not a THM object.|)
         fi)

        (Pif (not (eql (sel (object obj) status) 'COMPLETE)) -->
            (ref-error 
                '|Named lemma has unacceptable status (must be complete).|
            )
         fi)

        ;;(<- proof (get-proof-of-theorem-object (sel (object obj) value)))

;        ;-- see if the lemma's assumptions are a subset of ref-assum and
;        ;-- build assum-map showing which elements of ref-assum they are
;            (<- a-num 1)
;            (for
;                (a in (assumptions-of-proof-tree proof))
;                (do
;                    (<- ra-num 1)
;                    (<- r-assums ref-assums)
;                    (<- found nil)
;                    (Ploop
;                        (while (and (not found)
;                                    (not (null r-assums))
;                               )
;                        )
;                        (do
;                            (Pif (and (eql (id-of-declaration a)
;                                         (id-of-declaration (car r-assums))
;                                     )
;                                     (equal-terms 
;                                        (type-of-declaration a)
;                                        (type-of-declaration (car r-assums))
;                                     ) 
;                                ) -->
;                                (<- found t)
;                             || t -->
;                                (<- r-assums (cdr *-*))
;                                (<- ra-num (add1 *-*))
;                             fi)
;                        )
;                    )
;                    (Pif (not found) -->
;                        (ref-error (concat '|Assumption number |
;                                           a-num
;                                           '| of lemma does not occur in|
;                                           '| the assumptions of this goal.|
;                                   )
;                        )
;                     fi)
;                    (<- assum-map (cons ra-num assum-map))
;                    (<- a-num (add1 *-*))
;                )
;            )
;            (<- assum-map (reverse assum-map))
          
;        (Pif (equal-terms (conclusion-of-proof-tree proof)
;                         ref-concl
;            ) -->
;            ;-- conclusions match
;                (<- ref-rule (lemma-rule 'LEMMA lemma nil assum-map 'MATCH))
;
;            ;-- make the unproved leaves of the lemma (Pif any)
;            ;-- be the children of this goal
;                (<- ref-children (unproved-leaves$ proof))
;               
;         || t -->
;            ;-- conclusions don't match.  
                (<- ref-rule (lemma-rule 'LEMMA lemma new-id assum-map nil))            
                                                   
            ;-- Make sure the new-id (Pif non-nil) is really new.
                (check-if-new$ new-id ref-assums)

            ;-- Make the conclusion of the lemma the conclusion of the 
            ;-- first (new) subgoal of this goal.  If the lemma is imcomplete
            ;-- grab its unproved leaves and make them children of the goal too.
                (<- ref-children
                    (cons
                        (make-child
                            (append 
                                ref-assums
                                (list 
                                    (declaration
                                        nil
                                        new-id
                                        (get-conclusion-of-theorem-object
					  (sel (object obj) value)
					)
                                    )
                                )
                            )
                            ref-concl
                        )
;                       ;;;;(unproved-leaves$ proof)
                        nil
                    )
                )


;             fi)
    )
    nil
)

;--
;-- unproved-leaves$ (p:proof-tree)
;--
;--     Return a list of the leaves of p that are unproved.
;--     This list will not share any modifiable structure with p.
;--     The list is in left-to-right order, i.e., it is
;--     the frontier of p with proved leaves left out.
;--

(defun unproved-leaves$ (p)

    (Pif (null (rule-of-proof-tree p)) -->
	(Plet (new (copy-list p))
	    (<- (rule-body-of-proof-tree new) (copy (rule-body-of-proof-tree p)))
	    (ncons new)
	)

     || t -->
        (mapcan #'unproved-leaves$ (children-of-proof-tree p))

     fi)
)





;-- refine-def
;--
(defun refine-def ()
    (Plet (theorem         (theorem-of-def-rule ref-rule)
                              ;-- name of theorem being referenced
          new-id          (new-id-of-def-rule ref-rule)
          obj             nil ;-- the object associated with the name OBJ-lemma
          proof           nil ;-- the proof tree associated with this theorem
          extracted-term  nil ;-- the term extracted form this theorem
         )

        (check-if-new$ new-id ref-assums)

        (Pif (not (lib-member theorem)) -->
            (ref-error '|Named theorem not present in the library.|)
         fi)

        (<- obj (library-object theorem))

        (Pif (not (equal (sel (object obj) kind) 'THM)) -->
            (ref-error '|Named entity is not a THM object.|)
         fi)

        (Pif (not (member (sel (object obj) status) '(COMPLETE))) -->
            (ref-error '|Named lemma has unacceptable status.|)
         fi)
                                                                             
;        (<- proof (save-refiner-state-and-get-proof obj))
;
;        (Pif (not (null (assumptions-of-proof-tree proof))) -->
;            (ref-error '|named theorem must have no assumptions |)
;         fi)

        (<- extracted-term (term-of-theorem theorem))
        (Pif (not (null (free-vars-not-declared extracted-term ref-assums))) -->
            (ref-error
                  '|not all free vars in the extracted term have been declared |
            )
         fi)

        (<- ref-children 
            (list (make-child (append 
                                ref-assums
                                (list (declaration
                                         nil
                                         new-id
                                         (equal-term
                                            'EQUAL
                                            nil
                                            (get-conclusion-of-theorem-object
					      (sel (object obj) value))
                                            (list (term-of-theorem-term
                                                     'TERM-OF-THEOREM
                                                     nil
                                                     theorem
                                                  )
                                                  extracted-term
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
    nil
)


;(defun save-refiner-state-and-get-proof (obj)
;    (Plet (save-assums ref-assums
;	  save-concl  ref-concl
;	  save-rule   ref-rule
;	  save-hidden ref-hidden
;	 )
;	 (prog1
;	     (get-proof-of-theorem-object (sel (object obj) value))
;	     (<- ref-assums save-assums)
;	     (<- ref-concl save-concl)
;	     (<- ref-rule  save-rule)
;	     (<- ref-hidden save-hidden)
;	 )
;     )
;)


;-- refine-sequence

(defun refine-sequence ()
    (Plet (assums   ref-assums  
          new-ids  (new-ids-of-sequence-rule ref-rule)
         )
        (Pif new-ids -->
            (apply #'check-distinct new-ids)
         fi)
        (<- ref-children nil)
        (for (term in (terms-of-sequence-rule ref-rule))
             (do                          
                (check-if-new$ (car new-ids) assums)
                (Pif (not (null (free-vars-not-declared term assums))) -->
                    (ref-error (concat '|not all free vars. of some seq-rule |
                                 '|term have been (or will have been) declared |
                               )
                    )
                 fi)
                (<- ref-children
                    (append *-*
                            (list (make-child
                                      assums
                                      term
                                  )
                            )
                    )
                )
                (<- assums 
                       (append *-* (list (declaration nil (car new-ids) term)))
                )
                (<- new-ids (cdr new-ids))
            )
        )
        (<- ref-children
            (append *-*
                    (list (make-child
                              assums
                              ref-concl
                          )
                    )
            )
        )

    )
    nil
)

(defun refine-explicit-intro ()
    (Pif (not (null (free-vars-not-declared
                       (term-of-explicit-intro-rule ref-rule)
                       ref-assums
                   )
             )
        ) -->
        (ref-error '|term introduced contains undeclared variables |)
     fi)
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                   'EQUAL
                                   nil
                                   ref-concl
                                   (list (term-of-explicit-intro-rule ref-rule))
                                )
                           )
                     )
    )
    nil
)

(defun refine-cumulativity ()
    (Pif (not (and (eql (kind-of-term ref-concl) 'EQUAL)
                  (eql (kind-of-term (type-of-equal-term ref-concl)) 'UNIVERSE)
             )
        ) -->
        (ref-error '|conclusion not appropriate for cumulativity rule |)

     || (<= (level-of-universe-term (type-of-equal-term ref-concl))
	    (level-of-cumulativity-rule ref-rule)) -->
        (ref-error '|universe level too high in cumulativity|)
     fi)
    
    (<- ref-children (list (make-child
                                ref-assums
                                (equal-term
                                   'EQUAL
                                   nil
                                   (universe-term
                                        'UNIVERSE
                                        nil
                                        (level-of-cumulativity-rule ref-rule)
                                   )
                                   (terms-of-equal-term ref-concl)
                                )
                           )         
                     )
    )
    nil
)
            
(defun refine-equality ()
    (Plet (equalities-to-check  nil
          equality-classes     nil
          type                 nil
          types                nil
          terms                nil
         )
         
        (check-concl-kind$)
        (<- type (type-of-equal-term ref-concl))
        (<- equalities-to-check (list (list type)))
        (for (assum in ref-assums)
             (do
                (Pif (and (eql (kind-of-term (type-of-declaration assum)) 'EQUAL)
                         (eql (kind-of-term 
                                (type-of-equal-term (type-of-declaration assum))
                             )
                             'UNIVERSE
                         )
                    ) -->
                    (<- equalities-to-check  
                        (cons (terms-of-equal-term (type-of-declaration assum))
                              equalities-to-check
                        )
                    )    

                 fi)
             )
        )
        (<- equality-classes (merge-equalities$ equalities-to-check))
        (<- types 
            (set-union (mapcar #'(lambda (x)    
                                   (list-to-set
                                        (Pif (equal-terms-with-any$ type x) --> x
                                         || t --> nil
                                         fi)
                                   )
                                )           
                               equality-classes
                        )
            )
        )

        (<- terms (terms-of-equal-term ref-concl))   
        (<- equalities-to-check nil) 
        (for (assum in ref-assums)
             (do
                (Pif (and (eql (kind-of-term (type-of-declaration assum)) 'EQUAL)
                         (equal-terms-with-any$ (type-of-equal-term 
                                                    (type-of-declaration assum)
                                                )
                                                types
                         )
                    ) -->                 
                    (<- equalities-to-check 
                        (append *-* (list (terms-of-equal-term
                                             (type-of-declaration assum)
                                          )
                                    )
                        )
                    )

                 || (equal-terms-with-any$ 
                        (type-of-declaration assum) types
                    ) -->
                    (<- equalities-to-check
                        (append *-*  
                                (list (list
                                   (var-term 'VAR nil (id-of-declaration assum))
                                )     )
                        )
                    )
                 fi)
             )
        )
        (<- equality-classes (merge-equalities$ equalities-to-check))

        (Pif (subset-of-none$ terms equality-classes) -->
            (ref-error '| conclusion cannot be obtained by equality |)
         fi)
    )
    nil
)                                                  

(defun merge-equalities$ (equalities-to-check)
    (Plet (curr-equality    nil
          classes-to-merge nil
          equality-classes nil
         )
        (Ploop (while equalities-to-check)
              (do
                 (<- curr-equality (car equalities-to-check))
                 (<- classes-to-merge (list curr-equality))
                 (for (class in equality-classes)
                      (do
                         (Pif (non-null-intersection$ curr-equality class) -->
                             (<- classes-to-merge (cons class classes-to-merge))
                          fi)

                      )
                 )                                               
                 (<- equality-classes 
                     (cons
                         (merge-classes classes-to-merge)
                         equality-classes
                     )
                 )
                 (<- equalities-to-check (cdr equalities-to-check))
              )
        )
        equality-classes
    )
)

(defun equal-terms-with-any$ (term term-list)              
    (Pif (null term-list) --> 
        nil

     || (onep (length term-list)) -->
        (equal-terms term (car term-list))

     || t -->
        (or (equal-terms term (car term-list))
            (equal-terms-with-any$ term (cdr term-list))
        )

     fi)
)

(defun non-null-intersection$ (term-list1 term-list2)
    (Ploop
        (local
            term1  nil
            found  nil
        )
        (while (and (not found) (not (null term-list1))))
        (do
            (<- term1 (car term-list1))
            (Ploop
                (local
                    term2    nil
                    temp     term-list2
                )
                (while (and (not found) (not (null temp))))
                (do
                    (<- term2 (car temp))
                    (Pif (equal-terms term1 term2) -->
                        (<- found t)
                     fi)
                    (<- temp (cdr temp))
                )
            )
            (<- term-list1 (cdr term-list1))
        )
        (result found)
    )
)

(defun merge-classes (class-list)
    (Pif (not (null class-list)) -->
        (Ploop
            (local
                answer    nil
                class     nil
            )
            (while (not (null class-list)))
            (do
                (<- class (car class-list))
                (Ploop
                    (local
                        elem   nil
                    )
                    (while (not (null class)))
                    (do
                        (<- elem (car class))
                        (Ploop
                            (local temp answer)
                            (while
                                (and
                                    (not (null temp))
                                    (not (equal-terms elem (car temp)))
                                )
                            )
                            (do
                                (<- temp (cdr temp))
                            )
                            (result
                                (Pif (null temp) -->
                                    (<- answer (cons (car class) *-*))
                                 fi)
                            )
                        )
                        (<- class (cdr class))
                    )
                )
                (<- class-list (cdr class-list))
            )
            (result answer)
        )
     || t --> nil
     fi)
)

(defun subset-of-none$ (list list-of-lists)
    (Plet (result t)
        (for (eq-list in list-of-lists)
             (do
                (Pif (subset-of$ eq-list list) -->
                    (<- result nil)
                 fi)
             )
        )
        result
    )
)

(defun check-if-equal-terms$ (term-list)
    (Ploop
        (local
            term1              (car term-list)
            term2              nil
            found-disequality  nil
        )
        (while (and (not (null (cdr term-list))) (not found-disequality)))
        (do
            (<- term2 (cadr term-list))
            (<- found-disequality (not (equal-terms term1 term2)))
            (<- term-list (cdr term-list))
            (<- term1 term2)
        )
        (result found-disequality)
    )
)

;-- not a general subset function

(defun subset-of$ (list sublist)
    (Plet (result t
          found  nil
         )
        (for (elem in sublist)
             (do
                (<- found nil)
                (for (lelem in list)
                    (do 
                        (Pif (equal-terms elem lelem) -->
                            (<- found t)
                         fi)
                    )
                )
                (Pif (not found) -->
                    (<- result nil)
                 fi)
             )
        )
        result
    )
)

;(defun refine-substitute ()
;    (Plet (level      (level-of-substitute-rule ref-rule)
;          pair-list  (make-pair-list$                     
;                           (bound-ids-of-bound-id-term
;                              (bound-id-term-of-substitute-rule ref-rule)
;                           )
;                           (terms-of-equal-term
;                              (equality-term-of-substitute-rule ref-rule)
;                           )
;                     )                       
;          bound-vars (bound-ids-of-bound-id-term
;                            (bound-id-term-of-substitute-rule ref-rule)
;                     )
;          bare-concl (term-of-bound-id-term 
;                           (bound-id-term-of-substitute-rule ref-rule)
;                     )
;          type       (type-of-equal-term 
;                                  (equality-term-of-substitute-rule ref-rule)
;                     )  
;          new-id     (new-id-of-substitute-rule ref-rule)
;         )
;        (Pif (not (null (free-vars-not-declared 
;                           (equality-term-of-substitute-rule ref-rule) ref-assums
;                       )
;                 )
;            ) -->
;            (ref-error
;             '|not all free vars. in the equality provided have been declared.|
;            )
;         fi)
;        (Pif (not (equal-terms ref-concl (substitute bare-concl pair-list))) -->
;            (ref-error '|concl not appropriate for this rule |)
;         fi)
;        (check-if-new$ new-id ref-assums)
;        (<- ref-children
;            (list (make-child
;                        ref-assums
;                        (equality-term-of-substitute-rule ref-rule)
;                  )
;                (Plet (new-concl
;                        (substitute
;                            bare-concl
;                            (mapcar #'(lambda (x)
;                                         (list x 
;                                             (var-term 'VAR nil new-id)
;                                         )
;                                     )
;                                     bound-vars
;                            )
;                        )
;                     )
;                    (make-child
;                        (append ref-assums
;                                (list (declaration
;                                            nil
;                                            new-id
;                                            type
;                                      )
;                                )
;                        )
;                        new-concl
;                    )
;                )
;                (Plet (new-assums (append ref-assums
;                                         (mapcar #'(lambda (x)
;                                                    (declaration nil x type)
;                                                  )
;                                                  bound-vars
;                                         )
;                                 )
;                     )
;                     (make-child new-assums 
;                                 (equal-term 'EQUAL   
;                                             nil
;                                             (universe-term 'UNIVERSE nil level)
;                                             (list bare-concl)
;                                 )
;                     )
;                )
;            )
;        )
;    )
;    nil
;)


(defun refine-substitute ()
    (let* ((level      (level-of-substitute-rule ref-rule))
	   (equality (equality-term-of-substitute-rule ref-rule))
	   (equands (terms-of-equal-term equality))
	   (term-to-replace (first equands))
	   (replacing-term (second equands))
	   (over-pair (bound-id-term-of-substitute-rule ref-rule))
	   (over-id (first (bound-ids-of-bound-id-term over-pair)))
	   (over-term (term-of-bound-id-term over-pair))
	   (equality-type (type-of-equal-term equality)))
      (Pif (not (null (free-vars-not-declared equality ref-assums)))
	  --> (ref-error
		'|not all free vars. in the equality provided have been declared.|) fi)
      (Pif (not (equal-terms ref-concl (substitute over-term
						 `((,over-id ,term-to-replace)))))
	  --> (ref-error '|concl not appropriate for this rule |) fi)
      (check-if-new$ over-id ref-assums)
      (<- ref-children
	  (list (make-child
		  ref-assums
		  equality)
		(make-child
		  ref-assums
		  (substitute over-term `((,over-id ,replacing-term))))
		(make-child
		  (append ref-assums
			  (list (declaration nil over-id equality-type)))
		  (equal-term 'EQUAL   
			      nil
			      (universe-term 'UNIVERSE nil level)
			      (list over-term)))))
      nil))



(defun make-pair-list$ (ids terms)
    (Pif (null ids) --> 
        nil
     || t --> 
        (cons (list (car ids) (car terms)) 
              (make-pair-list$ (cdr ids) (cdr terms))
        )
     fi)
)

(defun refine-arith ()
    (Plet (result (arith ref-assums ref-concl nil)   
         )
        (Pif (eql result 'GOOD) -->
            (<- ref-children (get-arith-children$))
         || t -->
            (ref-error result)
         fi)
    )
    nil
)

(defun get-arith-children$ ()
    (mapcar #'(lambda (x) (make-child
                            ref-assums
                            (equal-term
                                'EQUAL
                                nil
                                (cadr x)
                                (list (car x))
                            )
                         )
             )
            (get-relevant-parts$ ref-concl)
    )
)

(defun get-relevant-parts$ (term)
    (declare (special type-int$))
    (Pif (eql (kind-of-term term) 'UNION) -->
        (append (get-relevant-union-parts$ (lefttype-of-union-term term))
                (get-relevant-union-parts$ (righttype-of-union-term term))
        )

     || (not-term$ term) -->
        (get-relevant-parts$ (lefttype-of-function-term term))

     || (and (eql (kind-of-term term) 'EQUAL)
             (equal-terms (type-of-equal-term term) type-int$)
             (not (onep (length (terms-of-equal-term term))))
        ) -->
        (mapcar #'(lambda (x) (list x type-int$))
                (terms-of-equal-term term) 
        )

     || (eql (kind-of-term term) 'LESS) -->
        (list (list (leftterm-of-less-term term) type-int$)
              (list (rightterm-of-less-term term) type-int$)
        )

     || t -->
        nil

     fi)
)

(defun get-relevant-union-parts$ (term)
    (Plet (result (get-relevant-parts$ term)
         )
        (Pif result -->  
            result
         || t --> 
            (list (list term 
                        (universe-term 
                            'UNIVERSE 
                            nil 
                            (level-of-arith-rule ref-rule)
                        )
                  )
            )
         fi)
    )
)

(defun refine-because ()
  (declare (special *because-rule-enabled?*))
  (unless *because-rule-enabled?*
    (ref-error '|because rule is disabled|)))

(defun refine-thinning ()
    (let* ((assums-to-delete (propagate-thinning$ () () 1 ref-assums)))
      (<- ref-hidden (prl-set-difference *-* assums-to-delete))
      (<- ref-hidden
	  (mapcar #'(lambda (x) (- x
				   (length (remove-if-not #'(lambda (y) (< y x))
						   assums-to-delete))))
		  ref-hidden))
      (<- ref-children
	  (list
	    (make-child (thin-list$ 1 ref-assums assums-to-delete)
			ref-concl)))
      nil))



;;; The call in refine-thinning does a left to right processing of the
;;; assumption list to compute the minimal set of assumptions which
;;; contains the assumptions specified in the thinning rule and whose
;;; deletion results in a closed sequent, (throwing an error if no such
;;; set exists). Result returned in order.

(defun propagate-thinning$
    (thinned-vars thinned-assums next-assum-num remaining-assums)
    (Pif (null remaining-assums)
	--> (Pif (intersection (free-vars ref-concl) thinned-vars)
		--> (ref-error
		      '|thinning would result in conclusion having free variables|) ||
		t
		--> (reverse thinned-assums)  fi) ||
	t
	--> (let* ((id (id-of-declaration (car remaining-assums)))
		   (type (type-of-declaration (car remaining-assums))))
	      (Pif (or (member next-assum-num
			      (assum-num-list-of-thinning-rule ref-rule))
		      (intersection (free-vars type) thinned-vars))
		  --> (propagate-thinning$
			(Pif (eql 'NIL id) --> thinned-vars ||
			    t --> (cons id thinned-vars) fi)
			(cons next-assum-num thinned-assums)
			(1+ next-assum-num)
			(cdr remaining-assums)) ||
		  t
		  --> (propagate-thinning$
			thinned-vars
			thinned-assums
			(1+ next-assum-num)
			(cdr remaining-assums)) fi)) fi))


(defun thin-list$ (next-assum-num remaining-assums remaining-thin-nums)
    (Pif (null remaining-assums)
	--> ()  ||
	(null remaining-thin-nums)
	--> remaining-assums  ||
	(eql next-assum-num (car remaining-thin-nums))
	--> (thin-list$ (1+ next-assum-num)
			(cdr remaining-assums)
			(cdr remaining-thin-nums))  ||
	t
	--> (cons (car remaining-assums)
		  (thin-list$ (1+ next-assum-num)
			      (cdr remaining-assums)
			      remaining-thin-nums)) fi))

