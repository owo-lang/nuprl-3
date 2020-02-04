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


(defun parse-rule$ ()
    (scan)
    (Plet (rule-type token-type
          rule-name token-val
         )
        (scan)
        (Pif (eql rule-type TEndInput) -->
            nil

         || (eql rule-name '|intro|) -->

            (Pif (eql (kind-of-term ref-concl) 'UNIVERSE) -->
                (parse-univ-intro-rule)

             || (eql (kind-of-term ref-concl) 'VOID) -->
                (ref-error '|there is no intro rule for the void type |)

             || (eql (kind-of-term ref-concl) 'ATOM) -->
                (parse-atom-intro-rule)

             || (eql (kind-of-term ref-concl) 'INT) -->
                (parse-int-intro-rule)

             || (eql (kind-of-term ref-concl) 'LIST) -->
                (parse-list-intro-rule)

             || (eql (kind-of-term ref-concl) 'UNION) -->
                (parse-union-intro-rule)
                                      
             || (eql (kind-of-term ref-concl) 'PRODUCT) -->
                (parse-product-intro-rule)

             || (eql (kind-of-term ref-concl) 'FUNCTION) -->
                (parse-function-intro-rule)
  
             || (eql (kind-of-term ref-concl) 'QUOTIENT) -->
                (parse-quotient-intro-rule)

	     || (eql (kind-of-term ref-concl) 'RECURSIVE) -->
	        (parse-recursive-intro-rule)

	     || (eql (kind-of-term ref-concl) 'SIMPLE-REC) -->
	        (parse-simple-rec-intro-rule)

             || (eql (kind-of-term ref-concl) 'SET) -->
                (parse-set-intro-rule)      

             || (eql (kind-of-term ref-concl) 'EQUAL) -->
                (parse-eq-intro-rule)

             || (eql (kind-of-term ref-concl) 'LESS) -->
                (parse-less-intro-rule)

             || t -->
                (ref-error '|intro rule not applicable here |)

             fi)

         || (eql rule-name '|elim|) -->
	    (parse-elim-rule)

	 || (eql rule-name '|unroll|) -->
	    (parse-simple-rec-unroll-elim-rule)

         || (eql rule-name '|reduce|) -->
            (parse-computation-rule)
          
         || (eql rule-name '|hyp|) -->
            (parse-hyp-rule)

         || (eql rule-name '|seq|) -->
            (parse-sequence-rule)    

         || (eql rule-name '|lemma|) -->
            (parse-lemma-rule)         

         || (eql rule-name '|def|) -->
            (parse-def-rule)

         || (eql rule-name '|explicit|) -->
            (parse-explicit-intro-rule)

         || (eql rule-name '|cumulativity|) -->
            (parse-cumulativity-rule)
        
         || (eql rule-name '|equality|) -->
            (parse-equality-rule)

         || (eql rule-name '|subst|) -->
            (parse-substitute-rule)
    
         || (eql rule-name '|arith|) -->
            (parse-arith-rule)

	 || (eql rule-name '|extensionality|) -->
	    (parse-extensionality-rule)

         || (eql rule-name '|because|) --> ;;; in lieu of equality and arith and
            (parse-because-rule)          ;;; anything else that's not yet in
	    
         || (eql rule-name '|compute|) -->
            (parse-direct-comp-rule)
	    
         || (eql rule-name '|thinning|) -->
	    (parse-thinning-rule)

	 || (eql rule-name '|monotonicity|) -->
	    (parse-monot-rule)

	 || (eql rule-name '|division|) -->
	    (parse-division-rule)

	 || (eql rule-name '|experimental|)  -->
	    (parse-experimental-rule)

	 || (and (symbolp rule-name)
		 (get rule-name 'parse-function)) -->
	    (funcall (get rule-name 'parse-function))

         || t -->
            ;-- Assume this is a tactic.  The tactic mechanism is
            ;-- responsible for parsing the rule.
                (tactic-rule 'TACTIC ref-rule-body nil)

;-- The following isn't needed since errors will be caught by tactics
;         || (not (eql token-type TEndInput)) -->
;            (ref-error (concat '|expecting 'intro','elim', 'hyp','seq','lemma',|
;                               '| 'def', or 'explicit intro' |
;                       )
;            )
;
;         || t -->
;            (ref-help (concat '|need 'intro','elim','hyp','seq','lemma', 'def',|
;                              '|or 'explicit intro' as first part of rule text |
;                      )
;            )

         fi)
    )
)

(defun parse-elim-rule ()
    (Pif (eql token-type TNbr) -->
	(Pif (or (< token-val 1) 
		(> token-val (length ref-assums))
	    ) -->
	    (ref-error '|assum. num after 'elim' is out of range.|)

	 || t -->     
	    (choose-elim-rule token-val)

	 fi)

     || (eql token-type TId) -->
	(choose-elim-rule (assum-id-to-assum-num token-val ref-assums))

     || (not (eql token-type TEndInput)) -->
	(ref-error '|expecting an assum. number or id after 'elim'|)

     || t -->
	(ref-help '|need an assum. number or an id after 'elim'|)

     fi)
)

(defun choose-elim-rule (assum-num)
    (Pif (member assum-num ref-hidden) -->
        (ref-error '|That assumption is hidden now|)
     fi)
    (Plet (elim-kind
             (kind-of-term 
                 (type-of-declaration (nthelem assum-num ref-assums))
             )
         )
        (scan)   ;-- skip assum number.
        (Pif (eql elim-kind 'UNIVERSE) -->
            (ref-error '|there is no elim. rule for universes |)

         || (eql elim-kind 'VOID) -->
            (parse-void-elim-rule assum-num)
                                           
         || (eql elim-kind 'ATOM) -->
            (ref-error '|there is no elim. rule for atom type |)

         || (eql elim-kind 'INT) -->                   
            (parse-int-elim-rule assum-num)

         || (eql elim-kind 'LIST) -->
            (parse-list-elim-rule assum-num)

         || (eql elim-kind 'UNION) -->
            (parse-union-elim-rule assum-num)

         || (eql elim-kind 'PRODUCT) -->
            (parse-product-elim-rule assum-num)
                                                       
         || (eql elim-kind 'FUNCTION) -->
            (parse-function-elim-rule assum-num)

         || (eql elim-kind 'QUOTIENT) -->
            (parse-quotient-elim-rule assum-num)

         || (eql elim-kind 'SET) -->
            (parse-set-elim-rule assum-num)

	 || (eql elim-kind 'RECURSIVE) -->
	    (parse-recursive-elim-rule assum-num)

	 || (eql elim-kind 'SIMPLE-REC) -->
	    (parse-simple-rec-elim-rule assum-num)

	 || (eql elim-kind 'PARFUNCTION) -->
	    (parse-parfunction-elim-rule assum-num)

         || (eql elim-kind 'EQUAL) -->
            (ref-error '|there is no elim. rule for equality type |)

         || t -->
            (ref-error '|elim rule not applicable here |)

         fi)
    )   
)

(defun parse-univ-intro-rule ()
    (Plet (current-type token-type
          current-val  token-val
         )
        (scan)  ;-- skip type name
        (Pif (eql current-type TVoid) -->
            (univ-intro-rule 'UNIVERSE-INTRO-VOID)
            
         || (eql current-type TInt) -->
            (univ-intro-rule 'UNIVERSE-INTRO-INT)
            
         || (eql current-type TAtom) -->
            (univ-intro-rule 'UNIVERSE-INTRO-ATOM)
            
         || (eql current-type TList) -->
	    (univ-intro-rule 'UNIVERSE-INTRO-LIST)
            
         || (eql current-type TUnion) -->
            (univ-intro-rule 'UNIVERSE-INTRO-UNION)
            
         || (eql current-type TProduct) -->
            (Pif (eql token-type TEndInput) -->
                (univ-intro-rule-product 'UNIVERSE-INTRO-PRODUCT nil nil)
             || t -->
                (Plet (term (check-for-term$ '|need a term after 'product'|))
                    (check-token-type TNew)
                    (Plet (ids (get-n-ids$ 1))
                        (univ-intro-rule-product 'UNIVERSE-INTRO-PRODUCT (car ids) term)
                    )
                )
             fi)
        
         || (eql current-type TFunction) -->
            (Pif (eql token-type TEndInput) -->  
                (univ-intro-rule-function 'UNIVERSE-INTRO-FUNCTION nil nil)
             || t -->
                (Plet (term (check-for-term$ '|need a term after 'function'|))
                    (check-token-type TNew)
                    (Plet (ids (get-n-ids$ 1))
                        (univ-intro-rule-function 'UNIVERSE-INTRO-FUNCTION (car ids) term)
                    )
                )
             fi)

         || (eql current-type TQuotient) -->
            (Plet (term (check-for-term$ '|need a term after 'quotient'|))
                (check-token-type TComma)
                (Plet (term2 (check-for-term$ '|need a term after the comma |))
                    (Plet (new-ids (get-n-new-ids$ 3))
                        (Pif (null new-ids) -->
                            (ref-help '| need 3 new ids for univ. intro quotient. |)
                         fi)
                        (univ-intro-rule-quotient 
                            'UNIVERSE-INTRO-QUOTIENT term term2 new-ids
                        )
                    )
                )
            )

         || (eql current-type TSet) -->
            (Pif (eql token-type TEndInput) -->
                (univ-intro-rule-set 'UNIVERSE-INTRO-SET nil nil)
             || t -->
                (Plet (term (check-for-term$ '|need a term after 'set'|))
                    (check-token-type TNew)
                    (Plet (ids (get-n-ids$ 1))
                        (univ-intro-rule-set 'UNIVERSE-INTRO-SET (car ids) term)
                    )
                )
             fi)
         || (eql current-val '|equality|) -->
            (Plet (term (check-for-term$ '|need a term after 'equality' |))
                (Pif (eql token-type TEndInput) -->
                    (univ-intro-rule-equal 'UNIVERSE-INTRO-EQUAL term 1)
                 || (not (eql token-type TNbr)) -->
                    (ref-error '|expecting a number or nothing after the term |)
                 || t -->
                    (Plet (level token-val)
                        (scan)
                        (univ-intro-rule-equal 'UNIVERSE-INTRO-EQUAL term level)
                    )
                 fi)
            )

         || (eql current-val '|less|) -->
            (univ-intro-rule 'UNIVERSE-INTRO-LESS)

         || (eql current-val '|universe|) -->
           (Plet (term (check-for-term$ '|need a universe-term |))
               (Pif (not (eql (kind-of-term term) 'UNIVERSE)) -->
                   (ref-error '|a universe term must follow 'universe' |)
                fi)
               (univ-intro-rule-universe 'UNIVERSE-INTRO-UNIVERSE 
                   (level-of-universe-term term)
               )
           )

         || (eql current-type TEndInput) -->
            (ref-help (concat '|need one of 'void','int','atom','list',|
                              '|'union','product','function','quotient'|
                              '|,'subset','equality', or 'universe' |
                      )
            )
         || t -->
            (ref-error (concat '|expecting one of 'void','int','atom','list',|
                               '|'union','product','function','quotient'|
                               '|,'subset','equality', or 'universe' |
                      )
            )

         fi)
    )
)               

(defun parse-int-intro-rule ()
    (Pif (eql token-type TEndInput) -->
        (ref-help '|need a signed integer constant or one of +,-,*,/,mod |)
     || t -->
        (Plet (current-type token-type
              current-val  token-val
             )
            (scan)
            (Pif (eql current-type TNbr) -->
                (int-intro-rule 'INT-INTRO-NUMBER current-val)
             || (eql current-type TMinus) -->
                (Pif (eql token-type TEndInput) -->
                    (int-intro-rule 'INT-INTRO-OP current-type)
                 || (eql token-type TNbr) -->
                    (Plet (val token-val)
                        (scan)
                        (int-intro-rule 'INT-INTRO-NUMBER (- val))
                    )
                 || t -->
                    (ref-error '|expecting a number after '-'| )
                 fi)
             || (not (member current-type (list TPlus TStar TSlash TMod))) -->
                (ref-error (concat '|expecting a signed integer constant or |
                                    '|one of +,-,*,/,mod after 'intro' |
                           )
                )
             || t --> 
                (int-intro-rule 'INT-INTRO-OP current-type)
             fi)
        )
     fi)
)

(defun parse-atom-intro-rule ()
    (Plet (term (check-for-term$ '|need a token-term  after 'intro' |))
        (Pif (not (eql (kind-of-term term) 'TOKEN)) -->
             (ref-error '|need a token-term after 'intro'|)
         || t -->
            (atom-intro-rule 'ATOM-INTRO term)
         fi)
    )
)

(defun parse-list-intro-rule ()
    (Pif (eql token-type TEndInput) -->
        (ref-help '|need nil-term or a period (for cons) |)
     || t -->
        (Plet (current-type token-type)
            (scan)
            (Pif (eql current-type TNil) -->
                (list-intro-rule 'LIST-INTRO-NIL (check-for-univ-level$))
                
             || (eql current-type TPeriod) -->
                (list-intro-rule 'LIST-INTRO-CONS nil)

             || t -->
                (ref-error '|expecting nil-term or period (for cons)|)
             fi)
        )
     fi)
)

(defun parse-product-intro-rule ()
    (Pif (null (bound-id-of-product-term ref-concl)) -->
        (product-intro-rule 'PRODUCT-INTRO nil nil nil)
     || t -->
        (Plet (level (check-for-univ-level$))
            (Plet (term (check-for-term$ '|need a term after '.. at U(..) |))
                (Plet (new-ids (get-n-new-ids$ 1))
                    (product-intro-rule
                        'PRODUCT-INTRO level term (set-new-id$ new-ids)
                    )
                )
            )
        )
     fi)
)

(defun parse-union-intro-rule ()
    (Plet (level (check-for-univ-level$))
        (Pif (eql token-type TEndInput) -->
            (ref-help '|need 'left' or 'right' |)
         || (not (member token-type (list TLeft TRight))) -->
            (ref-help '|expecting 'left' or 'right' after ..at U(..) |)
         || t -->
            (Plet (current-type token-type)
                (scan)
                (union-intro-rule 'UNION-INTRO level current-type)
            )
         fi)         
    )
)

(defun parse-function-intro-rule ()
    (Plet (level (check-for-univ-level$))
        (Plet (new-ids (get-n-new-ids$ 1))
            (function-intro-rule 'FUNCTION-INTRO level (set-new-id$ new-ids))
        )
    )
)                                      

(defun parse-quotient-intro-rule ()      
    (Plet (level (check-for-univ-level$))
        (quotient-intro-rule 'QUOTIENT-INTRO level)
    )
)

(defun parse-set-intro-rule ()
  (let ((level nil)
	(term nil)
	(new-id nil))
    (when (or (not (null (bound-id-of-set-term ref-concl)))
	      (eql token-type TAt))
	  (setf level (check-for-univ-level$))
	  (setf term (check-for-term$ '|need a term after '.. at U(..) |))
	  (setf new-id (car (check-for-new-ids))))
    (set-intro-rule 'SET-INTRO level term new-id)))

(defun parse-eq-intro-rule ()
    (parse-eq-intro-rule$)
)

(defun parse-less-intro-rule ()
    (less-intro-rule 'LESS-INTRO)
)

(defun parse-recursive-intro-rule ()
    (Plet (level (check-for-univ-level$))
	 (recursive-intro-rule 'RECURSIVE-INTRO level)
    )
)

(defun parse-simple-rec-intro-rule ()
    (Plet (level (check-for-univ-level$))
	 (simple-rec-intro-rule 'SIMPLE-REC-INTRO level)))


(defun parse-void-elim-rule (assum-num)
    (void-elim-rule 'VOID-ELIM assum-num)
)

(defun parse-int-elim-rule (assum-num)
    (Plet (id-list (check-for-new-ids))
        (int-elim-rule 'INT-ELIM assum-num id-list)
    )
)

(defun parse-list-elim-rule (assum-num)
    (Plet (id-list (check-for-new-ids))
        (list-elim-rule 'LIST-ELIM assum-num id-list)
    )
)

(defun parse-union-elim-rule (assum-num)
    (Plet (id-list (check-for-new-ids))
        (union-elim-rule 'UNION-ELIM assum-num id-list)
    )
)

(defun parse-product-elim-rule (assum-num)
    (Plet (id-list (check-for-new-ids))
        (product-elim-rule 'PRODUCT-ELIM assum-num id-list)
    )
)

(defun parse-function-elim-rule (assum-num)
    (Plet (term (check-for-on-term)
         id-list (check-for-new-ids)
         )
        (function-elim-rule 'FUNCTION-ELIM assum-num term id-list)
    )
)

(defun parse-parfunction-elim-rule (assum-num)
    (Plet (term (check-for-on-term))
	 (Plet (id-list (check-for-new-ids))
	      (parfunction-elim-rule 'PARFUNCTION-ELIM assum-num term id-list)
	 )
    )
)

(defun parse-quotient-elim-rule (assum-num)
    (Plet (level (check-for-univ-level$))
          (Plet (id-list (check-for-new-ids))
               (quotient-elim-rule 'QUOTIENT-ELIM assum-num level id-list)
	  )
    )
)

(defun parse-set-elim-rule (assum-num)
    (Plet (level  (check-for-univ-level$))
          (Plet (id-list (check-for-new-ids))
               (set-elim-rule 'SET-ELIM assum-num level id-list)
	  )
    )
)


(defun parse-simple-rec-elim-rule (assum-num)
    (let* ((level (check-for-univ-level$))
	   (new-ids  (check-for-new-ids)))
      (simple-rec-elim-rule
	'SIMPLE-REC-ELIM
	assum-num
	level
	new-ids)))

(defun parse-simple-rec-unroll-elim-rule ()
    (let* ((assum-num
	     (Pif (eql token-type TNbr)
		 --> (Pif (or (< token-val 1)
			     (> token-val (length ref-assums)))
			 --> (ref-error
			       '|assum. num after 'elim' is out of range.|) ||
			 t
			 --> token-val fi)  ||

		 (eql token-type TId)
		 --> (assum-id-to-assum-num token-val ref-assums) ||
		 t
		 -->
		 (ref-error '|expecting an assum. number or id after 'elim'|) fi))
	   (new-id (progn (scan) (set-new-id$ (get-n-new-ids$ 1)))))
      (Pif (member assum-num ref-hidden)
	  --> (ref-error '|That assumption is hidden now|) fi)
      (Pif (not (eql 'SIMPLE-REC
		   (kind-of-term 
		     (type-of-declaration (nthelem assum-num ref-assums)))))
	  --> (ref-error '|assumption must be a simple rec term|) fi)
      (simple-rec-unroll-elim-rule
	'SIMPLE-REC-UNROLL-ELIM
	assum-num
	new-id)))


(defun parse-recursive-elim-rule (assum-num)
    (Plet (over-pair-list (check-for-over-part-list$))
	  (Plet (using-term-list (check-for-using-term-list$))
	       (Plet (new-ids  (check-for-new-ids))
	            (Plet (level (check-for-univ-level$))
			 (Pif (null using-term-list) -->
			     (recursive-unroll-elim-rule
			       'RECURSIVE-UNROLL-ELIM assum-num level new-ids
			     )
			  || t -->
			     (recursive-elim-rule
			       'RECURSIVE-ELIM
			       assum-num level
			       over-pair-list
			       using-term-list
			       new-ids
			     )
			  fi)
		    )
	      )
	  )
    )
)

(defun parse-hyp-rule ()
    (Plet (current-type token-type
          current-val  token-val
         )
        (scan)
        (Pif (eql current-type TNbr) --> 
            (hyp-rule 'HYP current-val)
            
         || (eql current-type TId) -->
            (hyp-rule 'HYP (assum-id-to-assum-num current-val ref-assums))
           
         || (eql current-type TEndInput) -->                           
            (ref-help '|need an assum num or id after 'hyp' |)
            
         || t -->
            (ref-error '|expecting an assum num or id after 'hyp' |)
         fi)
    )
)

(defun parse-sequence-rule ()
  (let ((term-list (get-term-list '|expecting term|))
	(new-ids (check-for-new-ids)))

    (cond ((not (null new-ids))
	   (if (not (= (length term-list) (length new-ids)))
	       (ref-error '|there must be a new id for each term|)
	       (sequence-rule 'SEQUENCE term-list new-ids)))

	  ((not (= token-type TEndInput))
	   (ref-error '|expecting new id list after terms|))

	  (t (sequence-rule 'SEQUENCE term-list nil)))))


(defun get-term-list (error-message)
    (Ploop
        (local terms (list (check-for-term$ error-message)))
        (while (eql token-type TComma))
        (do
            (scan)
            (<- terms (cons (check-for-term$ error-message) terms))
        )
        (result (nreverse terms))
    )
)

(defun parse-lemma-rule ()
  (let ((lemma (check-type-and-return-value TId))
	(new-ids (check-for-new-ids)))
    
    (cond  ((not (null new-ids)) 
	    (if (not (onep (length new-ids)))
		(ref-error '|only want one new-id |)
		(lemma-rule 'LEMMA lemma (car new-ids) nil nil)))

	   ((eql token-type TEndInput)
	    (lemma-rule 'LEMMA lemma nil nil nil))

	   (t (ref-error '|expecting 'new' or nothing |)))))

(defun parse-def-rule ()
  (let ((thm (check-type-and-return-value TId))
	(new-ids (check-for-new-ids)))

    (cond ((not (null new-ids))
	   (if (not (onep (length new-ids)))
	       (ref-error '|only want one new-id |)
	       (def-rule 'DEF thm (car new-ids))))

	  ((eql token-type TEndInput)
	   (def-rule 'DEF thm nil))

	  (t (ref-error '|expecting 'new' or nothing |)))))


(defun parse-explicit-intro-rule ()
    (Pif (eql token-type TEndInput) -->                  
        (ref-help '|need 'intro' after 'explicit' |)
     || (not (eql token-val '|intro|)) -->           
        (ref-error '|expecting 'intro' following 'explicit' |)
     || t -->
        (scan)
        (Plet (term (check-for-term$ '|need a term after 'explicit intro' |))
             (explicit-intro-rule 'EXPLICIT-INTRO term)
        )
     fi)
)

(defun parse-cumulativity-rule ()
    (Plet (level (check-for-univ-level$))
        (cumulativity-rule 'CUMULATIVITY level)
    )
)

(defun parse-equality-rule ()
    (equality-rule 'EQUALITY)
)

;(defun parse-substitute-rule ()
;    (Plet (level (check-for-univ-level$)
;          equality-term (check-for-term$ '|need an equality term after 'subst'. |)
;         )
;        (Pif (not (eql (kind-of-term equality-term) 'EQUAL)) -->
;            (ref-error '|term after 'subst' must be an equality term. |)
;         fi)                                                            
;        (check-token-type TOver)
;        (Plet (bound-id-term (get-bound-id-term$))
;            (Pif (not (= (length (terms-of-equal-term equality-term))
;                        (length (bound-ids-of-bound-id-term bound-id-term))
;                     )
;                ) -->
;                (ref-error (concat '| number of terms to be substituted doesn't |
;                                   '|match number of bound ids given |
;                           )
;                )
;             fi)
;            (check-token-type TNew)
;            (Plet (id (check-type-and-return-value TId))
;                (substitute-rule 'SUBSTITUTE level equality-term bound-id-term id)
;            )
;        )
;    )
;)


(defun parse-substitute-rule ()
    (Plet (equality-term (check-for-term$ '|need an equality term after 'subst'. |)
	  level (check-for-univ-level$))
       (Pif (not (eql (kind-of-term equality-term) 'EQUAL))
	   -->
	   (ref-error '|term after 'subst' must be an equality term. |) fi)
       (check-token-type TOver)
       (Plet (bound-id-term (get-bound-id-term$))
	  (Pif (not (and (= (length (terms-of-equal-term equality-term)) 2)
                        (= (length (bound-ids-of-bound-id-term bound-id-term)) 1)))
	      -->
	      (ref-error (concat '| equality term must have two equands and|
				 '| "over" term must have one bound id. |)) fi)
	  (substitute-rule 'SUBSTITUTE level equality-term bound-id-term))))


(defun parse-arith-rule ()
    (arith-rule 'ARITH (check-for-univ-level$))
)

(defun parse-extensionality-rule ()
    (let* ((level (check-for-univ-level$))
	   (using-terms (check-for-using-term-list$))
	   (new-id (car (check-for-new-ids))))
      (extensionality-rule 'EXTENSIONALITY level using-terms new-id))) 

;(defun parse-extensionality-rule ()
;    (extensionality-rule
;        'EXTENSIONALITY
;	;-- this depends on (car nil) --> nil
;	    (car (check-for-new-ids))
;    )
;)

(defun parse-because-rule ()
    (because-rule 'BECAUSE)
)

(defun parse-experimental-rule ()
    (experimental-rule
      'EXPERIMENTAL
      (nthcdr 13 ref-rule-body)  ;-- skip over "experimental " (hack)
      nil
    )
)

(defun parse-thinning-rule ()
    (thinning-rule 'THINNING (get-assum-num-list$)))

(defun parse-monot-rule ()
    (let* ((hyp1 (get-assumption))
	   (op   (get-monot-operator))
	   (hyp2 (get-assumption)))
      (monot-rule 'MONOT op hyp1 hyp2)))


(defun parse-division-rule ()
    (division-rule 'DIVISION))


(defun get-assumption ()
    (Pif (= token-type TNbr) -->
	(Pif (and (>= token-val 0) (<= token-val (length ref-assums))) -->
	    (prog1 token-val (scan))
	 || t -->
	    (ref-help (concat '|non existent hypothesis | token-val))
	 fi)
     || (= token-type TId) -->
        (prog1
	  (assum-id-to-assum-num token-val ref-assums)
	  (scan))
     || t -->
        (ref-help '|expecting assumption number or id|)
     fi)
)

(defun get-monot-operator ()
    (Pif (member token-type #.`'(,TPlus ,TMinus ,TStar ,TSlash)) -->
	(prog1
	  (cdr (assoc
		 token-type
		 #.`'((,TPlus . PLUS) (,TMinus . MINUS)
		     (,TStar . MULT) (,TSlash . DIV))))
	  (scan))
     || t -->
        (ref-help '|expecting one of +, -, *, or / |)
     fi)
)

(defun check-token-type (type-needed)
    (Pif (eql token-type TEndInput) -->
        (ref-help (concat '|expecting '|
                          (delim-descr-for type-needed)
                          '|' but not found|
                  )
        )
     || (not (eql token-type type-needed)) -->
        (ref-error (concat '|expecting '| 
                           (delim-descr-for type-needed)
                           '|' but not found|
                   )
        )
     fi)
    (scan)
)


(defun check-type-and-return-value (type-needed)
    (prog1
        token-val
        (check-token-type type-needed)
    )
)

(defun check-for-term$ (message)
    (Pif (eql token-type TEndInput) -->
        (ref-help message)
     || t -->
        (Plet (term (catch 'process-err (parse-from-current-Ttree)))
            (Pif (eql (car term) 'ERR) -->
                (ref-error message)
             || t -->
                term
             fi)
        )
     fi)
)

(defun check-for-univ-level$ ()
    (Pif (not (eql token-type TAt)) -->
        1
     || t -->
        (scan)
        (check-type-and-return-value TUniv)
     fi)
)

(defun get-assum-num-list$ ()
    (Ploop
        (local nums (list (check-type-and-return-value TNbr)))
        (while (eql token-type TComma))
        (do
            (scan)
            (<- nums (cons (check-type-and-return-value TNbr) nums))
        )
        (result (nreverse nums))
    )
)

(defun get-id-list$ ()
    (Ploop
        (local ids (list (check-type-and-return-value TId)))
        (while (eql token-type TComma))
        (do
            (scan)
            (<- ids (cons (check-type-and-return-value TId) ids))
        )
        (result (nreverse ids))
    )
)                                                         


(defun check-types-and-return-value (types-needed)
  (when (or (eql token-type TEndInput)
	    (not (member token-type types-needed :test #'eql)))
     (ref-help (concat '|expecting one of '| 
		       (mapcar #'delim-descr-for types-needed)
		       '|' but not found|)))

  (prog1 token-val (scan)))


(defun get-id-nil-list$ ()
  (let ((id (check-types-and-return-value (list TId TNil))))
    (if (eql TComma token-type)
	(progn (scan)
	       (cons id	(get-id-nil-list$)))
	(cons id nil))))


(defun get-new-id-list$ ()
    (Ploop
        (local ids (list (check-type-and-return-value TId)))
        (while (eq token-type TComma))
        (do
            (scan)
            (<- ids (cons (check-type-and-return-value TId) ids))
        )
        (result (nreverse ids))
    )
)                                                         

(defun get-bound-id-term$ ()
    (Plet (ids (get-id-list$))
        (check-token-type TPeriod)
        (Plet (term (check-for-term$ '|expecting a term after '.' |))
            (bound-id-term 'BOUND-ID-TERM nil ids term)
        )
    )
)

(defun assum-id-to-assum-num (id assums)
    (assum-id-to-assum-num$ id assums 1)
)

(defun assum-id-to-assum-num$ (id assums assum-num)
    (Pif (null assums) -->
        (ref-error '|expecting an assum number or id |)

     || (eql id (id-of-declaration (car assums))) -->
        assum-num

     || t -->
        (assum-id-to-assum-num$ id (cdr assums) (1+ assum-num))

     fi)
)

(defun check-for-new-ids ()
    (Pif (= token-type TNew) -->
        (scan)
        (get-id-nil-list$)
     || t -->
        nil
     fi)
)

(defun check-for-on-term ()
    (Pif (eql token-val '|on|) -->
        (scan)
        (check-for-term$ '|need a term after 'on'|)
     || t -->
        nil
     fi)
)
