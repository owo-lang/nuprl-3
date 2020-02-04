;;; -*- Package: Nuprl; Syntax: Common-lisp; Base: 10.; Lowercase: Yes -*-


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


;--    EXTRACT.L
;-- 
;-- The nuprl extractor.  In general the process is a straightforward 
;-- induction on the structure of the rules.  A complicating factor is that
;-- assumptions are not necessarily named.  The extraction process requires
;-- names for all assumptions, so that if an elim is done on an assumption
;-- the name for that assumption can be used in building the resulting term.
;-- To handle this, the extractor remembers names to use for all the unnamed
;-- assumptions in the assumption list.  The structure used to implement this
;-- association is an assumption map.  It maps assumption numbers to the
;-- term that should be used when a reference is made to that assumption.
;-- There are two functions which manipulate assumption maps:
;-- 
;--    update-assump-map (term, assump number, assump map) : assump-map
;--       This function updates the given assump-map to return the given
;--       term for the given assump number.
;-- 
;--    apply-assump-map (assump map, assump number) : term
;--       Returns the term to use for the given assump number.
;-- 
;-- The function apply-assump-map is never directly called.  Instead
;-- the function get-assumption-term(assump map, assump number, assumptions)
;-- is used.  This checks to see if the referenced assumption has a name,
;-- and returns a var term containing it if it does.  Otherwise, the
;-- assumption is looked up in the assump map, and the corresponding term
;-- is used.
;--
;-- The other complicating factor is caused by refinement tactics.  Since
;-- assumption maps are used, the extraction of a term from a child
;-- of a refinement tactic cannot be done until the assumption map for that
;-- child is defined.  This occurs when the extractor reaches the corresponding
;-- unproved leaf in extracting from the proof top of the refinement tactic.
;-- We handle this by keeping a stack of proofs for incomplete leaves.  
;-- When a refinement tactic is encountered, we push the list of children on
;-- stack and start extracting from the proof top associated with the tactic.
;-- When an incomplete leaf is encountered, we find the corresponding proof
;-- in the top level of the stack, and extract from it, popping one level off 
;-- stack.

(fluid allow-incomplete)			; true if incomplete leaves are to
						; be allowed in this extraction

(fluid *proofs-for-incomplete-leaves-stack*)	; the stack of proofs for incomplete leaves

(global next-new-var-number)			; used to obtain unique ids


(defun extract-init ()
    (for
        (i in '((INT-INTRO-NUMBER          ext-int-intro-number)
                (INT-INTRO-OP              ext-int-intro-op)
                (ATOM-INTRO                ext-atom-intro)
                (LIST-INTRO-NIL            ext-list-intro-nil)
                (LIST-INTRO-CONS           ext-list-intro-cons)
                (UNION-INTRO               ext-union-intro)
                (PRODUCT-INTRO             ext-product-intro)
                (FUNCTION-INTRO            ext-function-intro)
                (QUOTIENT-INTRO            ext-quotient-intro)
                (SET-INTRO                 ext-set-intro)
		(RECURSIVE-INTRO           ext-recursive-intro)
		(SIMPLE-REC-INTRO          ext-simple-rec-intro)
                (UNIVERSE-INTRO-VOID       ext-univ-intro-void)
                (UNIVERSE-INTRO-INT        ext-univ-intro-int)
                (UNIVERSE-INTRO-ATOM       ext-univ-intro-atom)
                (UNIVERSE-INTRO-LIST       ext-univ-intro-list)
                (UNIVERSE-INTRO-UNION      ext-univ-intro-union)
                (UNIVERSE-INTRO-PRODUCT    ext-univ-intro-product)
                (UNIVERSE-INTRO-FUNCTION   ext-univ-intro-function)
                (UNIVERSE-INTRO-QUOTIENT   ext-univ-intro-quotient)
                (UNIVERSE-INTRO-SET        ext-univ-intro-set)
                (UNIVERSE-INTRO-UNIVERSE   ext-univ-intro-univ)
                (UNIVERSE-INTRO-EQUAL      ext-univ-intro-equal)
                (UNIVERSE-INTRO-LESS       ext-univ-intro-less)
                (VOID-ELIM                 ext-void-elim)
                (INT-ELIM                  ext-int-elim)
                (LIST-ELIM                 ext-list-elim)
                (UNION-ELIM                ext-union-elim)
                (PRODUCT-ELIM              ext-product-elim)
                (FUNCTION-ELIM             ext-function-elim)
		(SET-ELIM                  ext-set-elim)
		(PARFUNCTION-ELIM          ext-parfunction-elim)
		(RECURSIVE-ELIM            ext-recursive-elim)
		(SIMPLE-REC-ELIM          ext-simple-rec-elim)
		(RECURSIVE-UNROLL-ELIM     ext-recursive-unroll-elim)
		(SIMPLE-REC-UNROLL-ELIM    ext-simple-rec-unroll-elim)
                (HYP                       ext-hyp)
                (LEMMA                     ext-lemma)
                (SEQUENCE                  ext-sequence)
                (DEF                       ext-def)
                (TACTIC                    ext-tactic)
                (EXPLICIT-INTRO            ext-explicit-intro)
                (SUBSTITUTE                ext-substitute)
                (ARITH                     ext-arith)
		(DIRECT-COMP               ext-direct-comp)
		(DIRECT-COMP-HYP           ext-direct-comp)
		(THINNING                  ext-thinning)
		(MONOT                     ext-monot)
               )
        )
        (do (setf (get (car i) 'extract-fcn) (cadr i)))
    )
    (for (i in '(EQUAL-INTRO-EQUAL    EQUAL-INTRO-LESS     EQUAL-INTRO-VAR
                 EQUAL-INTRO-VOID     EQUAL-INTRO-ANY      EQUAL-INTRO-INT
                 EQUAL-INTRO-UNIVERSE EQUAL-INTRO-ATOM     EQUAL-INTRO-TOKEN
                 EQUAL-INTRO-TOKEN    EQUAL-INTRO-LIST     EQUAL-INTRO-UNION
                 EQUAL-INTRO-PRODUCT  EQUAL-INTRO-FUNCTION EQUAL-INTRO-INL
                 EQUAL-INTRO-INR      EQUAL-INTRO-PAIR     EQUAL-INTRO-LAMBDA
                 EQUAL-INTRO-IND      EQUAL-INTRO-LIST-IND EQUAL-INTRO-DECIDE
                 EQUAL-INTRO-SPREAD   EQUAL-INTRO-APPLY    EQUAL-INTRO-ADD
                 EQUAL-INTRO-SUB      EQUAL-INTRO-MUL      EQUAL-INTRO-DIV
                 EQUAL-INTRO-MOD      EQUAL-INTRO-POS-NUMBER
                 EQUAL-INTRO-MINUS    EQUAL-INTRO-NIL      EQUAL-INTRO-CONS
                 EQUAL-INTRO-QUOTIENT EQUAL-INTRO-QUOTIENT-ELEM
                 EQUAL-INTRO-SET      EQUAL-INTRO-SET-ELEM EQUAL-INTRO-ATOMEQ
                 EQUAL-INTRO-INTEQ    EQUAL-INTRO-INTLESS
                 EQUAL-INTRO-AXIOM-EQUAL EQUAL-INTRO-AXIOM-LESS
		 EQUAL-INTRO-OBJECT EQUAL-INTRO-OBJECT-MEMBER
		 
		 EQUAL-INTRO-REC-IND-WITH-FIX
		 EQUAL-INTRO-REC-IND-WITHOUT-FIX
		 EQUAL-INTRO-SIMPLE-REC-IND
		 EQUAL-INTRO-PARFUNCTION
		 EQUAL-INTRO-FIX
		 EQUAL-INTRO-APPLY-PARTIAL
                 EQUAL-INTRO-DOM
		 EQUAL-INTRO-RECURSIVE
		 EQUAL-INTRO-SIMPLE-REC 
		 EQUAL-INTRO-REC-MEMBER
		 EQUAL-INTRO-SIMPLE-REC-MEMBER

                 QUOTIENT-ELIM
		 FIX-COMP             DOM-COMP             REC-IND-COMP
                 APPLY-COMP           DECIDE-COMP          IND-COMP-DOWN
                 IND-COMP-BASE        IND-COMP-UP          LIST-IND-COMP-BASE
                 LIST-IND-COMP-UP     SPREAD-COMP          
                                                           EXTENSIONALITY
                 CUMULATIVITY         EQUALITY             BECAUSE
                 DIVISION 
		 ATOMEQ-COMP-TRUE
		 ATOMEQ-COMP-FALSE
		 INTEQ-COMP-TRUE
		 INTEQ-COMP-FALSE
		 INTLESS-COMP-TRUE
		 INTLESS-COMP-FALSE
                )
         )
        (do (setf (get i 'extract-fcn) 'ext-equal-intro))
    )
    (<- next-new-var-number 0)
    nil
)

(defun term-of-theorem (thm-name)
    (Plet (obj (library-object thm-name))
        (Plet (obj-val (sel (object obj) value))
            (Pif (sel (theorem-object obj-val) extracted-term)-->
                (sel (theorem-object obj-val) extracted-term)
             || (eql (sel (object obj) status) 'COMPLETE) -->
                (<- (sel (theorem-object obj-val) extracted-term)
                    (extract (get-proof-of-theorem-object obj-val thm-name) nil)
                )
                (sel (theorem-object obj-val) extracted-term)
             || t --> nil
             fi)
        )
    )
)

(defun evaluable-term-of-theorem (thm-name)
    (Plet (obj (library-object thm-name))
        (Plet (obj-val (sel (object obj) value))
            (Pif (sel (theorem-object obj-val) extracted-term)-->
                (sel (theorem-object obj-val) extracted-term)
	     || (eql (sel (object obj) status) 'COMPLETE) -->
	        (<- (sel (theorem-object obj-val) extracted-term)
                    (extract (get-proof-of-theorem-object obj-val thm-name) nil)
                )
                (sel (theorem-object obj-val) extracted-term)
             || (eql (sel (object obj) status) 'PARTIAL) -->
                (extract (get-proof-of-theorem-object obj-val thm-name) t)
             || t --> nil
             fi)
        )
    )
)

(defun invalidate-extraction (obj)
    (<- (sel (theorem-object (sel (object obj) value))
             extracted-term
        )
        nil
    )
)


(defun extraction-completed? (extraction-result)
    (catch 'extraction-completed? (extraction-completed?$ extraction-result)))

(defun extraction-completed?$ (x)
    (Pif (eql (car x) 'INCOMPLETE)
	--> (throw 'extraction-completed? nil) fi)
    (map-on-subterms #'extraction-completed?$ x)
    t)




(defun extract (proof allow-incomplete)
    (<- next-new-var-number 0)
    (mark-names-of-proof proof)
    (unwind-protect
        (catch
	    'process-err
	    (Plet (*proofs-for-incomplete-leaves-stack* nil)
		(extract$ proof (mk-empty-assum-map))
	    )
	)
       (unmark-names-of-proof proof)
    )
)

(defun extract$ (pt assum-map)
    (Pif (null pt) -->
        (extract-err "Bad proof tree: " nil)
     || (null (rule-of-proof-tree pt)) -->
        (extract-incomplete pt assum-map)
     || (member (kind-of-term (conclusion-of-proof-tree pt))
		'(EQUAL LESS VOID)) -->
        (axiom-term 'AXIOM nil)
     || t -->
        (funcall
            (extract-fcn-of pt)
            pt
            (rule-of-proof-tree pt)
            assum-map
        )
     fi)
)

(defun extract-fcn-of (pt)
    (Plet (
             fcn (get
                     (kind-of-rule (rule-of-proof-tree pt))
                     'extract-fcn
                 )
         )
        (Pif fcn -->
            fcn
         || t -->
            (extract-err
                "Bad rule kind: "
                (kind-of-rule (rule-of-proof-tree pt))
            )
         fi)
    )
)

(defun extract-incomplete (pt assum-map)
    (Pif (member
            (kind-of-term (conclusion-of-proof-tree pt))
            '(EQUAL LESS)
        ) -->
        (axiom-term 'AXIOM nil)

     || (not (null *proofs-for-incomplete-leaves-stack*)) -->
        (Plet (new-pt (find-proof-for-incomplete-leaf pt))
	    (Pif (atom new-pt) -->
		;-- The proof wasn't found in the current level.
		(Pif allow-incomplete -->
		    (list 'INCOMPLETE)
		 || t -->
		    (extract-err
		      "Couldn't find proof for incomplete leaf"
		      nil
		    )
		 fi)
	     || t -->
		;-- Move down a level in the incomplete leaf stack and extract
		;-- from the proof.
		(Plet (*proofs-for-incomplete-leaves-stack*
			 (cdr *proofs-for-incomplete-leaves-stack*)
		     )
		    (extract$ new-pt assum-map)
		)
	     fi)
        )

     || allow-incomplete -->
        (list 'INCOMPLETE)

     || t -->
        (extract-err "Internal status inconsistency" nil)
     fi)
)

(defun find-proof-for-incomplete-leaf (pt)
    ;-- Finds the proof in the current level that extends the incomplete proof pt.
    ;-- If no proof is found, the atom 'NOT-FOUND is returned.
    (do ((candidates (car *proofs-for-incomplete-leaves-stack*) (cdr candidates)))
        ((null candidates) 'NOT-FOUND)
      (Pif (same-sequent? (car candidates) pt) -->
	  (return (car candidates))
       fi)
    )
)

(defun same-sequent? (pt1 pt2)
    (and
      (eql (assumptions-of-proof-tree pt1) (assumptions-of-proof-tree pt2))
      (eql (conclusion-of-proof-tree pt1) (conclusion-of-proof-tree pt2))
    )
)

(defun ext-int-intro-number (pt rule assum-map)
  (declare (ignore pt assum-map))
  (mk-int-term (selector-of-int-intro-rule rule)))

(defun ext-int-intro-op (pt rule assum-map)
    (binary-term
        (cdr (assoc
                 (selector-of-int-intro-rule rule)
                 #.`'( (,TPlus . ADD) (,TMinus . SUB) (,TStar . MUL)
                    (,TSlash . DIV) (,TMod . MOD)
                  )
             )
        )
        nil
        (extract$ (car (children-of-proof-tree pt)) assum-map)
        (extract$ (cadr (children-of-proof-tree pt)) assum-map)
    )
)


(defun ext-atom-intro (pt rule assum-map)
  (declare (ignore pt assum-map))
  (token-term-of-atom-intro-rule rule))

(defun ext-list-intro-nil (pt rule assum-map)
  (declare (ignore pt rule assum-map))
  (nil-term 'NIL nil))

(defun ext-list-intro-cons (pt rule assum-map)
  (declare (ignore rule))
  (cons-term
    'CONS nil
    (extract$ (car (children-of-proof-tree pt)) assum-map)
    (extract$ (cadr (children-of-proof-tree pt)) assum-map)))


(defun ext-union-intro (pt rule assum-map)
    (injection-term
        (cdr (assoc
                 (selector-of-union-intro-rule rule)
                 `( (,TLeft . INL) (,TRight . INR))
             )
        )
        nil
        (extract$ (car (children-of-proof-tree pt)) assum-map)
    )
)


(defun ext-product-intro (pt rule assum-map)
    (pair-term
        'PAIR nil
        (Pif (is-dependent-product (conclusion-of-proof-tree pt)) -->
	    (Plet (new-id (Pif (null (new-id-of-function-intro-rule rule)) -->
			     (bound-id-of-product-term (conclusion-of-proof-tree pt))
			  || t -->
			     (new-id-of-function-intro-rule rule)
			  fi)
		 )
		(leftterm-of-product-intro-rule rule)
	    )
         || t -->
            (extract$ (car (children-of-proof-tree pt)) assum-map)
         fi)
        (extract$ (cadr (children-of-proof-tree pt)) assum-map)
    )
)

(defun is-dependent-product (product)
    (bound-id-of-product-term product)
)
    

(defun ext-function-intro (pt rule assum-map)
    (Plet (conc (conclusion-of-proof-tree pt)
	  new-id (Pif (null (new-id-of-function-intro-rule rule)) -->
		     (bound-id-of-function-term (conclusion-of-proof-tree pt))
		  || t -->
		     (new-id-of-function-intro-rule rule)
		  fi)
	 )
        (Plet (id (check-id new-id))
            (lambda-term
                'LAMBDA nil
                id
                (extract$
                    (car (children-of-proof-tree pt))
                    (update-assum-map
                        (var-term 'VAR nil id)
                        (1+ (length (assumptions-of-proof-tree pt)))
                        assum-map
                    )
                )
            )
        )
    )
)

(defun ext-quotient-intro (pt rule assum-map)
  (declare (ignore rule))
  (extract$ (cadr (children-of-proof-tree pt)) assum-map))

(defun ext-set-intro (pt rule assum-map)
    (Pif (is-dependent-set (conclusion-of-proof-tree pt)) -->
        (leftterm-of-set-intro-rule rule)
     || t -->
        (extract$ (car (children-of-proof-tree pt)) assum-map)
     fi)
)

(defun is-dependent-set (set-term)
    (bound-id-of-set-term set-term)
)

(defun ext-univ-intro-void (pt rule assum-map)
  (declare (ignore pt rule assum-map))
    (void-term 'VOID nil)
)

(defun ext-univ-intro-int (pt rule assum-map)
  (declare (ignore pt rule assum-map))
  (int-term 'INT nil))

(defun ext-univ-intro-atom (pt rule assum-map)
  (declare (ignore pt rule assum-map))
  (atom-term 'ATOM nil))

(defun ext-univ-intro-list (pt rule assum-map)
  (declare (ignore rule))
  (list-term 'LIST nil (extract$ (car (children-of-proof-tree pt)) assum-map)))

(defun ext-univ-intro-union (pt rule assum-map)
  (declare (ignore rule))
  (union-term
    'UNION nil
    (extract$ (car (children-of-proof-tree pt)) assum-map)
    (extract$ (cadr (children-of-proof-tree pt)) assum-map)))


(defun ext-univ-intro-product (pt rule assum-map)
    (product-term
        'PRODUCT nil
        (id-of-univ-intro-rule-product rule)
        (Pif (id-of-univ-intro-rule-product rule) -->
	    (type-of-univ-intro-rule-product rule)
	 || t -->
	    (extract$ (car (children-of-proof-tree pt)) assum-map)
	 fi)
        (extract$ (cadr (children-of-proof-tree pt)) assum-map)
    )
)

(defun ext-univ-intro-function (pt rule assum-map)
    (function-term
        'FUNCTION nil
        (id-of-univ-intro-rule-function rule)
        (Pif (id-of-univ-intro-rule-function rule) -->
	    (type-of-univ-intro-rule-function rule)
	 || t -->
	    (extract$ (car (children-of-proof-tree pt)) assum-map)
	 fi)
        (extract$ (cadr (children-of-proof-tree pt)) assum-map)
    )
)

(defun ext-univ-intro-quotient (pt rule assum-map)
  (declare (ignore pt assum-map))
    (Plet (
             id1  (car (new-ids-of-univ-intro-rule-quotient rule))
             id2  (cadr (new-ids-of-univ-intro-rule-quotient rule))
         )
        (quotient-term 'QUOTIENT nil
                       (list id1 id2)
                       (term-of-univ-intro-rule-quotient rule)
                       (term2-of-univ-intro-rule-quotient rule)
        )
    )
)


(defun ext-univ-intro-set (pt rule assum-map)
    (set-term
        'SET nil
        (id-of-univ-intro-rule-set rule)
        (Pif (id-of-univ-intro-rule-set rule) -->
	    (type-of-univ-intro-rule-set rule)
	 || t -->
	    (extract$ (car (children-of-proof-tree pt)) assum-map)
	 fi)
        (extract$ (cadr (children-of-proof-tree pt)) assum-map)
    )
)

(defun ext-univ-intro-univ (pt rule assum-map)
  (declare (ignore pt assum-map))
  (universe-term 'UNIVERSE nil (level-of-univ-intro-rule-universe rule)))

(defun ext-univ-intro-equal (pt rule assum-map)
    (equal-term
        'EQUAL nil
        (type-of-univ-intro-rule-equal rule)
        (mapcar
	 #'(lambda (x)
	     (extract$ x assum-map)
	     )
	 (cdr (children-of-proof-tree pt))
	 )
    )
)

(defun ext-univ-intro-less (pt rule assum-map)
  (declare (ignore rule))
  (less-term
        'LESS nil
        (extract$ (car (children-of-proof-tree pt)) assum-map)
        (extract$ (cadr (children-of-proof-tree pt)) assum-map)))


(defun ext-equal-intro (pt rule assum-map)
  (declare (ignore pt rule assum-map))
  (axiom-term 'AXIOM nil))

(defun ext-recursive-intro (pt rule assum-map)
  (declare (ignore rule))
  (extract$ (car (children-of-proof-tree pt)) assum-map))


(defun ext-simple-rec-intro (pt rule assum-map)
  (declare (ignore rule))
  (extract$ (car (children-of-proof-tree pt)) assum-map))

(defun ext-void-elim (pt rule assum-map)
    (any-term
        'ANY nil
        (get-assumption-term
            assum-map
            (assum-num-of-void-elim-rule rule)
            (assumptions-of-proof-tree pt)
        )
    )
)

(defun ext-int-elim (pt rule assum-map)
    (Plet (
	     ids       (new-ids-of-int-elim-rule rule)
	     assum-len (length (assumptions-of-proof-tree pt))
             assum-num (assum-num-of-int-elim-rule rule)
	     assum-map-for-induction nil
	     ind-hyp   nil
	     ind-var   nil
	     ind-var-was-not-nil t
         )
	(multiple-value-setq (ind-hyp ind-var) (get-ids 2 ids))
	(Pif (null ind-var) -->
	    (<- ind-var
		(id-of-declaration (nthelem assum-num (assumptions-of-proof-tree pt)))
	    )
	    (<- ind-var-was-not-nil nil)
	 fi)
	(Pif (or ind-var-was-not-nil
		(occurs-free-in-assumption-list
		  (id-of-declaration (nthelem assum-num (assumptions-of-proof-tree pt)))
		  (nthcdr assum-num (assumptions-of-proof-tree pt)))
	    ) -->
	    (<- assum-map-for-induction
		(update-assum-map
		    (axiom-term 'AXIOM nil)
		    (+ 2 assum-len)
		    (cond ((null ind-hyp)
			   (<- ind-hyp (new-id))
			   (update-assum-map
			     (var-term 'VAR nil ind-hyp)
			     (+ 3 assum-len)
			     assum-map))
			  (t assum-map))
		)
	    )
	 || t -->
	    (<- assum-map-for-induction
		(update-assum-map
		    (axiom-term 'AXIOM nil)
		    (+ 1 assum-len)
		    (cond ((null ind-hyp)
			   (<- ind-hyp (new-id))
			   (update-assum-map
			     (var-term 'VAR nil ind-hyp)
			     (+ 2 assum-len)
			     assum-map))
			  (t assum-map))
		)
	    )
	 fi)

        (ind-term
            'IND nil
            (get-assumption-term
                assum-map
                assum-num
                (assumptions-of-proof-tree pt)
            )
            (bound-id-term
                'BOUND-ID-TERM nil
                (list ind-var ind-hyp)
                (extract$
                    (car (children-of-proof-tree pt))
                    assum-map-for-induction
                )
            )
            (extract$ (cadr (children-of-proof-tree pt)) assum-map)
            (bound-id-term
                'BOUND-ID-TERM nil
                (list ind-var ind-hyp)
                (extract$
                    (caddr (children-of-proof-tree pt))
                    assum-map-for-induction
                )
            )
        )
    )
)

(defun ext-list-elim (pt rule assum-map)
    (Plet (
	     ids  (new-ids-of-list-elim-rule rule)
             assum-num (assum-num-of-list-elim-rule rule)
             assum-len (length (assumptions-of-proof-tree pt))
	     hd-var   nil
	     tl-var   nil
	     ind-hyp  nil
         )
	(multiple-value-setq (ind-hyp hd-var tl-var) (get-ids 3 ids))
	(Pif (not tl-var) -->
	    (<- tl-var
		(id-of-declaration (nthelem assum-num (assumptions-of-proof-tree pt)))
	    )
	 fi)
	(cond ((not ind-hyp) (<- ind-hyp (new-id))))
        (list-ind-term
                'LIST-IND nil
                (get-assumption-term
                    assum-map
                    assum-num
                    (assumptions-of-proof-tree pt)
                )
                (extract$ (car (children-of-proof-tree pt)) assum-map)
                (bound-id-term
                    'BOUND-ID-TERM nil
                    (list hd-var tl-var ind-hyp)	
                    (extract$ (cadr (children-of-proof-tree pt))
			      (update-assum-map
				(var-term 'VAR nil ind-hyp)
				(length (assumptions-of-proof-tree
					  (cadr (children-of-proof-tree pt))))
				assum-map))

                )
        )
    )
)

(defun ext-union-elim (pt rule assum-map)
    (Plet (
             left-var  nil
             right-var nil
	     ids       (new-ids-of-union-elim-rule rule)
             assum-len (length (assumptions-of-proof-tree pt))
         )
	(multiple-value-setq (left-var right-var) (get-ids 2 ids))
	(<- left-var (check-id left-var))
	(<- right-var (check-id right-var))
        (decide-term
            'DECIDE nil
            (get-assumption-term
                assum-map
                (assum-num-of-union-elim-rule rule)
                (assumptions-of-proof-tree pt)
            )
            (bound-id-term
                'BOUND-ID-TERM nil
                (list left-var)
                (extract$
                    (car (children-of-proof-tree pt))
		    (update-assum-map
		        (var-term 'VAR nil left-var)
			(+ assum-len 1)
			(update-assum-map
			    (axiom-term 'AXIOM nil)
			    (+ assum-len 2)
			    assum-map
			)
		    )
                )
            )
            (bound-id-term
                'BOUND-ID-TERM nil
                (list right-var)
                (extract$
                    (cadr (children-of-proof-tree pt))
                    (update-assum-map
		        (var-term 'VAR nil right-var)
			(+ assum-len 1)
			(update-assum-map
			    (axiom-term 'AXIOM nil)
			    (+ assum-len 2)
			    assum-map
			)
		    )
                )
            )
        )
    )
)

(defun ext-product-elim (pt rule assum-map)
    (Plet (
	     ids (new-ids-of-product-elim-rule rule)
             1st-var nil
             2nd-var nil
	     assum-len (length (assumptions-of-proof-tree pt))
         )
        (multiple-value-setq (1st-var 2nd-var) (get-ids 2 ids))
	(<- 1st-var (check-id 1st-var))
	(<- 2nd-var (check-id 2nd-var))
        (spread-term
            'SPREAD nil
            (get-assumption-term
                assum-map
                (assum-num-of-product-elim-rule rule)
                (assumptions-of-proof-tree pt)
            )
            (bound-id-term
                'BOUND-ID-TERM nil
                (list 1st-var 2nd-var)
                (extract$
                    (car (children-of-proof-tree pt))
                    (update-assum-map
                        (var-term 'VAR nil 1st-var)
                        (+ assum-len 1)
                        (update-assum-map
                            (var-term 'VAR nil 2nd-var)
                            (+ assum-len 2)
                            (update-assum-map
                                (axiom-term 'AXIOM nil)
                                (+ assum-len 3)
                                assum-map
                            )
                        )
                    )
                )
            )
        )
    )
)

(defun ext-function-elim (pt rule assum-map)
    (Plet (
            ids   (new-ids-of-function-elim-rule rule)
	    id    nil
            assum-len (length (assumptions-of-proof-tree pt))
            term nil
         )
        (<- id (check-id (get-ids 1 ids)))
        (Pif (leftterm-of-function-elim-rule rule) -->
            (<- term (leftterm-of-function-elim-rule rule))
         || t -->                                                 
            (<- term (extract$ (car (children-of-proof-tree pt)) assum-map))
         fi)

        (apply-term 
            'APPLY nil
            (lambda-term 
                'LAMBDA nil
                id
                (extract$ (cadr (children-of-proof-tree pt))
                          (update-assum-map
                                (var-term 'VAR nil id)
                                (1+ assum-len)
                                (update-assum-map
                                    (axiom-term 'AXIOM nil)
                                    (+ assum-len 2)
                                    assum-map
                                )
                          )
                )
            )
            (apply-term 
                'APPLY nil 
                (get-assumption-term
                    assum-map
                    (assum-num-of-function-elim-rule rule)
                    (assumptions-of-proof-tree pt)
                )
                term
            )
        )
    )   
)


(defun ext-parfunction-elim (pt rule assum-map)
    (Plet (
            ids   (new-ids-of-parfunction-elim-rule rule)
	    id    nil
            assum-len (length (assumptions-of-proof-tree pt))
            term nil
         )
        (<- id (check-id (get-ids 1 ids)))
	(<- term (leftterm-of-parfunction-elim-rule rule))
        (apply-term 
            'APPLY nil
            (lambda-term 
                'LAMBDA nil
                id
                (extract$ (cadr (children-of-proof-tree pt))
                          (update-assum-map
                                (var-term 'VAR nil id)
                                (1+ assum-len)
                                (update-assum-map
                                    (axiom-term 'AXIOM nil)
                                    (+ assum-len 2)
                                    assum-map
                                )
                          )
                )
            )
            (apply-partial-term 
                'APPLY-PARTIAL nil 
                (get-assumption-term
                    assum-map
                    (assum-num-of-parfunction-elim-rule rule)
                    (assumptions-of-proof-tree pt)
                )
                term
            )
        )
    )   
)

(defun ext-recursive-unroll-elim (pt rule assum-map)
    (Plet (assum-len (length (assumptions-of-proof-tree pt))
	  ids       (new-ids-of-recursive-unroll-elim-rule rule)
	  elim-var  (apply-assumption-map
		      assum-map
		      (assum-num-of-recursive-unroll-elim-rule rule)
		    )
	  id        nil
	 )
	 (<- id (check-id (get-ids 1 ids)))
	 (substitute
	     (extract$ (car (children-of-proof-tree pt))
		   (update-assum-map
                        (var-term 'VAR nil id)
                        (1+ assum-len)
                        (update-assum-map
                            (axiom-term 'AXIOM nil)
                            (+ assum-len 2)
                            assum-map
                        )
                   )
	     )
	     (list (list (id-of-var-term elim-var) (var-term 'VAR nil id)))
	 )
    )
)



(defun ext-simple-rec-unroll-elim (pt rule assum-map)
    (let* ((elim-var (get-assumption-term
		       assum-map
		       (assum-num-of-simple-rec-unroll-elim-rule rule)
		       (assumptions-of-proof-tree pt)))
	   (new-id (check-id  (new-id-of-simple-rec-unroll-elim-rule rule)))
	   (n (length (assumptions-of-proof-tree pt)))
	   (child (car (children-of-proof-tree pt)))
	   (child-ext-term
	     (extract$
	       child
	       (extend-assum-map		
		 assum-map
		 (1+ n)
		 (cons (var-term 'VAR nil new-id)
		       (cond ((eql (1+ n)
				   (length (assumptions-of-proof-tree child)))
			      nil)
			     (t
			      (list (axiom-term 'AXIOM nil)))))))))
      (substitute child-ext-term `((,new-id ,elim-var)))))

(defun ext-recursive-elim (pt rule assum-map)
    (Plet  (assum-list (assumptions-of-proof-tree pt)
	   assum-num  (assum-num-of-recursive-elim-rule rule)
	   over-pairs (over-pair-list-of-recursive-elim-rule rule)
	   new-ids    (new-ids-of-recursive-elim-rule rule)
	   bound-ids  nil
	   bound-id-list nil
	   new-assum-map nil
	   assum      nil
	   selected   nil
	   rec-term   nil
	   size       nil
	   term-list  nil
	  )
	  (<- assum (nthelem assum-num assum-list))
	  (<- rec-term (type-of-declaration assum))
	  (<- bound-id-list (bound-id-list-term-of-recursive-term rec-term))
	  (<- bound-ids (bound-ids-of-bound-id-list-term bound-id-list))
	  (<- size (length bound-ids))
	  (<- selected
	      (position
		(id-of-recursive-term rec-term)
		(bound-ids-of-bound-id-list-term
		  (bound-id-list-term-of-recursive-term rec-term)
		)
	      )
	  )
	  (<- new-assum-map
	      (extend-assum-map
		assum-map
		(+ 1 (length assum-list))
		(append
		  (for (i in bound-ids)
		       (save
			 (lambda-term 'LAMBDA nil i
			   (recursive-term
			     'RECURSIVE nil bound-id-list
			     (fix-term-of-recursive-term rec-term) i i)
			 )
		       )
		  )
		  (for (i in over-pairs)
		       (save
			 (lambda-term 'LAMBDA nil (car i) (axiom-term 'AXIOM nil))
		       )
		  )
		  (for (i in new-ids)
		       (save
			 (lambda-term 'LAMBDA nil i
			   (lambda-term 'LAMBDA nil i (axiom-term 'AXIOM nil))
			 )
		       )
		  )
		  (for (i in new-ids) (save (var-term 'VAR nil i)))
		)
	      )
	  )
	  (<- term-list
	      (for (i in over-pairs)
		   (j in (subseq (children-of-proof-tree pt) 0 size)) 
		   (save
		     (extract$ j
		       (update-assum-map (var-term 'VAR nil (car i))
		            (+ 1 (length new-assum-map))
		            new-assum-map
		       )
		     )
		   )
	       )
	  )
	  (rec-ind-term 'REC-IND nil
	    (pair-term 'PAIR nil
	       (var-term 'VAR nil (id-of-declaration assum))
	       (term-of-recursive-term rec-term)
	    )
	    (bound-id-list-term 'BOUND-ID-LIST nil
	       new-ids
	       (for (i in term-list)
		    (j in over-pairs)
		    (save
		      (bound-id-term 'BOUND-ID-TERM nil (list (car j)) i)
		    )
	       )
	    )
	    (nth selected new-ids)
	  )
    )
)

(defun ext-simple-rec-elim (pt rule assum-map)
    (let* ((assums (assumptions-of-proof-tree pt))
	   (child (car (children-of-proof-tree pt)))
	   (child-assums (assumptions-of-proof-tree child))
	   (hyp-tags (mapcar #'id-of-declaration
			     (nthcdr (length assums)
				     child-assums)))
	   (denilled-hyp-tags (mapcar #'check-id hyp-tags))
	   (p (first denilled-hyp-tags))
	   (h (second denilled-hyp-tags))
	   (z (third denilled-hyp-tags))
	   (elim-var (get-assumption-term
		       assum-map
		       (assum-num-of-simple-rec-elim-rule rule)
		       assums))
	   (child-ext (extract$
			child
			(extend-assum-map
			  assum-map
			  (1+ (length assums))
			  (list
			    (var-term 'VAR nil p)
			    (var-term 'VAR nil h)
			    (var-term 'VAR nil z)))))
	   (child-ext-with-p-instantiated
	     (substitute child-ext
			 (list (list p (lambda-term 'LAMBDA nil 'x (void-term 'VOID nil)))))))
      (simple-rec-ind-term
	'SIMPLE-REC-IND
	nil
	elim-var
	(bound-id-term 'BOUND-ID-TERM nil (list h z) child-ext-with-p-instantiated))))

(defun ext-set-elim (pt rule assum-map)
 (declare (special *use-new-set-rules-p*))
 (cond
   (*use-new-set-rules-p*
    (ext-new-set-elim pt rule assum-map))
   (t
    (Plet (
	    ids       (new-ids-of-set-elim-rule rule)
	    new-id    nil
	    assum-num (assum-num-of-set-elim-rule rule)
	    assum-len (length (assumptions-of-proof-tree pt))
	    assum     nil
	 )
	(<- assum (nthelem assum-num (assumptions-of-proof-tree pt)))
        (<- new-id (get-ids 1 ids))
	(Pif (null new-id) -->
	    (Pif (occurs-free-in-term
		    (bound-id-of-set-term (type-of-declaration assum))
		    (righttype-of-set-term (type-of-declaration assum))
		) -->
		(<- new-id (bound-id-of-set-term (type-of-declaration assum)))
	     || t -->
	        (<- new-id (check-id new-id))
	     fi)
	 fi)
	(apply-term 'APPLY nil
	    (lambda-term 'LAMBDA nil new-id
                (extract$
		    (cadr (children-of-proof-tree pt))
		    (update-assum-map
			(var-term 'VAR nil new-id)
			(+ 1 assum-len)
			(update-assum-map
			    (axiom-term 'AXIOM nil)
			    (+ assum-len 2)
			    assum-map
			)
		    )
		)
	    )
	    (get-assumption-term
		assum-map
		assum-num
		(assumptions-of-proof-tree pt)
	    )
	)
    )))
)


(defun ext-new-set-elim (pt rule assum-map)
  (let* ((i (assum-num-of-set-elim-rule rule))
	 (n (length (assumptions-of-proof-tree pt)))
	 (is-declared? (not (null (id-of-declaration (nthelem i (assumptions-of-proof-tree pt))))))
	 (new-id (if is-declared?
			    nil
			    (check-id (id-of-declaration (nthelem (1+ n) (assumptions-of-proof-tree (first (children-of-proof-tree pt)))))))))
    (if
      is-declared?
      (extract$ (first (children-of-proof-tree pt))
		(update-assum-map
		  (axiom-term 'AXIOM nil)
		  (1+ i)
		  (shift-assum-map assum-map (1+ i) 1)))
      (apply-term
	'APPLY nil
	(lambda-term 'LAMBDA nil new-id
		     (extract$
		       (first (children-of-proof-tree pt))
		       (update-assum-map
			 (var-term 'VAR nil new-id)
			 (+ 1 n)
			 (update-assum-map
			   (axiom-term 'AXIOM nil)
			   (+ n 2)
			   assum-map))))
	(get-assumption-term
	  assum-map
	  i
	  (assumptions-of-proof-tree pt))))))

(defun ext-hyp (pt rule assum-map)
    (get-assumption-term
        assum-map
        (assum-num-of-hyp-rule rule)
        (assumptions-of-proof-tree pt)
    )
)


#|
(defun ext-sequence (pt rule assum-map)
  (let* ((ids (if (new-ids-of-sequence-rule rule)
		  (mapcar #'(lambda (x) (cond (x x) (t (new-id))))
			  (new-ids-of-sequence-rule rule))
		  (gen-ids (terms-of-sequence-rule rule))))
	 (unreduced-term
	   (ext-seq (children-of-proof-tree pt) ids assum-map)))
    (if (null ids)
	unreduced-term
	(initialize-and-compute (length ids) unreduced-term))))
|#

(defun ext-sequence (pt rule assum-map)
    (Plet (ids
             (Pif (new-ids-of-sequence-rule rule) -->
                 (mapcar #'(lambda (x) (cond (x x) (t (new-id))))
			 (new-ids-of-sequence-rule rule))
              || t -->
                 (gen-ids (terms-of-sequence-rule rule))
              fi)
         )
        (ext-seq (children-of-proof-tree pt) ids assum-map)
    )
)


(defun ext-seq (pt-list ids assum-map)
    (Plet (extracted-term (extract$ (car pt-list) assum-map))
        (Pif ids -->
            (apply-term 'APPLY nil
                (lambda-term 'LAMBDA nil
                    (car ids)
                    (ext-seq
                        (cdr pt-list)
                        (cdr ids)
                        (update-assum-map
                            (var-term 'VAR nil (car ids))
                            (1+ (length
                                    (assumptions-of-proof-tree (car pt-list))
                                )
                            )
                            assum-map
                        )
                    )
                )
                extracted-term
            )
         || t --> extracted-term
         fi)
    )
)


(defun ext-lemma (pt rule assum-map)
            (Pif (new-id-of-lemma-rule rule) -->
		(substitute
		  (extract$
		      (car (children-of-proof-tree pt))
		      (update-assum-map
                           (var-term 'VAR nil (new-id-of-lemma-rule rule))
			   (1+ (length (assumptions-of-proof-tree pt)))
			   assum-map
		      )
		  )
		  (list
		    (list (new-id-of-lemma-rule rule)
			  (term-of-theorem-term
                             'TERM-OF-THEOREM nil
                             (lemma-of-lemma-rule rule)
                           )
		    )
		  )
		)
             || t -->
	        (extract$
		      (car (children-of-proof-tree pt))
		      (update-assum-map
                           (term-of-theorem-term
                             'TERM-OF-THEOREM nil
                             (lemma-of-lemma-rule rule)
                           )
			   (1+ (length (assumptions-of-proof-tree pt)))
			   assum-map
		      )
		)
                
	     fi)
)

(defun ext-def (pt rule assum-map)
    (Plet (new-id (check-id (new-id-of-def-rule rule)))
        (extract$
            (car (children-of-proof-tree pt))
            (update-assum-map
                (var-term 'VAR nil new-id)
                (1+ (length (assumptions-of-proof-tree pt)))
                assum-map
            )
        )
    )
)

(defun ext-explicit-intro (pt rule assum-map)
  (declare (ignore pt assum-map))
  (term-of-explicit-intro-rule rule))

;(defun ext-substitute (pt rule assum-map)
;    (Plet (
;            id (new-id-of-substitute-rule rule)
;            bound-id-term (bound-id-term-of-substitute-rule rule)
;         )
;        (extract$ (car (children-of-proof-tree pt)) assum-map)
;        (extract$ (caddr (children-of-proof-tree pt))
;                  (new-subst-rule-assum-map$ 
;                        (bound-ids-of-bound-id-term bound-id-term)
;                        assum-map
;                  )
;        )
;        (apply-term
;            'APPLY nil
;            (lambda-term                                                       
;                'LAMBDA nil
;                id
;                (extract$ (cadr (children-of-proof-tree pt)) 
;                          (update-assum-map
;                            (var-term 'VAR nil id)
;                            (add1 (length (assumptions-of-proof-tree pt)))
;                            assum-map
;                          )
;                )
;            )
;            (car (terms-of-equal-term (equality-term-of-substitute-rule rule)))
;        )
;    )
;)


(defun ext-substitute (pt rule assum-map)
  (declare (ignore rule))
  (extract$ (cadr (children-of-proof-tree pt)) assum-map))

(defun ext-arith (pt rule assum-map)
  (declare (ignore rule assum-map))
    (Plet (                  
            concl (conclusion-of-proof-tree pt) 
            id    (new-id)
         )
        (Pif (eql (kind-of-term concl) 'UNION) -->
            (ext-arith-union$ concl id)

         || t -->
            (Plet (term-not-num-list (processable-arith-term$ concl 0)
                 )
                (Pif term-not-num-list -->
                    (make-n-lambda-lambda-term$
                        (car term-not-num-list) (cadr term-not-num-list) id
                    )

                 || t -->                  
                    ;-- assumptions were contadictory, so can extract anything
                        (axiom-term 'AXIOM nil)

                 fi)
            )
         fi)
    )
)

(defun ext-arith-union$ (term id)
    (Pif (eql (kind-of-term term) 'UNION) -->
        (make-arith-ext-term$ 
            (processable-arith-term$ (lefttype-of-union-term term) 0)
            (ext-arith-union$ (righttype-of-union-term term) id)
            id
        )

     || t -->
        (Pif (processable-arith-term$ term 0) -->
            (axiom-term 'AXIOM nil)
         || t -->
            nil
         fi)
     fi)
)

(defun make-arith-ext-term$ (term-not-num-list ext-term id)
    (Pif (null term-not-num-list) -->
        (Pif (null ext-term) -->
            (axiom-term 'AXIOM nil)
         || t -->
            (injection-term 'INR nil ext-term)
         fi)

     || t -->
        (Pif (null ext-term) -->
            (injection-term 
                'INL nil
                (make-n-lambda-lambda-term$ (car term-not-num-list)
                                            (cadr term-not-num-list)
                                            id
                )                                                  
            )
         || (eql (kind-of-term (car term-not-num-list)) 'EQUAL) -->
            (Pif (evenp (cadr term-not-num-list)) -->
                (decision-term 
                    'INTEQ nil
                    (car (terms-of-equal-term (car term-not-num-list)))
                    (cadr (terms-of-equal-term (car term-not-num-list)))
                    (injection-term 
                        'INL nil
                        (make-n-lambda-lambda-term$ 
                            (car term-not-num-list) (cadr term-not-num-list) id
                        )
                    )
                    (injection-term 'INR nil ext-term)
                )
             || t -->
                (make-diseq-arith-ext$
                    (car term-not-num-list)
                    (terms-of-equal-term (car term-not-num-list))
                    (cadr term-not-num-list)
                    ext-term
                    id
                )
             fi)
         || t -->       
            (Pif (evenp (cadr term-not-num-list)) -->
                (decision-term 
                    'INTLESS nil
		    (leftterm-of-less-term (car term-not-num-list))
		    (rightterm-of-less-term (car term-not-num-list))
                    (injection-term 
                        'INL nil
                        (make-n-lambda-lambda-term$ 
                            (car term-not-num-list) (cadr term-not-num-list) id
                        )
                    )
                    (injection-term 'INR nil ext-term)
                )
             || t -->
                (decision-term 
                    'INTLESS nil
                    (leftterm-of-less-term (car term-not-num-list))
                    (rightterm-of-less-term (car term-not-num-list))
                    (injection-term 'INR nil ext-term)
                    (injection-term 
                        'INL nil
                        (make-n-lambda-lambda-term$ 
                            (car term-not-num-list) (cadr term-not-num-list) id
                        )
                    )
                )
             fi)
         fi)
     fi)
)

(defun processable-arith-term$ (term curr-num-nots)
    (declare (special type-int$))
    (Pif (not-term$ term) -->
        (processable-arith-term$ (not-term-body$ term) (1+ curr-num-nots))

     || (eql (kind-of-term term) 'LESS) -->
        (list term curr-num-nots)

     || (and (eql (kind-of-term term) 'EQUAL)
             (equal-terms (type-of-equal-term term) type-int$)
             (or (and
                    (= (length (terms-of-equal-term term)) 2)
                    (evenp curr-num-nots)
                 )
                 (oddp curr-num-nots)
            )
        ) -->
        (list term curr-num-nots)

     || t -->
        nil

     fi)
)

(defun make-diseq-arith-ext$ (orig-term diseq-terms num-nots ext-term id)
    (Pif (= (length diseq-terms) 2) -->
        (decision-term 
            'INTEQ nil
            (car diseq-terms)
            (cadr diseq-terms)
            (injection-term 'INR nil ext-term)
            (injection-term 
                'INL nil
                (make-n-lambda-lambda-term$ orig-term num-nots id)
            )
        )
     || t -->
        (decision-term 
            'INTEQ nil
            (car diseq-terms)
            (cadr diseq-terms)
            (make-diseq-arith-ext$
                orig-term (cdr diseq-terms) num-nots ext-term id
            )
            (injection-term
                'INL nil
                (make-n-lambda-lambda-term$ orig-term num-nots id)
            )
        )
     fi)
)

(defun make-n-lambda-lambda-term$ (term n id)
    (Pif (zerop n) -->
        (axiom-term 'AXIOM nil)
     || t -->
        (lambda-term 
            'LAMBDA nil
            id
            (make-n-lambda-lambda-term$ term (1- n) id)
        )
     fi)
)

(defun ext-tactic (pt rule assum-map)
    ;-- Push the new level of proofs for incomplete leaves and extract
    ;-- from the proof top.
    (Plet (*proofs-for-incomplete-leaves-stack*
	     (cons (children-of-proof-tree pt) *proofs-for-incomplete-leaves-stack*)
	 )
	(extract$ (proof-top-of-tactic-rule rule) assum-map)
    )
)

(defun ext-direct-comp (pt rule assum-map)
  (declare (ignore rule))
  (extract$ (car (children-of-proof-tree pt)) assum-map))


(defun ext-thinning (pt rule assum-map)
    (extract$ (car (children-of-proof-tree pt))
	      (thin-assum-map pt rule assum-map)))

;;; a trivial term is an equality or less term or a conjunction or
;;; negation of trivial terms.
(defun proof-of-trivial-term (term)
  (let ((axiom (axiom-term 'AXIOM nil)))
    (case (kind-of-term term)
      (PRODUCT (pair-term 'PAIR nil (proof-of-trivial-term (lefttype-of-product-term term))
			  (righttype-of-product-term term)))
      (FUNCTION (lambda-term 'LAMBDA nil '|x| axiom))
      (LESS axiom)
      (EQUAL axiom)
      (otherwise (error "Cannot compute proof of term.")))))

(defun ext-monot (pt rule assum-map)
  (declare (ignore rule))
  (let* ((subgoal (car (children-of-proof-tree pt)))
	 (n (length (assumptions-of-proof-tree subgoal)))
	 (new-hyp (type-of-declaration
		    (car (last (assumptions-of-proof-tree subgoal))))))
    (extract$ subgoal
	      (update-assum-map (proof-of-trivial-term new-hyp) n assum-map))))

(defun get-assumption-term (assum-map assum-num assum-list)
    (let* ((assum (nthelem assum-num assum-list))
           (apply-a-map-result (apply-assumption-map assum-map assum-num))
           (id (id-of-declaration assum)))
        (Pif apply-a-map-result -->
	    apply-a-map-result
	 || id -->
	    (var-term 'VAR nil id)
	 || t -->
	    (extract-err "Inconsistency in assum-map" nil)
	 fi)
     )
)


;-- Functions defining an assum-map.  An assum-map is an association between
;-- assumption numbers and the term which should be used to display the
;-- assumption.  The implementation is an a-list, with the assumption
;-- numbers as keys.
;-- 

(defun mk-empty-assum-map () nil)

(defun update-assum-map (term assum-num assum-map)
    (cons (cons assum-num term) assum-map)
)

(defun extend-assum-map (assum-map starting-num term-list)
    (cond ((null term-list)
	   assum-map)
	  (t
	   (extend-assum-map
	     (update-assum-map (car term-list) starting-num assum-map)
	     (1+ starting-num)
	     (cdr term-list)))))

(defun shift-assum-map (assum-map from by)
  (mapcar #'(lambda (item) (if (<= from (car item))
				      (cons (+ by (car item)) (cdr item))
				      item))
	  assum-map))

(defun apply-assumption-map (assum-map assum-num)
    (Plet (result (assoc assum-num assum-map))
        (Pif result --> (cdr result)
         || t --> nil    ;-- (extract-err "Inconsistency in assumption map" nil)
         fi)
    )
)

(defun one-to-n (n)
  (Plet (result nil)
    (dotimes (i (1+ n)) (<- result (cons i result)))
    (cdr (nreverse result))))

(defun thin-assum-map (pt rule assum-map)
    (let* ((assums-to-delete
	     (propagate-thinning-in-assums$
	       (assum-num-list-of-thinning-rule rule)
	       ()
	       ()
	       1
	       (assumptions-of-proof-tree pt)))
	   (n (length (assumptions-of-proof-tree pt)))
	   (assums-to-not-delete
	     (for (i in (one-to-n n))
		  (filter (and (not (member i assums-to-delete))
			       i)))))
      (for (p in assum-map)
	   (filter
	     (let* ((i (position (car p) assums-to-not-delete)))
	       (and (not (null i)) (cons (1+ i) (cdr p))))))))

(defun propagate-thinning-in-assums$
    (list-from-rule thinned-vars thinned-assums next-assum-num remaining-assums)
    (Pif (null remaining-assums)
	--> (reverse thinned-assums)  ||
	t
	--> (let* ((id (id-of-declaration (car remaining-assums)))
		   (type (type-of-declaration (car remaining-assums))))
	      (Pif (or (member next-assum-num list-from-rule)			      
		      (intersection (free-vars type) thinned-vars))
		  --> (propagate-thinning-in-assums$
			list-from-rule
			(Pif (eql 'NIL id) --> thinned-vars ||
			    t --> (cons id thinned-vars) fi)
			(cons next-assum-num thinned-assums)
			(1+ next-assum-num)
			(cdr remaining-assums)) ||
		  t
		  --> (propagate-thinning-in-assums$
			list-from-rule
			thinned-vars
			thinned-assums
			(1+ next-assum-num)
			(cdr remaining-assums)) fi)) fi))


(defun mark-names-of-proof (proof)
    (map-on-names-of-proof
      #'(lambda (id) (setf (get id 'name-is-used) t))
      proof
    )
)

(defun unmark-names-of-proof (proof)
    (map-on-names-of-proof
      #'(lambda (id) (setf (get id 'name-is-used) nil))
      proof
    )
)

(defun map-on-names-of-proof (f pt)		
  (labels ((do-it (pt do-root?)
	     (when do-root?
	       (mapc #'(lambda (decl) (funcall f (id-of-declaration decl)))
		     (assumptions-of-proof-tree pt)))
	     (cond ((null (rule-of-proof-tree pt)))

		   ((eql 'TACTIC (kind-of-rule (rule-of-proof-tree pt)))
		    (do-it
		      (proof-top-of-tactic-rule (rule-of-proof-tree pt))
		      nil)
		    (mapc #'(lambda (p) (do-it p nil))
			  (children-of-proof-tree pt)))

		   (t
		    (mapc #'(lambda (p) (do-it p t))
			  (children-of-proof-tree pt))))))
    (do-it pt t))
  (values)) 

;(defun map-on-names-of-proof (f pt)
;    (for (decl in (assumptions-of-proof-tree pt))
;	 (do
;	   (Pif (id-of-declaration decl) -->
;	       (funcall f (id-of-declaration decl))
;	    fi)
;	 )
;    )
;    (for (child in (children-of-proof-tree pt))
;	 (do
;	   (map-on-names-of-proof f child)
;	 )
;    )
;)
		

(defun check-id (id)
    (Pif id -->
        id
     || t -->
        (new-id)
     fi)
)

(defun gen-ids (terms)
    (mapcar
      #'(lambda (term) (new-id))
      terms
    )
)


(defun new-id ()
    (Ploop
        (local  id (next-new-extract-id))
        (while (get id 'name-is-used))
        (do
            (<- id (next-new-extract-id))
        )
        (result id)
    )
)

(defun next-new-extract-id ()
    (prog1
        (concat '|v| next-new-var-number)
        (<- next-new-var-number (1+ *-*))
    )
)

(defun get-ids (n ids)
  (declare (ignore n))
  (values
    (nthelem 1 ids)
    (nthelem 2 ids)
    (nthelem 3 ids)))


(defun extract-err (msg1 msg2)
    (display-message '#.(istring "Internal PRL error in extraction: "))
    (display-message (istring msg1))
    (display-message (istring msg2))
    (throw 'process-err nil))
