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


(defun refine-apply-comp ()
    (Plet (apply-term nil
          result-terms nil
                    where      (where-of-comp-rule ref-rule)
         )
        (check-comp-concl-kind$)   
        (<- apply-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'APPLY apply-term)
        (<- result-terms (get-comp-result-terms$ where))
        (<- ref-children 
            (list
                (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (cons
                            (substitute 
                                (term-of-lambda-term
                                    (function-of-apply-term apply-term)
                                )
                                (list
                                    (list
                                        (bound-id-of-lambda-term
                                            (function-of-apply-term apply-term)
                                        )
                                        (arg-of-apply-term apply-term)
                                    )
                                )
                            )
                            result-terms
                        )
                    )
                )
            )
        )
    )
    nil
)


(defun refine-fix-comp ()
    (Plet (term-list       nil
	  ids             nil
	  fix-term        nil
	  apply-fix-term  nil
	  selected        0
          result-terms    nil
          where           (where-of-comp-rule ref-rule)
          reduced-term    nil
         )
        (check-comp-concl-kind$)
        (<- apply-fix-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'APPLY-PARTIAL apply-fix-term)
	(Pif (not
	      (eql (kind-of-term (function-of-apply-partial-term apply-fix-term)) 'FIX)
	    ) --> (ref-error '|expecting a fix term as the function term in application. |)
	 fi)
        (<- result-terms (get-comp-result-terms$ where))
	(<- fix-term (function-of-apply-partial-term apply-fix-term))
	(<- term-list (term-list-of-bound-id-list-term
			(bound-id-list-term-of-fix-term fix-term)
		      )
	)
	(<- ids (bound-ids-of-bound-id-list-term
		  (bound-id-list-term-of-fix-term fix-term)
		)
	)
	(<- selected (position (id-of-fix-term fix-term) ids))    
	(<- reduced-term
	    (substitute
	      (term-of-bound-id-term (nth selected term-list))
	      (append
		(list
		  (list (car (bound-ids-of-bound-id-term (nth selected term-list)))
			(arg-of-apply-partial-term apply-fix-term)
		  )
		)
		(for (z in ids)
		     (save
		       (list
			 z
			 (fix-term
			   'FIX
			   nil
			   (bound-id-list-term 'BOUND-ID-LIST nil ids term-list)
			   z
			 )
		       )
		     )
		)
	      )
	    )

	)
        (<- ref-children 
            (list (make-child ref-assums
                              (equal-term 'EQUAL
                                          nil
                                          (type-of-equal-term ref-concl)
                                          (cons reduced-term result-terms)
                              )
                  )
            )
        )
        nil
    )
)

(defun refine-rec-ind-comp ()
    (Plet (term-list       nil
	  rec-ind-term    nil
	  ids             nil
	  base-term       nil
	  selected        0
          result-terms    nil
          where           (where-of-comp-rule ref-rule)
          reduced-term    nil
         )
        (check-comp-concl-kind$)
        (<- rec-ind-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'REC-IND rec-ind-term)
        (<- result-terms (get-comp-result-terms$ where))
	(<- term-list (term-list-of-bound-id-list-term
			(bound-id-list-term-of-rec-ind-term rec-ind-term)
		      )
	)
	(<- ids (bound-ids-of-bound-id-list-term
			(bound-id-list-term-of-rec-ind-term rec-ind-term)
		      )
	)
	(<- base-term (term-of-rec-ind-term rec-ind-term))
	(<- selected
	    (position (id-of-rec-ind-term rec-ind-term) ids)
	)
	(<- reduced-term
	    (substitute
	      (term-of-bound-id-term (nth selected term-list))
	      (append
		(list
		  (list (car (bound-ids-of-bound-id-term (nth selected term-list)))
			(term-of-rec-ind-term rec-ind-term)
		  )
		)
		(for (x in ids)
		     (z in term-list)
		     (save
		       (list
			 x
			 (lambda-term
			   'LAMBDA
			   nil
			   (car (bound-ids-of-bound-id-term z))
			   (rec-ind-term
			     'REC-IND
			     nil
			     (var-term 'VAR nil (car (bound-ids-of-bound-id-term z)))
			     (bound-id-list-term-of-rec-ind-term rec-ind-term)
			     x
			   )
			 )
			 
		       )
		     )
		)
	      )
	    )

	)
        (<- ref-children 
            (list (make-child ref-assums
                              (equal-term 'EQUAL
                                          nil
                                          (type-of-equal-term ref-concl)
                                          (cons reduced-term result-terms)
                              )
                  )
            )
        )
        nil
    )
)

(defun refine-dom-comp ()
    (Plet (term-list       nil
	  fix-term        nil
	  ids             nil
	  dom-term        nil
	  selected-term   nil
	  selected        0
          result-terms    nil
          where           (where-of-dom-comp-rule ref-rule)
	  new-ids         (new-ids-of-dom-comp-rule ref-rule)
          reduced-term    nil
         )
        (check-comp-concl-kind$)
        (<- dom-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'DOM dom-term)
        (<- result-terms (get-comp-result-terms$ where))
	(<- fix-term (term-of-dom-term dom-term))
	(<- term-list (term-list-of-bound-id-list-term
			(bound-id-list-term-of-fix-term fix-term)
		      )
	)
	(<- ids (bound-ids-of-bound-id-list-term
			(bound-id-list-term-of-fix-term fix-term)
		      )
	)
	(Pif (not (eql (length new-ids) (length ids))) -->
	    (ref-error `|new id list not of correct length|)
	 fi)
	(<- selected (position (id-of-fix-term fix-term) ids))
	(<- selected-term (nth selected term-list))
	(<- reduced-term
	    (lambda-term
	      'LAMBDA
	      nil
	      (car (bound-ids-of-bound-id-term selected-term))
	      (recursive-term
		'RECURSIVE
		nil
		(bound-id-list-term
		  'BOUND-ID-LIST
		  nil
		  new-ids
		  (for (x in term-list)
		       (save
			 (domain-transform x (pairlis ids new-ids) nil )
		       )
		  )
		)
		fix-term
		(nth selected new-ids)
		(var-term 'VAR nil (car (bound-ids-of-bound-id-term selected-term)))
	      )
	    )
	)
        (<- ref-children 
            (list (make-child ref-assums
                              (equal-term 'EQUAL
                                          nil
                                          (type-of-equal-term ref-concl)
                                          (cons reduced-term result-terms)
                              )
                  )
            )
        )
        nil
    )
)



(defun refine-spread-comp ()
    (Plet (spread-term nil
          result-terms nil                     
          where       (where-of-comp-rule ref-rule)
         )
        (check-comp-concl-kind$)   
        (<- spread-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'SPREAD spread-term)
        (<- result-terms (get-comp-result-terms$ where))
        (<- ref-children
            (list
                (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (cons
                            (substitute 
                                (term-of-bound-id-term
                                    (term-of-spread-term spread-term)
                                )                                    
                                (list
                                    (list
                                        (car
                                            (bound-ids-of-bound-id-term
                                               (term-of-spread-term spread-term)
                                             )
                                        )
                                        (leftterm-of-pair-term
                                            (value-of-spread-term spread-term)     
                                        )
                                    )
                                    (list
                                        (cadr
                                            (bound-ids-of-bound-id-term
                                                (term-of-spread-term spread-term)
                                              )
                                        )
                                        (rightterm-of-pair-term
                                            (value-of-spread-term spread-term)     
                                        )
                                    )
                                )
                            )
                            result-terms
                        )
                    )
                )
            )
        )
    )
    nil
)


(defun refine-decide-comp ()
    (Plet (decide-term nil
          injection-term nil
          bound-term  nil
          result-terms nil                     
          where       (where-of-comp-rule ref-rule)
         )
        (check-comp-concl-kind$)   
        (<- decide-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'DECIDE decide-term) 
        (<- injection-term (value-of-decide-term decide-term))
        (Pif (eql (kind-of-term injection-term) 'INL) -->
            (<- bound-term (leftterm-of-decide-term decide-term))
         || t -->
            (<- bound-term (rightterm-of-decide-term decide-term))
         fi)
        (<- result-terms (get-comp-result-terms$ where))
        (<- ref-children
            (list
                (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (cons
                            (substitute 
                                (term-of-bound-id-term bound-term)
                                (list
                                    (list
                                        (car (bound-ids-of-bound-id-term
                                                                    bound-term
                                             )
                                        )
                                        (term-of-injection-term injection-term)
                                      )
                                )
                            )
                            result-terms
                        )
                    )
                )
            )
        )
    )
    nil
)

(defun refine-ind-comp-down ()
    (Plet (ind-term nil
          downterm nil
          result-terms nil                     
          where       (where-of-comp-rule ref-rule)
         )
        (check-comp-concl-kind$)   
        (<- ind-term (get-term-to-reduce$ where))
        (<- downterm (downterm-of-ind-term ind-term))
        (check-term-to-reduce$ 'IND ind-term)
        (<- result-terms (get-comp-result-terms$ where))
        (<- ref-children
            (list
                (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (cons
                            (substitute 
                                (term-of-bound-id-term downterm)
                                (list
                                    (list
                                         (car
                                             (bound-ids-of-bound-id-term
                                                 downterm
                                              )
                                         )     
                                         (value-of-ind-term ind-term)
                                    )
                                    (list                          
                                        (cadr
                                            (bound-ids-of-bound-id-term
                                                downterm
                                            )
                                        )
                                        (ind-term 
                                            'IND
                                            nil
                                            (binary-term 
                                                'ADD
                                                nil
                                                (value-of-ind-term ind-term)
                                                (pos-number-term
                                                    'POS-NUMBER nil 1
                                                )
                                            )
                                            (downterm-of-ind-term ind-term)
                                            (baseterm-of-ind-term ind-term)
                                            (upterm-of-ind-term ind-term)
                                        )
                                    )
                                )
                            )
                            result-terms
                        )
                    )
                )
		(make-child
		  ref-assums
		  (less-term
		    'LESS nil
		    (value-of-ind-term ind-term)
		    (pos-number-term 'POS-NUMBER nil 0)
		  )
		)
            )
        )
    )
    nil
)

(defun refine-ind-comp-base ()
    (Plet (ind-term nil
          result-terms nil                     
          where       (where-of-comp-rule ref-rule)
         )
        (check-comp-concl-kind$)   
        (<- ind-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'IND ind-term)
        (<- result-terms (get-comp-result-terms$ where))
        (<- ref-children
            (list
                (make-child              
                    ref-assums
                    (equal-term 
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (cons (baseterm-of-ind-term ind-term)
                              result-terms
                        )
                    )
                )
		(make-child
		  ref-assums
		  (equal-term
		    'EQUAL nil
		    (int-term 'INT nil)
		    (list
		      (value-of-ind-term ind-term)
		      (pos-number-term 'POS-NUMBER nil 0)
		    )
		  )
		)
            )
        )
    )
    nil
)

(defun refine-ind-comp-up ()
    (Plet (ind-term nil
          upterm nil
          result-terms nil                     
          where       (where-of-comp-rule ref-rule)
         )
        (check-comp-concl-kind$)   
        (<- ind-term (get-term-to-reduce$ where))
        (<- upterm (upterm-of-ind-term ind-term))
        (check-term-to-reduce$ 'IND ind-term)
        (<- result-terms (get-comp-result-terms$ where))
        (<- ref-children
            (list
                (make-child
                    ref-assums
                    (equal-term
                        'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (cons
                            (substitute 
                                (term-of-bound-id-term upterm)
                                (list
                                    (list
                                         (car (bound-ids-of-bound-id-term
                                                  upterm
                                              )
                                         )
					 (value-of-ind-term ind-term)
                                      )
                                      (list                          
                                          (cadr (bound-ids-of-bound-id-term
                                                    upterm
                                                )
                                          )
                                          (ind-term 
                                              'IND
                                              nil
                                              (binary-term 
                                                  'SUB
                                                  nil
                                                  (value-of-ind-term ind-term)
                                                  (pos-number-term
                                                      'POS-NUMBER nil 1
                                                  )
                                              )
                                              (downterm-of-ind-term ind-term)
                                              (baseterm-of-ind-term ind-term)
                                              (upterm-of-ind-term ind-term)
                                          )
                                      )
                                )
                            )
                            result-terms
                        )
                    )
                )
		(make-child
                    ref-assums
                    (less-term
                        'LESS
                        nil
                        (pos-number-term 'POS-NUMBER nil 0)
                        (value-of-ind-term ind-term)
                    )
                )
            )
        )
    )
    nil
)

(defun refine-list-ind-comp ()
    (Plet (list-ind-term nil
          result-terms nil                     
          where       (where-of-comp-rule ref-rule)
         )
        (check-comp-concl-kind$)   
        (<- list-ind-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'LIST-IND list-ind-term)
        (<- result-terms (get-comp-result-terms$ where))
	(Pif (not (is-canonical-list-term (value-of-list-ind-term list-ind-term))) -->
	    (ref-error '|the argument of list_ind must be a canonical list|)
	 fi)
        (<- ref-children
            (list
              (make-child
		ref-assums
		(Pif (eq
		      (kind-of-term (value-of-list-ind-term list-ind-term))
		      'NIL
		    ) -->
		    (equal-term
			'EQUAL nil
			(type-of-equal-term ref-concl)
			(cons (baseterm-of-list-ind-term list-ind-term)
			    result-terms
			)
		    )
		 || t -->
		    (equal-term
		      'EQUAL nil
		      (type-of-equal-term ref-concl)
		      (cons
			(symbolically-reduce-list-ind list-ind-term)
			result-terms
		      )
		    )
		 fi)
	      )
	    )
	)
	nil
     )
)

(defun symbolically-reduce-list-ind (li-term)
    (let* ((ids (bound-ids-of-bound-id-term (upterm-of-list-ind-term li-term)))
	   (hd  (car ids))
	   (tl   (cadr ids))
	   (ih  (caddr ids))
	   (cons-term (value-of-list-ind-term li-term))
	   (head (head-of-cons-term cons-term))
	   (tail (tail-of-cons-term cons-term))
	   (ind-val (list-ind-term
		      'LIST-IND nil
		      tail
		      (baseterm-of-list-ind-term li-term)
		      (upterm-of-list-ind-term li-term))))
      (substitute
	(term-of-bound-id-term (upterm-of-list-ind-term li-term))
	`((,hd ,head)
	  (,tl ,tail)
	  (,ih ,ind-val))
      )
    )
)

(defun is-canonical-list-term (term)
    (member (kind-of-term term) '(NIL CONS))
)
	
(defun refine-atomeq-comp ()
    (Plet (atomeq-term      nil
          result-terms      nil
          subgoal-equality nil
          where            (where-of-comp-rule ref-rule)
	  case             (eql 'ATOMEQ-COMP-TRUE (kind-of-comp-rule ref-rule))
          reduced-term     nil
         )
        (check-comp-concl-kind$)
        (<- atomeq-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'ATOMEQ atomeq-term)
        (<- result-terms (get-comp-result-terms$ where))
        (Pif case -->
            (<- reduced-term (if-term-of-decision-term atomeq-term)) 
         || t -->
            (<- reduced-term (else-term-of-decision-term atomeq-term))
         fi)
        (<- ref-children 
            (list
                (make-child
                    ref-assums
                    (equal-term 'EQUAL
                        nil
                        (type-of-equal-term ref-concl)
                        (cons reduced-term result-terms)
                    )
                )
		(make-child ref-assums (make-decision-requirement$ atomeq-term case))
            )
	      
        )
        nil
    )
)

(defun refine-inteq-comp ()
    (Plet (inteq-term      nil
          result-terms     nil
          where           (where-of-comp-rule ref-rule)
	  case             (eql 'INTEQ-COMP-TRUE (kind-of-comp-rule ref-rule))
          reduced-term    nil
         )
        (check-comp-concl-kind$)
        (<- inteq-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'INTEQ inteq-term)
        (<- result-terms (get-comp-result-terms$ where))
        (Pif case -->
            (<- reduced-term (if-term-of-decision-term inteq-term))
         || t -->
            (<- reduced-term (else-term-of-decision-term inteq-term))
         fi)
        (<- ref-children 
            (list (make-child ref-assums
                              (equal-term 'EQUAL
                                          nil
                                          (type-of-equal-term ref-concl)
                                          (cons reduced-term result-terms)
                              )
                  )
		  (make-child ref-assums (make-decision-requirement$ inteq-term case))
            )
        )
        nil
    )
)

(defun refine-intless-comp ()
    (Plet (intless-term     nil
          result-terms      nil
          where            (where-of-comp-rule ref-rule)
	  case             (eql 'INTLESS-COMP-TRUE (kind-of-comp-rule ref-rule))
          reduced-term     nil
         )
        (check-comp-concl-kind$)
        (<- intless-term (get-term-to-reduce$ where))
        (check-term-to-reduce$ 'INTLESS intless-term)
        (<- result-terms (get-comp-result-terms$ where))
        (Pif case -->
            (<- reduced-term (if-term-of-decision-term intless-term))
         || t --> 
            (<- reduced-term (else-term-of-decision-term intless-term))
         fi)
        (<- ref-children 
            (list (make-child ref-assums
                              (equal-term 'EQUAL
                                          nil
                                          (type-of-equal-term ref-concl)
                                          (cons reduced-term result-terms)
                              )
                  )
		  (make-child ref-assums (make-decision-requirement$ intless-term case))
            )
        )
        nil
    )
)




(defun check-comp-concl-kind$ ()
    (Pif (not (eql (kind-of-term ref-concl) 'EQUAL)) -->
        (ref-error '|conclusion not suitable for computation rule|)
     fi)
)
                                      
(defun get-term-to-reduce$ (where)
  (unless (<= 1 where (length (terms-of-equal-term ref-concl)))
    (ref-error '|"where" out of range|))
  (car (nthcdr (1- where) (terms-of-equal-term ref-concl))))

(defun get-comp-result-terms$ (where)                 
    (deln$ where (terms-of-equal-term ref-concl))
)
(defun deln$ (n lst)
    (Pif (onep n) -->
        (cdr lst)     
     || t -->
        (cons (car lst) (deln$ (1- n) (cdr lst)))
     fi)
)

(defun check-term-to-reduce$ (kind term-to-reduce)              
    (Pif (not (or (and (eql kind 'APPLY)
                      (eql (kind-of-term term-to-reduce) 'APPLY)
                      (eql (kind-of-term (function-of-apply-term term-to-reduce))
                          'LAMBDA
                      )
                 )
		 (and (eql kind 'APPLY-PARTIAL)
		      (eql (kind-of-term term-to-reduce) 'APPLY-PARTIAL)
		      (eql (kind-of-term (function-of-apply-partial-term term-to-reduce))
			  'FIX
		      )
		 )
                 (and (eql kind 'SPREAD)
                      (eql (kind-of-term term-to-reduce) 'SPREAD)
                      (eql (kind-of-term (value-of-spread-term term-to-reduce))
                          'PAIR
                      )
                 )
                 (and (eql kind 'DECIDE)
                      (eql (kind-of-term term-to-reduce) 'DECIDE)
                      (or 
                        (eql (kind-of-term (value-of-spread-term term-to-reduce))
                            'INL
                        )
                        (eql (kind-of-term (value-of-spread-term term-to-reduce))
                            'INR
                        )
                      )
                 )
		 (and (eql kind 'REC-IND)
		      (eql (kind-of-term term-to-reduce) 'REC-IND)
		 )
		 (and (eql kind 'DOM)
		      (eql (kind-of-term term-to-reduce) 'DOM)
		      (eql (kind-of-term (term-of-dom-term term-to-reduce)) 'FIX)
		 )
                 (and (eql kind 'IND)
                      (eql (kind-of-term term-to-reduce) 'IND)
                 )
                 (and (eql kind 'LIST-IND) 
                      (eql (kind-of-term term-to-reduce) 'LIST-IND)
                 )
                 (and (eql kind 'ATOMEQ) 
                      (eql (kind-of-term term-to-reduce) 'ATOMEQ)
;                      (is-token-term$
;                          (leftterm-of-decision-term term-to-reduce)
;                      )                                            
;                      (is-token-term$ 
;                          (rightterm-of-decision-term term-to-reduce)
;                      )
                 )
                 (and (eql kind 'INTEQ)
                      (eql (kind-of-term term-to-reduce) 'INTEQ)
;                      (is-integer-term$ 
;                          (leftterm-of-decision-term term-to-reduce)
;                      )
;                      (is-integer-term$
;                          (rightterm-of-decision-term term-to-reduce)
;                      )
                 )				
                 (and (eql kind 'INTLESS)
                      (eql (kind-of-term term-to-reduce) 'INTLESS)
;                      (is-integer-term$ 
;                          (leftterm-of-decision-term term-to-reduce)
;                      )
;                      (is-integer-term$
;                          (rightterm-of-decision-term term-to-reduce)
;                      )
                 )
             )
        ) -->
        (ref-error '|conclusion not appropriate for computation rule |)
     fi) 
     
)

(defun is-token-term$ (term)
    (eql (kind-of-term term) 'TOKEN)
)

(defun is-integer-term$ (term)
    (or (eql (kind-of-term term) 'POS-NUMBER)
        (and (eql (kind-of-term term) 'MINUS)
             (eql (kind-of-term (term-of-minus-term term)) 'POS-NUMBER)
        )
    )
)

(defun get-number-from$ (term)
    (Pif (eql (kind-of-term term) 'POS-NUMBER) -->
        (number-of-pos-number-term term)

     || t -->
        (- (number-of-pos-number-term (term-of-minus-term term)))
     fi)
)


(defun make-decision-requirement$ (term case)
    (let* ((k (kind-of-term term))
	   (a (leftterm-of-decision-term term))
	   (b (rightterm-of-decision-term term))
	   (base-term
	     (Pif (eql k `INTLESS)
		 --> (less-term 'LESS nil a b)  ||
		 (eql k 'INTEQ)
		 --> (equal-term 'EQUAL nil (int-term 'INT nil) (list a b)) ||
		 (eql k 'ATOMEQ)
		 --> (equal-term 'EQUAL nil (atom-term 'ATOM nil) (list a b)) fi)))
      (Pif case --> base-term  ||
	  t --> (function-term 'FUNCTION nil nil base-term (void-term 'VOID nil)) fi)))


;;;**********************************************************************
;;;**********************************************************************

;;;     DIRECT COMPUTATION RULES (and supporting functions)

;;;**********************************************************************
;;;**********************************************************************





(defun refine-direct-comp ()
    (Plet (using-term (using-term-of-direct-comp-rule ref-rule))
	 (Pif (not (equal-terms ref-concl (erase-tags using-term)))
	     --> (ref-error '|Using term doesn't match conclusion.|) ||	     
	     (has-legal-tagging using-term)
	     --> (<- ref-children
		     (list (make-child ref-assums
				       (do-indicated-computations
					 using-term)))) ||
	     t
	     --> (ref-error '|Using term has illegal tagging|) fi)
	 nil))

(defun refine-direct-comp-hyp ()
    (let* ((assum-num (assum-num-of-direct-comp-hyp-rule ref-rule))
	   (using-term (using-term-of-direct-comp-hyp-rule ref-rule))
	   (assum-to-be-replaced (nth (1- assum-num) ref-assums))
	   (preceeding-assums (subseq ref-assums 0 (1- assum-num)))
	   (following-assums (nthcdr assum-num ref-assums)))
      (Pif (not assum-to-be-replaced)
	  --> (ref-error '|hypothesis number out of range|) ||
	  (not (equal-terms
		 (type-of-declaration assum-to-be-replaced)
		 (erase-tags using-term)))
	  --> (ref-error '|Using term doesn't match hypothesis.|) ||
	  (not (has-legal-tagging using-term))
	  --> (ref-error '|Illegal tagging in using term.|) ||
	  t
	  --> (<- ref-children
		  (list (make-child
			  (append
			    preceeding-assums
			    (cons (declaration
				    nil
				    (id-of-declaration assum-to-be-replaced)
				    (do-indicated-computations using-term))
				  following-assums))
			  ref-concl))) fi)
      nil))



(defun erase-tags (term)
    (Pif (eql 'TAGGED (kind-of-term term))
	--> (erase-tags (term-of-tagged-term term)) ||
	t
	--> (map-on-subterms #'erase-tags term) fi))



(constant type-terms-with-subterms
	  '(LIST UNION EQUAL PRODUCT FUNCTION SET
		 QUOTIENT RECURSIVE SIMPLE-REC PARFUNCTION))

(constant questionable-terms
	  '(DOM FIX APPLY-PARTIAL PARFUNCTION))

(constant canonical-terms-with-subterms
	  '(LIST CONS LIST UNION INL INR
		 PAIR EQUAL LESS
		 FIX RECURSIVE SIMPLE-REC PRODUCT FUNCTION LAMBDA SET PARFUNCTION
		 QUOTIENT))

;;; Bag the questionable terms for now.
(constant non-canonical-terms
	  '(MINUS ADD SUB MUL DIV MOD IND LIST-IND
		  DECIDE SPREAD APPLY  ATOMEQ INTLESS INTEQ SIMPLE-REC-IND
		  REC-IND))


;;;    The function has-legal-tagging: term -> bool uses three "illegal-tags"
;;; functions which return a list of all the subterms which are
;;; encountered in an illegal position.  They are based on the following
;;; formulation of the definition of what positions within a term may
;;; be marked.  
;;;    Let T be a term (ignore tags) and define a relation < on subterm
;;; occurrences of T by: u<v <=> u occurs properly within v.  A t <_ T
;;; may be marked if there are u,v with t <_ u <_ v <_ T  (<_ is less
;;; than or equals) such that:
;;; 1.  v < r <_ T  => r is a canonical term (including types),  and
;;; 2.  u is free in v  (i.e., no free vars of u are bound in v), and
;;; 3.  t < r <_ u  => 
;;;        a) r is a noncanonical term with t occurring within the 
;;;           principal arg. of r  (-- treat any as noncanonical here, and
;;;           note that rec-ind has no principal arg), or
;;;        b) r is a spread, decide, less, int_eq, or atom_eq term, or
;;;        c) r is ind(a;m,x.b;c;n,y.d) such that x,y do not occur free
;;;           in c,d respectively, or r is list_ind(a;h,t,v.b) and v
;;;           does not occur free in b.
;;;    There are 3 "illegal-tags" functions, corresponding to the 3 clauses
;;; above, and more comment on them appears with their definitions.  For
;;; purposes of this further comment, let T denote the term on which
;;; has-a-legal-tagging is called.


;;; Tagging restrictions are no longer necessary --- See Howe in LICS89.

(defun has-legal-tagging (term)
  (declare (special *all-tags-legal?*))
  (or *all-tags-legal?* (null (illegal-tags-1 term))))

(defun tagged-term-err ()
    (display-message '#.(istring " Unexpected tagged term.  "))
    (throw 'process-err nil))

(defun remove-outer-tags (term)
    (cond ((eql 'TAGGED (kind-of-term term))
	   (remove-outer-tags (term-of-tagged-term term)))
	  (t
	   term)))

;;; illegal-tags-fn must be illegal-tags-2 or illegal-tags-2
(defun collect-illegal-tags (illegal-tags-fn ids subterms)
    (apply
      #'append
      (for (term in subterms)
	   (save (Pif (eql (kind-of-term term) 'BOUND-ID-TERM)
		     --> (funcall
			   illegal-tags-fn
			   (append (bound-ids-of-bound-id-term term) ids)
			   (term-of-bound-id-term term))  ||
		     (eql (kind-of-term term) 'BOUND-ID-LIST)
		     --> (Plet (type-ids (bound-ids-of-bound-id-list-term term))
			      (apply
				#'append
				(for (x in (term-list-of-bound-id-list-term term))
				     (save (funcall
					     illegal-tags-fn
					     (append type-ids
						     (bound-ids-of-bound-id-term x)
						     ids)
					     (term-of-bound-id-term x))))))  ||
		     t
		     --> (funcall illegal-tags-fn ids term) fi)))))

;; Assume clause 1 with v replaced by term.
(defun illegal-tags-1 (term)
  (declare (special *all-tags-legal?*))
  (if *all-tags-legal?*
      nil
      (Plet (k (kind-of-term term))
	 (Pif (member k questionable-terms)
	     --> (all-subterms-with-tags term)  ||
	     (or (member k canonical-terms-with-subterms)  
		 (eql k 'TAGGED))
	     --> (apply
		   #'append
		   (for (x in (subterms-of-term term))	
			(save (Pif (eql (kind-of-term x) 'BOUND-ID-LIST)
				  --> (apply
					#'append
					(for (y in (subterms-of-term x))
					     (save (illegal-tags-1
						     (term-of-bound-id-term y))))) ||
				  t
				  --> (illegal-tags-1 x) fi)))) ||
	     t
	     --> (illegal-tags-3 nil term) fi))))



;;; Assume: there is a v satisfying clause 1 with term occurring in v;
;;; ids contains the identifiers which have binding occurrences in v
;;; that have term within their scope; and term is in an illegal position
;;; within T unless it is free in v.

(defun illegal-tags-2 (ids term)
    (let* ((k (kind-of-term term))
	   (subterms (subterms-of-term term)))
      (Pif (null (prl-set-difference
		 (intersection ids (free-vars term))
		 '(nil)))
	  --> (illegal-tags-3 ids term)  ||
	  (eql k 'TAGGED)
	  --> (cons term (illegal-tags-2 ids
					 (term-of-tagged-term term)))  ||
	  (member k '(PRODUCT FUNCTION QUOTIENT SET PARFUNCTION))
	  --> (append
		(illegal-tags-2 ids (first subterms))
		(illegal-tags-2 (append (binding-ids-of-term term) ids)
			  (second subterms)))  ||
	  (eql k 'LAMBDA)
	  --> (illegal-tags-2 (cons (bound-id-of-lambda-term term) ids)
		      (car subterms))  ||
	  (eql k 'BOUND-ID-TERM)
	  --> (collect-illegal-tags #'illegal-tags-2
				    (append (bound-ids-of-bound-id-term term)
					    ids)
				    subterms) ||
	  t
	  --> (collect-illegal-tags #'illegal-tags-2 ids subterms) fi)))
		   


;;; Assume: there are u,v so that clauses 1,2, and 3 are satisfied when
;;; t is replaced by term, and ids has the property described in illegal-tags-2.

(defun illegal-tags-3 (ids term)
    (let* ((k (kind-of-term term))
	   (subterms (subterms-of-term term)))
      (Pif
	
	(or (eql k 'APPLY)
	    (and (eql k 'IND)
		 (or (induction-var-used (downterm-of-ind-term term))
		     (induction-var-used (upterm-of-ind-term term))))
	    (and (eql k 'LIST-IND)
		 (induction-var-used (upterm-of-list-ind-term term))))
	--> (append (illegal-tags-3 ids (car subterms))
		    (collect-illegal-tags #'illegal-tags-2 ids (cdr subterms))) ||
	
	(and (member k non-canonical-terms)
	     (not (or (eql k 'SIMPLE-REC-IND) (eql k 'REC-IND))))
	--> (collect-illegal-tags #'illegal-tags-3 ids subterms)  ||
	
	(eql k 'TAGGED)
	--> (collect-illegal-tags #'illegal-tags-3 ids subterms)  ||
	
	(member k '(PRODUCT FUNCTION QUOTIENT SET PARFUNCTION))
	--> (append
	      (illegal-tags-2 ids (first subterms))
	      (illegal-tags-2 (append (binding-ids-of-term term) ids)
			(second subterms)))  ||
	
	(eql k 'LAMBDA)
	--> (illegal-tags-2 (cons (bound-id-of-lambda-term term) ids)
		      (car subterms))  ||

	(eql k 'BOUND-ID-TERM)	
	--> (collect-illegal-tags #'illegal-tags-2
				  (append (bound-ids-of-bound-id-term term)
					  ids)
				  subterms) ||
	t
	--> (collect-illegal-tags #'illegal-tags-2 ids subterms) fi)))


(defun induction-var-used (bound-id-term)
    (let* ((bound-id-term (remove-outer-tags bound-id-term)))
      (member (car (last (bound-ids-of-bound-id-term bound-id-term)))
	    (free-vars (term-of-bound-id-term bound-id-term)))))



;;; Collect all the subterms with tags.
(defun all-subterms-with-tags (term)
    (Pif (eql (kind-of-term term) 'TAGGED)
	--> (cons term (all-subterms-with-tags (term-of-tagged-term term)))  ||
	t
	--> (mapcar #'all-subterms-with-tags (subterms-of-term term)) fi))



;;; do-indicated-computations: term -> term.  Perform the computations
;;; indicated by the tags in the argument as far as possible, never
;;; failing.   This function, and some of its supporting functions, are
;;; somewhat dependent on term representation.

(defun do-indicated-computations (term)
    (let* ((recursive-result
	     (map-on-subterms #'do-indicated-computations term)))
      (Pif (eql (kind-of-term term) 'TAGGED)
	  --> (initialize-and-compute
		(tag-of-tagged-term term)
		(do-indicated-computations
		  (term-of-tagged-term term))) ||  
	  (prl-every (mapcar #'eql (cddr term) (cddr recursive-result))
			#'(lambda (x) x))	; Preserve Ttrees if
	  --> term  ||			        ; possible.
	  t
	  --> recursive-result fi)))



;;;  The next blob of stuff comprises the auxiliaries for
;;;  do-indicated-computations.

(for
  (i in '((INCOMPLETE       compute-incomplete)
	  (MINUS            compute-minus)
	  (ADD              compute-binary)
	  (SUB              compute-binary)
	  (MUL              compute-binary)
	  (DIV              compute-binary)
	  (MOD              compute-binary)
	  (ATOMEQ           compute-atomeq)
	  (INTEQ            compute-inteq)
	  (INTLESS          compute-intless)
	  (IND              compute-ind)
	  (LIST-IND         compute-list-ind)
	  (DECIDE           compute-decide)
	  (SPREAD           compute-spread)
	  (APPLY            compute-apply)
	  (TERM-OF-THEOREM  compute-term-of-theorem)
	  (REC-IND          compute-rec-ind)
	  (SIMPLE-REC-IND   compute-simple-rec-ind)
	  (TAGGED           compute-tagged)))
  
  (do (setf (get (car i) 'prl-computer) (cadr i))))

(for (i in
	'(UNIVERSE VOID ANY ATOM TOKEN INT POS-NUMBER OBJECT
		   LIST NIL CONS UNION INL INR PRODUCT PAIR
		   FUNCTION LAMBDA QUOTIENT SET FIX DOM PAR-FUNCTION
		   BOUND-ID-LIST APPLY-PARTIAL VAR RECURSIVE SIMPLE-REC 
		   EQUAL AXIOM LESS BOUND-ID-TERM))
     (do (setf (get i 'prl-computer) 'null-computation)))


(defvar *computation-can-continue*)

(defvar *step-count*)

(defvar *max-step-count*)

(defun increment-step-count ()
    (Pif (zerop *max-step-count*)
	--> (progn (<- *step-count* (1+ *-*)) nil)  ||
	t
	--> (progn (<- *step-count* (1+ *-*))
		   (Pif (eql *step-count* *max-step-count*)
		       --> (setq *computation-can-continue* nil) fi) nil) fi))



;;; Used in the ML primitive no_extraction_compute
(defun no-extraction-compute (tag term)
    (let* ((saved-computer (get 'TERM-OF-THEOREM 'prl-computer))
	   (*computation-can-continue* t)
	   (*step-count* 0)
	   (*max-step-count* tag))
      (setf (get 'TERM-OF-THEOREM 'prl-computer) 'null-computation)
      (unwind-protect
	  (let ((cterm (compute term)))
;	    (break)
	  (values cterm *step-count*))
	(setf (get 'TERM-OF-THEOREM 'prl-computer) saved-computer))))

(defun initialize-and-compute (tag term)
    (let* ((*computation-can-continue* t)
	   (*step-count* 0)
	   (*max-step-count* tag))
      (compute term)))

(defun compute (term) 
    (Pif *computation-can-continue*
	--> (funcall (get (kind-of-term term) 'prl-computer) term)  ||
	t
	--> term fi))

(defun subst-for-bound-ids (terms term-with-bound-ids)
    (let* ((term-with-bound-ids (remove-outer-tags  term-with-bound-ids)))
      (increment-step-count)
      (substitute
	(car (subterms-of-term term-with-bound-ids))
	(mapcar #'(lambda (x y) (list y x))
		terms
		(binding-ids-of-term term-with-bound-ids)))))

(defun clobber-Ttree (term) (setf (Ttree-of-term term) nil))

(defun null-computation (term) term)

(defun compute-apply (term)
    (let* ((e (function-of-apply-term term))
	   (new-e (compute e)))
      (Pif (and (is-lambda new-e) *computation-can-continue*)
	  --> (compute (subst-for-bound-ids
			 (list (arg-of-apply-term term))
			 new-e)) ||
	  (eql e new-e)
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (function-of-apply-term result) new-e)
		   (clobber-Ttree result)
		   result) fi)))

(defun compute-spread (term)
    (let* ((e (value-of-spread-term term))
	   (new-e (compute e)))
      (Pif (and (is-pair new-e) *computation-can-continue*)
	  --> (compute (subst-for-bound-ids
			 (list (leftterm-of-pair-term new-e)
			       (rightterm-of-pair-term new-e))
			 (term-of-spread-term term)))  ||
	  (eql e new-e)
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (value-of-spread-term result) new-e)
		   (clobber-Ttree result)
		   result) fi)))


(defun compute-decide (term)
    (let* ((e (value-of-decide-term term))
	   (new-e (compute e)))
      (Pif (and (is-injection new-e) *computation-can-continue*)
	  --> (compute (subst-for-bound-ids
			 (list (term-of-injection-term new-e))
			 (Pif (eql (kind-of-term new-e) 'INR)
			     --> (rightterm-of-decide-term term) ||
			     t
			     --> (leftterm-of-decide-term term) fi))) ||
	  (eql e new-e)
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (value-of-decide-term result) new-e)
		   (clobber-Ttree result)
		   result) fi)))

(defun compute-ind (term)
    (let* ((e (value-of-ind-term term))
	   (new-e (compute e)))
      (Pif (and (is-number new-e) *computation-can-continue*)
	  --> (Plet (n (val-of new-e))
		   (Pif (zerop n)
		       --> (progn
			     (increment-step-count)
			     (compute (baseterm-of-ind-term term))) ||
		       (plusp n)
		       --> (compute (subst-for-bound-ids
				      (list
					(make-int-term n)
					(Plet (result (copy term))
					     (setf (value-of-ind-term
						     result)
						   (make-int-term (1- n)))
					     (clobber-Ttree result)
					     result) )
				      (upterm-of-ind-term term)))  ||
		       t
		       --> (compute (subst-for-bound-ids
				      (list
					(make-int-term n)
					(Plet (result (copy term))
					     (setf (value-of-ind-term
						     result)
						   (make-int-term (1+ n)))
					     (clobber-Ttree result)
					     result) )
				      (downterm-of-ind-term term))) fi)) ||
	  (eql e new-e)
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (value-of-ind-term result) new-e)
		   (clobber-Ttree result)
		   result) fi)))

(defun compute-atomeq (term)
    (let* ((e1 (leftterm-of-decision-term term))
	   (e2 (rightterm-of-decision-term term))
	   (new-e1 (compute e1))
	   (new-e2 (compute e2)))
      (Pif (and (eql 'TOKEN (kind-of-term new-e1))
	       (eql 'TOKEN (kind-of-term new-e2))
	       *computation-can-continue*)
	  --> (progn
		(increment-step-count)
		(compute (Pif (equal (atom-of-token-term new-e1)
				    (atom-of-token-term new-e2))
			     --> (if-term-of-decision-term term) ||
			     t
			     --> (else-term-of-decision-term term) fi)))  ||
	  (and (eql e1 new-e1) (eql e2 new-e2))
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (leftterm-of-decision-term result) new-e1)
		   (setf (rightterm-of-decision-term result) new-e2)
		   (clobber-Ttree result)
		   result) fi)))


(defun compute-intless (term)
    (let* ((e1 (leftterm-of-decision-term term))
	   (e2 (rightterm-of-decision-term term))
	   (new-e1 (compute e1))
	   (new-e2 (compute e2)))
      (Pif (and (is-number new-e1)
	       (is-number new-e2)
	       *computation-can-continue*)
	  --> (progn
		(increment-step-count)
		(compute (Pif (< (val-of new-e1) (val-of new-e2))
			     --> (if-term-of-decision-term term) ||
			     t
			     --> (else-term-of-decision-term term) fi)))  ||
	  (and (eql e1 new-e1) (eql e2 new-e2))
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (leftterm-of-decision-term result) new-e1)
		   (setf (rightterm-of-decision-term result) new-e2)
		   (clobber-Ttree result)
		   result) fi)))

(defun compute-inteq (term)
    (let* ((e1 (leftterm-of-decision-term term))
	   (e2 (rightterm-of-decision-term term))
	   (new-e1 (compute e1))
	   (new-e2 (compute e2)))
      (Pif (and (is-number new-e1)
	       (is-number new-e2)
	       *computation-can-continue*)
	  --> (progn
		(increment-step-count)
		(compute (Pif (eql (val-of new-e1) (val-of new-e2))
			     --> (if-term-of-decision-term term) ||
			     t
			     --> (else-term-of-decision-term term) fi)))  ||
	  (and (eql e1 new-e1) (eql e2 new-e2))
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (leftterm-of-decision-term result) new-e1)
		   (setf (rightterm-of-decision-term result) new-e2)
		   (clobber-Ttree result)
		   result) fi)))

(defun compute-incomplete (term)
  (declare (ignore term))
  (ref-error '|Attempted Direct Computation of Incomplete THM.|))

(defun compute-minus (term)
    (let* ((e (term-of-minus-term term))
	   (new-e (compute e)))
      (Pif (and (is-number new-e) *computation-can-continue*)
	  --> (Plet (n (val-of new-e))
		   (Pif  (minusp n) --> (increment-step-count) fi)
		   (make-int-term (* -1 n))) ||
	  (eql e new-e)
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (term-of-minus-term result) new-e)
		   (clobber-Ttree result)
		   result) fi)))

(defun compute-binary (term)
    (let* ((e1 (leftterm-of-binary-term term))
	   (e2 (rightterm-of-binary-term term))
	   (new-e1 (compute e1))
	   (new-e2 (compute e2))
	   (k (kind-of-term term)))
      (Pif (and (is-number new-e1)
	       (is-number new-e2)
	       *computation-can-continue*)
	  --> (let* ((m (val-of new-e1))
		     (n (val-of new-e2))
		     (result
		       (Pif (eql k 'ADD)
			   --> (+ m n) ||
			   (eql k 'SUB)
			   --> (- m n) ||
			   (eql k 'MUL)
			   --> (* m n) ||
			   (eql k 'DIV)
			   --> (prl-div m n) ||
			   t
			   --> (prl-mod n m) fi)))
		(increment-step-count)
		(make-int-term result))  ||
	  (and (eql e1 new-e1) (eql e2 new-e2))
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (leftterm-of-binary-term result) new-e1)
		   (setf (rightterm-of-binary-term result) new-e2)
		   (clobber-Ttree result)
		   result) fi)))

(defun compute-list-ind (term)
    (let* ((e (value-of-ind-term term))
	   (new-e (compute e)))
      (Pif (and (is-list new-e) *computation-can-continue*)
	  --> 
	  (Pif (is-nil new-e)
	      --> (progn
		    (increment-step-count)
		    (compute (baseterm-of-list-ind-term term))) ||
	      t
	      --> (compute (subst-for-bound-ids
			     (list
			       (head-of-cons-term new-e)
			       (tail-of-cons-term new-e)
			       (Plet (result (copy term))
				    (setf (value-of-ind-term result)
					  (tail-of-cons-term new-e))
				    (clobber-Ttree result)
				    result))
			     (upterm-of-list-ind-term term))) fi) ||
	  (eql e new-e)
	  --> term  ||
	  t
	  --> (Plet (result (copy term))
		   (setf (value-of-list-ind-term result) new-e)
		   (clobber-Ttree result)
		   result) fi)))


(defun compute-rec-ind (term)
    (let* ((term-list (term-list-of-bound-id-list-term
			(bound-id-list-term-of-rec-ind-term term)))
	   (ids (bound-ids-of-bound-id-list-term
		  (bound-id-list-term-of-rec-ind-term term)))
	   (base-term (term-of-rec-ind-term term))
	   (selected (position (id-of-rec-ind-term term) ids)))
      (increment-step-count)
      (substitute
	(term-of-bound-id-term (nth selected term-list))
	(append
	  (list (list
		  (car (bound-ids-of-bound-id-term (nth selected term-list)))
		  base-term))
	  (for (x in ids)
	       (z in term-list)
	       (save
		 (list
		   x
		   (lambda-term
		     'LAMBDA
		     nil
		     (car (bound-ids-of-bound-id-term z))
		     (rec-ind-term
		       'REC-IND
		       nil
		       (var-term 'VAR nil (car (bound-ids-of-bound-id-term z)))
		       (bound-id-list-term-of-rec-ind-term term)
		       x)))))))))



(defun compute-simple-rec-ind (term)
    (let* ((e (value-of-simple-rec-ind-term term))
	   (ind-term (term-of-simple-rec-ind-term term))
	   (z (second (bound-ids-of-bound-id-term ind-term)))
	   (ind-fcn (lambda-term
		      'LAMBDA nil
		      z
		      (simple-rec-ind-term
			'SIMPLE-REC-IND
			nil
			(var-term 'VAR nil z)
			ind-term))))
      (compute (subst-for-bound-ids (list ind-fcn e) ind-term))))




(defun compute-tagged (term)
  (declare (ignore term))
  (tagged-term-err))

(defun compute-term-of-theorem (term)
  (let ((name (name-of-term-of-theorem-term term)))
    (cond ((and (lib-member name)
		(eql 'THM
		    (sel (object (library-object name))
			 kind)))
	   (increment-step-count)
	   (compute (evaluable-term-of-theorem
		      (name-of-term-of-theorem-term term))))
	  (t
	   term))))

(defun make-int-term (val)
    (Pif (< val 0)
	--> (minus-term
	      'MINUS nil
	      (make-int-term (* -1 val))) ||
	t -->
	(pos-number-term 'POS-NUMBER nil val) fi))



;;; ********************************************************************************
;;; ********************************************************************************

;;; The following code is for an experimental evaluator /
;;; symbolic-computer.  It is, so far, only implemented for the
;;; functional subset of Nuprl.

;;; ********************************************************************************
;;; ********************************************************************************


(defun id-suffix (symbol)
  (let* ((str (symbol-name symbol))
	 (i (position #\@ str)))
    (if (null i)
	 0
	 (or (parse-integer (subseq str (1+ i)) :junk-allowed t) 0))))

(defun max-id-suffix (term)
  (case (kind-of-term term)
    (apply
     (max (max-id-suffix (function-of-apply-term term))
	  (max-id-suffix (arg-of-apply-term term))))
    (LAMBDA
     (max (id-suffix (bound-id-of-lambda-term term))
      (max-id-suffix (term-of-lambda-term term))))
    (VAR
     (id-suffix (id-of-var-term term)))
    (otherwise
     0)))

;;; Used to generate new ids of the form "x@n".
(defvar *new-id-suffix* 0)


;;; There must be at least one term.  Make a left-associated application sequence.
(defun make-application (terms)
  (labels ((aux (revd-terms)
	     (if (null (cdr revd-terms))
		  (car revd-terms)
		  (apply-term
		    'apply nil
		    (aux (cdr revd-terms))
		    (car revd-terms)))))
    (aux (reverse terms))))



(defvar *extractions-scanned*)

(defun new-id-from (id)
  (let* ((str (symbol-name id))
	 (i (position #\@ str))
	 (suffix-string (with-output-to-string (moose)	; ugh.
			  (princ *new-id-suffix* moose))))
    (incf *new-id-suffix*)
    (if (or (null i) (= i 0))
	 (intern (concatenate 'string str "@" suffix-string) (find-package 'nuprl))
	 (intern (concatenate 'string (subseq str 0 i) "@" suffix-string)
		 (find-package 'nuprl)))))

;;; All values in the environment must be closures.
(defun get-closure (id env)
  (cdr (assoc id env)))


;;; A new term kind for intermediate use in normalization.
;;; kind is 'CONSTANT-VAR.
(deftuple constant-var-term kind Ttree var-term)


;;; fun must take as arguments a term, an env, and a constant-vars-with-binders.
;;; No action is taken on terms with no subterms.
(defun apply-with-envs-to-subterms (fun term env constant-vars-with-binders)
  (case (kind-of-term term)
    (LAMBDA
     (let* ((id (bound-id-of-lambda-term term))
	    (new-lambda-term (lambda-term 'LAMBDA nil id nil))
	    (new-var-term (var-term 'VAR nil id))
	    (constant-var-term (constant-var-term 'CONSTANT-VAR
						  nil new-var-term))
	    (lambda-body
	      (funcall
		fun
		(term-of-lambda-term term)
		`((,id ,constant-var-term . ()) ,@env)
		`((,new-var-term . ,new-lambda-term)
		  ,@constant-vars-with-binders))))
       (setf (term-of-lambda-term new-lambda-term) lambda-body)
       new-lambda-term))
    (FUNCTION
     (let* ((id (bound-id-of-function-term term))
	    (new-function-term (function-term 'FUNCTION nil id nil nil))
	    (new-var-term (var-term 'VAR nil id))
	    (constant-var-term (constant-var-term 'CONSTANT-VAR
						  nil new-var-term))
	    (new-lefttype
	      (funcall
		fun
		(lefttype-of-function-term term)
		env constant-vars-with-binders))
	    (new-righttype 
	      (funcall
		fun
		(righttype-of-function-term term)
		`((,id ,constant-var-term . ()) ,@env)
		`((,new-var-term . ,new-function-term)
		  ,@constant-vars-with-binders))))
       (setf (lefttype-of-function-term new-function-term) new-lefttype)
       (setf (righttype-of-function-term new-function-term) new-righttype)
       new-function-term))
    (apply
     (apply-term
       'APPLY nil
       (funcall
	 fun
	 (function-of-apply-term term) env constant-vars-with-binders)
       (funcall
	 fun
	 (arg-of-apply-term term) env constant-vars-with-binders)))
    (otherwise					; assume term a constant    
     term)))


;;; should nil out ttree. 
(defun change-id-of-term (term new-id) 
  (case (kind-of-term term)
    (VAR 
     (setf (id-of-var-term term) new-id))
    (LAMBDA
     (setf (bound-id-of-lambda-term term) new-id))
    (FUNCTION
     (setf (bound-id-of-function-term term) new-id))))

;;; constant-vars-with-binders must be an a list each of whose elements is a
;;; var-term lambda-term pair.  Mutates the argument constant-vars-with-binders
;;; so that the ids of the terms associated with the id arg are new (and
;;; distinct).
(defun resolve-var-constant-var-conflicts (var constant-vars-with-binders)
  (let* ((id (id-of-var-term var)))
    (mapc #'(lambda (x)
	      (let ((var (car x))
		    (binding-term (cdr x)))
		(if (eql id (id-of-var-term var))
		     (let* ((new-id (new-id-from id)))
		       (change-id-of-term var new-id)
		       (change-id-of-term binding-term new-id)))))
	  constant-vars-with-binders)
    nil))

(defun resolve-constant-var-constant-var-conflicts
       (constant-var constant-vars-with-binders)
  (let* ((var-to-avoid (var-term-of-constant-var-term constant-var))
	 (id-to-avoid (id-of-var-term var-to-avoid)))
    (do ((cvs constant-vars-with-binders))
	((or (null cvs)
	     (eql (caar cvs) var-to-avoid))
	 nil)
      (let* ((tmpv (pop cvs))
	     (var (car tmpv))
	     (binding-term (cdr tmpv)))
	(if (eql id-to-avoid (id-of-var-term var))
	     (let* ((new-id (new-id-from id-to-avoid)))
	       (change-id-of-term var new-id)
	       (change-id-of-term binding-term new-id)))))))



;;; All values in the environment must be closures.
(defun apply-env (term env constant-vars-with-binders)
  (case (kind-of-term term)
    (VAR
     (let* ((tmpv  (get-closure (id-of-var-term term) env))
	    (id-term (car tmpv))
	    (id-env (cdr tmpv)))
       (cond ((null id-term)
	      (resolve-var-constant-var-conflicts
		term constant-vars-with-binders)
	      term)
	     (t	
	      (apply-env id-term id-env constant-vars-with-binders)))))
    (CONSTANT-VAR
     (resolve-constant-var-constant-var-conflicts
       term constant-vars-with-binders)
     (var-term-of-constant-var-term term))
    (otherwise
     (apply-with-envs-to-subterms #'apply-env term env
				  constant-vars-with-binders))))


(defun make-final-application
       (fun env arg-closures constant-vars-with-binders)
  (make-application
    (mapcar #'(lambda (p)
		(let ((term (car p))
		      (term-env (cdr p)))
		  (apply-env term term-env constant-vars-with-binders)))
	    `( (,fun . ,env) ,@arg-closures ) )))




(defvar *normalizep*)
(defvar *expand-extractions-p*)
(defvar *excepted-extractions*)

(defun lambda-compute
       (term
	&optional
	(normalizep nil)
	(expand-extractions-p t)
	(excepted-extractions ()))
  
  (setq *new-id-suffix* (1+ (max-id-suffix term))
	*expand-extractions-p* expand-extractions-p
	*normalizep* normalizep
	*excepted-extractions* excepted-extractions
	*extractions-scanned* ())
  (lambda-compute$ term () ()))

;;; There is absolutely no error-checking yet.
(defun lambda-compute$ (term env constant-vars-with-binders)

  (do ((donep nil)
       (current-term term )			; term to be evaluated.
       (current-env env)			; environment in which to evaluate
						; current-term.
       (current-args ()))			; postponed non-principal args with
						; environments they are to be evaluated in.
      
      (donep
	(if (not *normalizep*)
	     (make-final-application current-term current-env current-args
				     constant-vars-with-binders)
	     (if (member (kind-of-term current-term)
			'(LAMBDA FUNCTION))	; => current-args empty
		  (apply-with-envs-to-subterms
		    #'lambda-compute$ current-term current-env
		    constant-vars-with-binders)
		  (let*
		    ((k (kind-of-term current-term))
		     (fun (cond ((eql k 'VAR)
				 (resolve-var-constant-var-conflicts
				   current-term
				   constant-vars-with-binders)
				 current-term)
				((eql k 'CONSTANT-VAR)
				 (resolve-constant-var-constant-var-conflicts
				   current-term
				   constant-vars-with-binders)
				 (var-term-of-constant-var-term current-term))
				(t current-term))))
		    (make-application
		      (cons
			fun
			(mapcar
			  #'(lambda (p)
			      (let ((term (car p))
				    (term-env (cdr p)))
				(lambda-compute$ term term-env constant-vars-with-binders)))
			  current-args)))))))
    
    (case (kind-of-term current-term)
      (apply
       (push (cons (arg-of-apply-term current-term) current-env) current-args)
       (setq current-term (function-of-apply-term current-term)))
      (LAMBDA
       (if
	(null current-args)
	(setq donep t)
	(progn (push (cons (bound-id-of-lambda-term current-term)
			   (pop current-args))
		     current-env)
	       (setq current-term (term-of-lambda-term current-term)))))
      (VAR
       (let* ((tmpv  (get-closure (id-of-var-term current-term) current-env))
	      (term (car tmpv))
	      (env (cdr tmpv)))
	 (if (null term)
	      (setq donep t)
	      (setq current-term term
		    current-env env))))
      (CONSTANT-VAR
       (setq donep t))
      (TERM-OF-THEOREM
       (let* ((name (name-of-term-of-theorem-term current-term)))
	 (if (eql *expand-extractions-p*
		  (not (member name *excepted-extractions*)))
	      (progn
		(setq current-term (evaluable-term-of-theorem name)	; need check here
		      current-env nil)
		(cond ((not (member name *extractions-scanned*))
		       (setq *new-id-suffix* 
			     (1+ (max (max-id-suffix current-term) *new-id-suffix*)))
		       (push name *extractions-scanned*))))
	      (setq donep t))))
      (otherwise
       (setq donep t)))))




