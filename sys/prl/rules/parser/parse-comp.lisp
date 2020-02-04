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


(defun parse-computation-rule ()
    (Plet (where          nil                    ;-- 1 is left, 2 is right
          which          nil                    ;-- 'base','up',or 'down'
	  case           nil			;-- 'true' or 'false'
          term-to-reduce nil
          reduce-term-kind nil
          kind nil
	  new-ids nil
         )                                                          
        (Pif (not (eql (kind-of-term ref-concl) 'EQUAL)) -->
            (ref-error '|conclusion not appropriate for computation rule |)
         fi)                       
        (<- where (get-where$))
        (<- term-to-reduce (nth (1- where) (terms-of-equal-term ref-concl)))
        (<- reduce-term-kind (kind-of-term term-to-reduce))

        (Pif (eql reduce-term-kind 'APPLY) -->
            (comp-rule 'APPLY-COMP where)

	 || (eql reduce-term-kind 'APPLY-PARTIAL) -->
	    (comp-rule 'FIX-COMP where)

         || (eql reduce-term-kind 'SPREAD) -->
            (comp-rule 'SPREAD-COMP where)

         || (eql reduce-term-kind 'DECIDE) -->
            (comp-rule 'DECIDE-COMP where)

         || (eql reduce-term-kind 'IND) -->
             (<- which (get-ind-which$))
            (Pif (eql which '|down|) -->
                (<- kind 'IND-COMP-DOWN)
             || (eql which '|base|) -->  
                (<- kind 'IND-COMP-BASE)
             || (eql which '|up|) -->    
                (<- kind 'IND-COMP-UP)
             fi)
            (comp-rule kind where)

         || (eql reduce-term-kind 'LIST-IND) -->
            (comp-rule 'LIST-IND-COMP where)

         || (eql reduce-term-kind 'ATOMEQ) -->
	    (<- case (get-decision-case$))
	    (Pif (eql case '|true|) -->
                (<- kind 'ATOMEQ-COMP-TRUE)
             || (eql case '|false|) -->  
                (<- kind 'ATOMEQ-COMP-FALSE)
             fi)
            (comp-rule kind where)

         || (eql reduce-term-kind 'INTEQ) -->
	    (<- case (get-decision-case$))
	    (Pif (eql case '|true|) -->
                (<- kind 'INTEQ-COMP-TRUE)
             || (eql case '|false|) -->  
                (<- kind 'INTEQ-COMP-FALSE)
             fi)
            (comp-rule kind where)

         || (eql reduce-term-kind 'INTLESS) -->
	    (<- case (get-decision-case$))
	    (Pif (eql case '|true|) -->
                (<- kind 'INTLESS-COMP-TRUE)
             || (eql case '|false|) -->  
                (<- kind 'INTLESS-COMP-FALSE)
             fi)
            (comp-rule kind where)

	 || (eql reduce-term-kind 'DOM) -->
	    (<- new-ids (check-for-new-ids))
	    (dom-comp-rule 'DOM-COMP where new-ids)

	 || (eql reduce-term-kind 'REC-IND) -->
	    (comp-rule 'REC-IND-COMP where)

	 || (eql reduce-term-kind 'SIMPLE-REC-IND) -->
	    (ref-error '|Not yet, maybe never. Use direct computation.|)

         || t -->
            (ref-error '|conclusion not appropriate for this rule |)

         fi)
    )
)

(defun get-ind-which$ ()
    (Pif (or (not (eql token-type TId)) 
            (not (member token-val (list '|down| '|base| '|up|)))
        )-->
        (ref-error '|expecting 'down','base',or 'up' after 'reduce ...' |)

     || t -->
        (prog1 token-val (scan))
    
     fi)
)


(defun get-decision-case$ ()
    (Pif (or (not (eql token-type TId)) 
            (not (member token-val (list '|true| '|false|)))
        )-->
        (ref-error '|expecting 'true' or 'false' after 'reduce ...' |)

     || t -->
        (prog1 token-val (scan))
    
     fi)
)



(defun get-where$ ()
    (Pif (or (not (eql token-type TNbr))
            (< token-val 1)
            (> token-val (length (terms-of-equal-term ref-concl)))
        ) -->
        (ref-error (concat '| expecting a number indicating which term of |
                           '|the equality is to be reduced. |
                   )
        )           
      || t -->
         (prog1 token-val (scan))
      fi)
)


(defun parse-direct-comp-rule ()
    (Pif (eql token-val '|hyp|)
	--> (progn
	      (scan)
	      (Pif (eql token-type TNbr)
		  --> (Pif (or (< token-val 1) 
			      (> token-val (length ref-assums)))
			  --> (ref-error
				'|assum. num after is out of range.|) ||
			  t
			  --> (direct-comp-hyp-rule
				'DIRECT-COMP-HYP
				token-val
				(progn
				  (scan)
				  (check-for-using-term$ '||))) fi)  ||
		  t
		  --> (ref-error '|missing assum. num|) fi)) ||
	t
	--> (direct-comp-rule
	      'DIRECT-COMP
	      (check-for-using-term$ '||)) fi))
	    
