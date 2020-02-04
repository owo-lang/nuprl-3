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


;-- the parser

(defun open-action-stack () (send-to-best-Ttree ':open))
(defun yield () (send-to-best-Ttree ':yield))
(defun close-action-stack () (send-to-best-Ttree ':close))
(defun forget-parens () (send-to-best-Ttree ':forget-parens))

(global parse-a-declaration$)

;-- A parse table vector is a vector which maps token types to some value.
(Pdeftype parse-table-vec vector (nbr-token-types))
(Pdeftype parse-table-prec-vec int-vector (nbr-token-types))

(global delim-descr parse-table-vec)        ;-- A description of the token
(global left-binding-power parse-table-prec-vec)   
                                            ;-- The left binding power of
                                            ;-- the token
(global initial     parse-table-vec)        ;-- The function to call when
                                            ;-- this token occurs as the
                                            ;-- initial token of a term.
(global medial      parse-table-vec)        ;-- The function to call when
                                            ;-- this token appears in a
                                            ;-- medial position in the term.

(defun delim-descr-for (type)
    (sel delim-descr (type))
)

(defun parse-table-init ()

    ;-- Create the data structures used for best Ttree computation.
        (action-buffer-create)
        (BestTtree-create)

    ;-- Define precedence of operators, for disp-proof.l.
    (for (x in '((FUNCTION 6 5)  (UNION 6 5)  (PRODUCT 6 5)  (QUOTIENT 6 5)
                 (SET 6 5) (LAMBDA nil 95)  (IN 2 2) (INL nil 50) (INR nil 50)
                 (EQUAL 2 2)  (LESS  14 14)  (CONS 41 40)  (ADD 20 20)
                 (SUB  20 20)  (MUL  30 30)  (DIV  30 30)  (MOD 30 30)
                 (LIST 110 nil)  (APPLY 120 nil) (MINUS nil 50)
		 (PARTIALFUNCTION 6 5) (RECURSIVE nil 50)
		 (DOM nil 50) (APPLY-PARTIAL 120 nil) 
         )      )
         (do 
            (setf (get (car x) 'lprecedence) (cadr x))
            (setf (get (car x) 'rprecedence) (caddr x))
         )
    )

    ;-- Create and initialize the parsing tables.
        (<- delim-descr (new parse-table-vec))
        (<- initial (new parse-table-vec))
        (<- medial (new parse-table-vec))
        (<- left-binding-power (new parse-table-prec-vec))

    (for (x in `((,TAny      |any|        -1  parse-any        parse-err)
                 (,TArrow    |->|          6  parse-erri       parse-arrow)
                 (,TAt       |at|         -1  parse-erri       parse-err)
                 (,TAtom     |atom|       -1  parse-atom       parse-err)
                 (,TAtomeq   |atom_eq|    -1  parse-atomeq     parse-err)
                 (,TAxiom    |axiom|      -1  parse-axiom      parse-err)
                 (,TBslash   |\\|         -1  parse-lambda     parse-err)
                 (,TColon    |:|           6  parse-erri       parse-colon)
                 (,TComma    |,|          -1  parse-erri       parse-err)
                 (,TDblLsqrbrace |\[\[|   -1  parse-tagged     parse-err)
                 (,TDecide   |decide|     -1  parse-decide     parse-err)
                 (,TEqual    |=|           2  parse-erri       parse-equal)
                 (,TEndInput |end-input|   0  parse-erri       parse-err)
                 (,TFunction |function|   -1  parse-erri       parse-err)
                 (,TGreater  |>|           0  parse-erri       parse-err)
                 (,TId       |identifier| -1  parse-id         parse-err)
                 (,TIn       |in|          2  parse-erri       parse-in)
                 (,TInd      |ind|        -1  parse-ind        parse-err)
                 (,TInl      |inl|        -1  parse-inl        parse-err)
                 (,TInr      |inr|        -1  parse-inr        parse-err)
                 (,TInt      |int|        -1  parse-int        parse-err)
                 (,TInteq    |int_eq|     -1  parse-inteq      parse-err)
                 (,TIntless  |less|       -1  parse-intless    parse-err)
                 (,TLbrace   |{|          -1  parse-set        parse-err)
                 (,TLeft     |left|        0  parse-erri       parse-err)
                 (,TLess     |<|          14  parse-pair       parse-less)
                 (,TList-ind |list_ind|   -1  parse-list-ind   parse-err)
                 (,TList     |list|      110  parse-erri       parse-list)
                 (,TLparen   |(|         120  parse-parens     parse-apply)
                 (,TMinus    |-|          20  parse-minus      parse-sub)
		 (,TMlchar   |`|          -1  parse-erri       parse-err)
                 (,TMod      |mod|        30  parse-erri       parse-mod)
                 (,TNbr      |number|     -1  parse-pos-number parse-err)
                 (,TNew      |new|        -1  parse-erri       parse-err)
                 (,TNil      |nil|        -1  parse-nil        parse-err)
                 (,TOr       |union|      -1  parse-erri       parse-err)
                 (,TOver     |over|       -1  parse-erri       parse-err)
                 (,TPeriod   |.|          41  parse-erri       parse-cons)
                 (,TPlus     |+|          20  parse-erri       parse-add)
                 (,TProduct  |product|    -1  parse-erri       parse-err)
                 (,TPsign    |\#|          6  parse-erri       parse-prod)
                 (,TQuot     |//|          6  parse-erri       parse-err)
                 (,TQuote    |'|          -1  parse-erri       parse-err)
                 (,TQuotient |quotient|   -1  parse-erri       parse-err)
                 (,TRbrace   |}|           0  parse-erri       parse-err)
                 (,TRight    |right|       0  parse-erri       parse-err)
                 (,TRparen   |)|           0  parse-erri       parse-err)
                 (,TScolon   |;|           0  parse-erri       parse-err)
                 (,TSet      |set|        -1  parse-erri       parse-err)
                 (,TShriek   |!|          -1  parse-erri       parse-err)
                 (,TSlash    |/|          30  parse-erri       parse-div)
                 (,TSpread   |spread|     -1  parse-spread     parse-err)
                 (,TStar     |*|          30  parse-erri       parse-mul)
                 (,TToken    |token|      -1  parse-token      parse-err)
                 (,TTofTh    |term_of|    -1  parse-term-of    parse-err)
                 (,TUnion    |\||          6  parse-erri       parse-union)
                 (,TUniv     |U|          -1  parse-univ       parse-err)
                 (,TUniverse |universe|   -1  parse-erri       parse-err)
                 (,TUsing    |using|      -1  parse-erri       parse-err)
                 (,TVoid     |void|       -1  parse-void       parse-err)
		 (,TRec	     |rec|        -1  parse-rec        parse-err)
		 (,TRec-ind  |rec_ind|    -1  parse-rec-ind    parse-err)
		 (,TParFunArrow |~>|       6  parse-erri       parse-partial-arrow)
		 (,TFix      |fix|        -1  parse-fix        parse-err)
		 (,TLsqrbrace |\[|       120  parse-erri      parse-apply-partial)
		 (,TRsqrbrace |\]|         0  parse-erri       parse-err)
		 (,TDom      |dom|        -1  parse-dom        parse-err)
                 (,TObject   |object|     -1  parse-object        parse-err)
		 ;; Tlet is used for making bindings in the eval subsystem.
		 (,Tlet      |let|        -1  parse-id         parse-err)	
               )
         )
         (do 
             (<- (sel delim-descr ((car x))) (cadr x))
             (<- (sel left-binding-power ((car x))) (caddr x))
             (<- (sel initial ((car x))) (cadddr x))
             (<- (sel medial ((car x))) (car (cddddr x)))
         )
    )    
)

(defun parse (Ttree)
    (scan-init Ttree)
    (scan)
    (parse-from-current-Ttree)
)

(defun parse-from-current-Ttree ()
    (<- parse-a-declaration$ 'no)
    (activate-BestTtree)
    (unwind-protect
        (parse$ 0)
        (deactivate-BestTtree)
    )
)

;-- On each call to a parsing routine activating-type is SET to the
;-- type of the token causing this routine to be called.  If the routine is
;-- an initial routine, activating-value is SET to the value of the token
;-- causing the routine to be called.  
(declaim (special activating-type activating-value right-binding-power))

(defun parse$ (right-binding-power)
    (open-action-stack)
    (flush-token-actions)
    (Ploop
        (local left (do-initial))
        (while (< right-binding-power (sel left-binding-power (token-type))))
        (do
            (<- activating-type token-type)
            (eat-token$)
            (<- left (do-medial left))
        )
        (result (progn (close-action-stack) left))
    )
)   


(defun do-initial ()
    (<- activating-type   token-type)
    (<- activating-value  token-val)
    (scan)
    (funcall (sel initial (activating-type)))
)


(defun do-medial (left)
    (funcall (sel medial (activating-type)) left)
)

(defun parse-err (left)
  (declare (ignore left))
    (parse-error (concat '|cannot have "|
                         (sel delim-descr (activating-type))
                         '|" following "|
                         (implode (cdr (yield)))
                         '|".|
                 ) 
    )
)

(defun parse-erri ()
    (parse-error (concat '|"|
                         (sel delim-descr (activating-type))
                         '|" cannot begin a term.|
                 )
    ) 
)

(defun parse-error (message)
    (throw 'process-err (list 'ERR (concat '|parse-error -- | message)))
)

(defun parse-any ()
    (check$ TLparen 'any)
    (Plet (val (parse$ 0))
        (check$ TRparen 'any)
        (any-term 'ANY (yield) val)
    )
)


(defun parse-arrow (left)   
    (Plet (right (parse$ 5))
        (function-term 'FUNCTION (yield) nil left right)
    )
)

(defun parse-partial-arrow (left)
    (Plet (right (parse$ 5))
	(parfunction-term 'PARFUNCTION (yield) nil left right)
    )
)

(defun parse-atom ()
    (atom-term 'ATOM (yield))
)

(defun parse-axiom ()
    (axiom-term 'AXIOM (yield))
)

(defun parse-lambda ()
    (Plet (bound-id (check$ TId 'lambda))
        (check$ TPeriod 'lambda)
        (Plet (term (parse$ 95))
            (lambda-term 'LAMBDA (yield) bound-id term)
        )
    )
)

(defun parse-colon (left)
    (Pif (not (eql (kind-of-term left) 'VAR)) -->
        (parse-error '|only identifiers may immediately precede a colon. |)
     fi)
    (Plet (id    (id-of-var-term left)
          term  (parse$ 6)
         )
        (Pif (eql token-type TPsign) -->
            (eat-token$)
            (Plet (rightterm (parse$ 5))
                (product-term  'PRODUCT (yield) id term rightterm)
            )
                             
         || (eql token-type TArrow) -->
            (eat-token$)
            (Plet (rightterm (parse$ 5))
                (function-term 'FUNCTION (yield) id term rightterm)
            )

	 || (eql token-type TParFunArrow) -->
	    (eat-token$)
	    (Plet (rightterm (parse$ 5))
	        (parfunction-term 'PARFUNCTION (yield) id term rightterm)
	    )

         || (not (eql parse-a-declaration$ 'yes)) -->
            (parse-error (concat 
                           '|improper use of a colon (or found a declaration|
                           '| while looking for a term |
                         )
            )                                           

         || t -->
            (<- parse-a-declaration$ 'did-one)
            (declaration (yield) id term)

         fi)
    )
)

(defun parse-decide ()
    (check$ TLparen 'decide)
    (Plet (value (parse$ 0))
        (check$ TScolon 'decide)
        (Plet (leftterm (parse-bound-id-term 1))
            (check$ TScolon 'decide)
            (Plet (rightterm (parse-bound-id-term 1))
                (check$ TRparen 'decide)
                (decide-term 'DECIDE (yield) value leftterm rightterm)
            )
        )
    )
)

(defun parse-token ()
    (token-term 'TOKEN (yield) activating-value)
)

(defun parse-equal (left)
    (Plet (terms (list left))
        (Ploop
            (local done nil)
            (while (not done))
            (do
                (<- terms (cons (parse$ 2) terms))
                (Pif (= token-type TEqual) -->
                    (eat-token$)
                 || t -->
                    (<- done t)
                 fi)
              )
        )
        (check$ TIn 'equal)
        (Plet (type (parse$ 2))
            (equal-term 'EQUAL (yield) type (nreverse terms))
        )
    )
)

(defun parse-id ()
    (var-term 'VAR (yield) activating-value)
)

(defun parse-in (left)
    (Plet (type (parse$ 2))
        (equal-term 'EQUAL (yield) type (list left))
    )
)

(defun parse-ind ()
    (check$ TLparen 'induction)
    (Plet (value (parse$ 0))
        (check$ TScolon 'induction)
        (Plet (downterm (parse-bound-id-term 2))
            (check$ TScolon 'induction)
            (Plet (baseterm (parse$ 0))
                (check$ TScolon 'induction)
                (Plet (upterm (parse-bound-id-term 2))
                    (check$ TRparen 'induction)
                    (ind-term 'IND (yield) value downterm baseterm upterm)
                )
            )
        )
    )
)


;;;  These were changed so that the argument to inl and inr must be enclosed in
;;; parentheses.  Without this the best ttree for inl(axiom) was being computed
;;; as inlaxiom because the parentheses were understood to be redundant and were
;;; being removed.
(defun parse-inl ()
    (check$ TLparen 'inl)
    (Plet (term (parse$ 0))
	 (check$ TRparen 'inl)
	 (injection-term 'INL (yield) term)))

(defun parse-inr ()
    (check$ TLparen 'inr)
    (Plet (term (parse$ 0))
	 (check$ TRparen 'inr)
	 (injection-term 'INR (yield) term)))

;(defun parse-inl ()
;    (Plet (arg (parse$ 50))
;        (injection-term 'INL (yield) arg)
;    )
;)
;
;(defun parse-inr ()
;    (Plet (arg (parse$ 50))
;        (injection-term 'INR (yield) arg)
;    )
;)

(defun parse-dom ()
    (Plet (arg (parse$ 50))
	 (dom-term 'DOM (yield) arg)
    )
)

(defun parse-int ()
    (int-term 'INT (yield))
)


(defun parse-object ()
    (object-term 'OBJECT (yield))
)


(defun parse-set ()
    (Plet (term (parse$ 6))
        (Pif (and
                (eql (kind-of-term term) 'VAR)
                (= token-type TColon)
            ) -->
            (Plet (id (id-of-var-term term))
                (eat-token$)
                (parse-set-tail id (parse$ 6))
            )

         || (eql token-type TUnion) -->
            (parse-set-tail nil term)

         || t -->
            (parse-error '|set syntax is {x:A\|B} or {A\|B} |)
         fi)
    )
)

(defun parse-set-tail (id lefttype)
    (check$ TUnion 'set)
    (Plet (righttype (parse$ 0))
        (check$ TRbrace 'set)
        (set-term 'SET (yield) id lefttype righttype)
    )
)

(defun parse-pair ()
    (Plet (left  (parse$ 0))
        (check$ TComma 'pair)
        (Plet (right (parse$ 0))
            (check$ TGreater 'pair)
            (pair-term 'PAIR (yield) left right)
        )
    )
)

(defun parse-less (left)
    (Plet (right (parse$ 14))
        (less-term 'LESS (yield) left right)
    )
)

(defun parse-list-ind ()
    (check$ TLparen '|list induction|)
    (Plet (value (parse$ 0))
        (check$ TScolon '|list induction|)                              
        (Plet (baseterm (parse$ 0))
            (check$ TScolon '|list induction|)
            (Plet (upterm (parse-bound-id-term 3))
                (check$ TRparen '|list induction|) 
                (list-ind-term 'LIST-IND (yield) value baseterm upterm)
            )
        )
    )
)

;--
;-- rec_ind form is:
;--
;--   rec_ind(term;g1,x1.t1;....;gn.xn.tn;gi)
;--

(defun parse-rec-ind ()
    (check$ TLparen '|rec_ind|)
    (Plet (value (parse$ 0))
        (check$ TScolon '|rec_ind|)
	(parse-fix-or-rec-ind-tail TRec-ind value)
     )
)

 
;--
;-- fix form is:
;--
;--    fix(f1,y,b1; ... ;fn,yn.bn;fi)
;--

(defun parse-fix ()
    (check$ TLparen '|fix|)
    (parse-fix-or-rec-ind-tail TFix nil)
)




;--
;-- parse-fix-or-rec-ind-tail
;--
;-- parses the tail of a fix or rec_ind term which is of the form
;--
;--        f1,x1.b1;f2,x2,b2; .... ;fn,xn.bn;fi)
;--
;-- note that f1, ... fn must be distinct and that fi must occur among them.
;--

(defun parse-fix-or-rec-ind-tail (tk value)
    (Plet (term-list   nil
	  ids         nil
	  select-var  nil
	  err-message (Pif (eql tk TFix) --> '|fix|
			  
		       || t --> '|rec_ind|
		       
		       fi)
	  )
        (Ploop
	  (local done nil)
	  (while (not done))
	  (do
	    (<- ids (cons (check$ TId err-message) ids))
	    (Pif (eql token-type TComma) -->
	        (eat-token$)
		(<- term-list (cons (parse-bound-id-term 1) term-list))
		(Pif (and (token-is$ TRparen)
			 (eql (length ids) 1)
			 (eql tk TRec-ind))  -->
		    (eat-token$)
		    (<- done t)			
		 || t --> (check$ TScolon err-message)
		 fi
		)

	     || (eql token-type TRparen) -->
	        (eat-token$)
	        (<- done t)

	     || t --> (parse-error (concat '|unexpected character after | (car ids)))

	     fi)
           )
         )
        (<- term-list (nreverse term-list))
	(<- select-var (car ids))
	(<- ids (nreverse (cdr ids)))
	(Pif (eql tk TFix) -->
            (check-conditions-on-fix-and-rec-ind
	          select-var ids term-list err-message)
            (fix-term 'FIX
		      (yield)
		      (bound-id-list-term 'BOUND-ID-LIST nil ids term-list)
		      select-var
	    )

	 || (null ids) -->
	    (simple-rec-ind-term
	      'SIMPLE-REC-IND
	      (yield)
	      value
	      (bound-id-term
		`BOUND-ID-TERM
		nil
		(cons select-var (bound-ids-of-bound-id-term (car term-list)))
		(term-of-bound-id-term (car term-list))))

	 || t -->
	    (check-conditions-on-fix-and-rec-ind
	          select-var ids term-list err-message)
	    (rec-ind-term 'REC-IND
			  (yield)
			  value
			  (bound-id-list-term 'BOUND-ID-LIST nil ids term-list)
			  select-var
	    )

	 fi)
   )
)

;--
;-- check that var occurs bound in a bound-id-term of the term list and
;-- check that the number of ids matches the length of the bound-id-lsit
;-- check that there are no repeated ids among the ids of the term list
;-- err-message will either be the atom '|fix| or '|rec-ind|.
;-- 

(defun check-conditions-on-fix-and-rec-ind (var ids bound-id-term-list err-message)
    (Plet
      (msg (check-fix-or-rec-ind-term-constraints var ids bound-id-term-list err-message))
      (cond (msg (parse-error msg))
	    (t nil)
      )
     )
)


;--
;-- Perform the checks for both ml and the term parser.   Returns nil if no
;-- errors, and an error message otherwise.
;--

(defun all-bound-id-terms (term-list)
    (cond ((null term-list) t)
	  (t (and (equal 'BOUND-ID-TERM (kind-of-term (car term-list)))
		  (all-bound-id-terms (cdr term-list))
	     )
	  )
     )
 )

(defun check-fix-or-rec-ind-term-constraints (var ids bound-id-term-list err-message)
    (Pif (not (member var ids)) -->
	     (concat var '| does not occur bound in | err-message '| term.|)
     || (not (equal (length ids) (length bound-id-term-list))) -->
             (concat '|Number of ids does not match the number of bound id terms in |
                     err-message '|term.|
             )
        
     || (not
	   (all-bound-id-terms    bound-id-term-list)
	) --> (concat '|Not a bound id term in | err-message '| term.|)
     || t --> nil
             (Ploop
                (local y (cdr ids)
		       z (car ids)
		       msg nil
                )
                (while (and y (null msg)))
                   (do
                      (Pif (member z y) -->
                          (setq msg
                            (concat z '| has multiple occurrence in | err-message '| term.|)
	                  )
                       || t --> 
                            (<- z (car y))
                            (<- y (cdr y))
		      fi)

	       )
	       (result msg)				
            )
     fi)
)







;--  rec form is:
;--
;--   rec(g1,x1.t1;....;gn,xn.tn;fix(f1,y1.b1;....;fn,yn.bn;fi);gi,term)
;--
(defun parse-rec ()
    (check$ TLparen '|rec|)
    (Plet (term-list nil
	  ids       nil
	  var       nil
	  fix-term  nil
	  term      nil
	  done      nil
	  id2       nil
	  simple-rec? nil
	 )
	 (Ploop
	  (while (and (not done) (not simple-rec?) (not (eql token-type TFix))))
	  (do
	    (<- ids (cons (check$ TId '|recursive |) ids))
	    (Pif (eql token-type Tcomma) -->
	        (eat-token$)
		(Pif (eql token-type TId) -->
		    (<- id2 (check$ TId '|rec|))
		    (Pif (eql token-type TPeriod) -->
		        (eat-token$)
		        (<- term-list
			    (cons (bound-id-term
				    'BOUND-ID-TERM
				    nil
				    (list id2)
				    (parse$ 0)
			          )
			          term-list
			    )
		         )
			 (check$ TScolon '|recursive |)
			
	             || t  -->
		        (check$ TRparen '|rec|)
		        (<- fix-term nil)
		        (<- term (var-term 'VAR nil id2))
		        (<- var (car ids))
		        (<- ids (cdr ids))
		        (<- done t)

		    fi)
		   
		|| t -->
		   (<- term (parse$ 0))
		   (check$ TRparen '|rec|)
		   (<- fix-term nil)
		   (<- var (car ids))
		   (<- ids (cdr ids))
		   (<- done t)
		
		fi)

	     || (and (token-is$ TPeriod) (eql (length ids) 1)) -->
		(eat-token$)
		(<- simple-rec? t)
		
	     || t --> (parse-error (concat '|unexpected character after | (car ids)))

	     fi)
           )
         )
	 (Pif simple-rec? -->
	     (Plet (term (parse$ 0))
	       (check$ TRparen '|rec|)
	       (simple-rec-term 'SIMPLE-REC (yield) (car ids) term))
	  || t -->
             (<- term-list (nreverse term-list))
	     (<- ids (nreverse ids))
	     (Pif (eql token-type TFix) -->
	         (open-action-stack)
                 (check$ TFix '|rec|)
                 (<- fix-term (parse-fix))
	         (close-action-stack)
                 (check$ TScolon '|rec|)
                 (<- var (check$ TId '|rec|))
                 (check$ TComma '|rec|)
                 (<- term (parse$ 0))
                 (check$ TRparen '|rec|)
       	      fi)
	     (check-conditions-on-rec-term ids term-list fix-term var)
	     (recursive-term 'RECURSIVE
			     (yield)
       			     (bound-id-list-term 'BOUND-ID-LIST nil ids term-list)
			     fix-term
			     var
	       	             term
	     )
	  fi)        
     )
)

;--
;-- check-conditions-on-rec-term
;--
;--   rec(g1,x1.t1;....;gn,xn.tn;fix(f1,y1.b1;....;fn,yn.bn;fi);gi,term)
;--
;-- The term lists in the rec form and in the 
;-- fix form it contains must be of the same length and the variable fi and gi
;-- must occur at the same position in these lists. Also, each gi must occur
;-- positively in each  tj. The fix term is optional.
;--

(defun check-conditions-on-rec-term (id-list termlist fixterm var1)
  (Plet (result (check-constraints-on-rec-term id-list termlist fixterm var1))
       (cond (result (parse-error result))
	     (t nil)
       )
  )
)

(defun check-constraints-on-rec-term (id-list termlist fixterm var1)
  (Plet (message nil)
    ;;- check that var1 occurs bound in rec's termlist
    (Pif (not (member var1 id-list)) -->
		 (setq message
		    (concat var1 '| does not occur bound in rec term|))
    ;-- check that there are no repeated ids bound in id-list
     || t -->
        (Ploop
		(local y (cdr id-list)
		       z (car id-list)
		)
		(while y)
		(do
		  (Pif (member z y) -->
		      (setq message
			 (concat z '| has multiple binding occurrence in rec term. |))
		   fi)
		  (<- z (car y))
		  (<- y (cdr y))
		)
        )
        ;-- check that all ids occur positively in term-list of rec form

        (Pif (not message) -->
          (for (v in id-list)
	   (do
	     (for (z in termlist)
		  (do
		     (Pif (not (occurs-positively v (term-of-bound-id-term z))
		         ) --> (setq message
			         (concat v '| does not occur positively in rec form. |)
			       )
                      fi)
                  )
	     )
	   )
          )
	fi)

      (Pif (and fixterm (not message)) -->
	;;- check that termlist and the termlist of the fix term have same length
       (Pif (not (eql (length termlist)
		     (length (term-list-of-bound-id-list-term
			       (bound-id-list-term-of-fix-term fixterm)
			      )
		     )
	         )
	     ) -->
                (setq message '|Mismatch in number of arguments of rec and fix terms. |)
		 
        fi)

	(Pif (not message) -->
	    (Plet (fix-id-list
	         (bound-ids-of-bound-id-list-term
		   (bound-id-list-term-of-fix-term fixterm)
	         )
	      var2
	          (id-of-fix-term fixterm)
	     )
	     ;;- check that var1 and var2 occur at the same position
	     ;;- in id-list and fix-id-list
	     (Pif (not (eql (position var1 id-list)
		          (position var2 fix-id-list)
		      )
	          ) --> (setq message 
			   (concat var1 '| and | var2 '| do not occur in the same |
				   '|relative position in rec and fix terms. |
			   )
		         )
	      fi)
         )
	fi)
       fi)
    fi)
   message
  )
)  
 

(defun parse-list (left)
    (list-term 'LIST (yield) left)
)

(defun parse-parens ()
    (Plet (term (parse$ 0))
        (Pif (and (eql (kind-of-term term) 'VAR) (token-is$ TComma)) -->
            (parse-quotient-tail (id-of-var-term term))

         || t -->
            (check$ TRparen 'paren)

	    (Pif (parens-are-redundant term) --> (forget-parens) fi)

	    (<- (Ttree-of-term term) (yield))
            term
         fi)
    )
)

(defun parens-are-redundant (term)
    (Plet (lprec (get (kind-of-term term) 'lprecedence)
	  rprec (get (kind-of-term term) 'rprecedence)
	  lbp (sel left-binding-power (token-type))
	 )
        (and
	  (or (null lprec) (< right-binding-power lprec))
	  (or (null rprec)
	      (>= right-binding-power lbp)
	      (< lbp rprec)
	  )
	)
    )
)

(defun parse-quotient-tail (id)
    (check$ TComma 'quotient)
    (Plet (id2 (check$ TId 'quotient))
	(cond ((eql id2 id)
	       (parse-error '|bound identifiers of quotient term must be distinct|)))
        (check$ TRparen 'quotient)
        (check$ TColon 'quotient)
        (Plet (lterm (parse$ 6))
            (check$ TQuot 'quotient)
            (Plet (rterm (parse$ 5))
                (quotient-term 'QUOTIENT (yield) (list id id2) lterm rterm)
            )
        )
    )
)


(defun parse-apply (left)
    (Plet (arg (parse$ 0))
        (check$ TRparen 'application)
        (apply-term 'APPLY (yield) left arg)
    )
)

(defun parse-apply-partial (left)
    (Plet (arg (parse$ 0))
	(check$ TRsqrbrace 'partial-application)
	(apply-partial-term 'APPLY-PARTIAL (yield) left arg)
    )
)

(defun parse-minus ()
    (Plet (arg (parse$ 40))
        (minus-term 'MINUS (yield) arg)
    )
)

(defun parse-sub (left)
    (Plet (right (parse$ 20))
        (binary-term 'SUB (yield) left right)
    )
)
 
(defun parse-mod (left)
    (Plet (right (parse$ 30))
        (binary-term 'MOD (yield) left right)
    )
)

(defun parse-pos-number ()
    (pos-number-term 'POS-NUMBER (yield) activating-value)
)

(defun parse-nil ()
    (nil-term 'NIL (yield))
)

(defun parse-union (left)
    (Plet (right (parse$ 5))
        (union-term 'UNION (yield) left right)
    )
)

(defun parse-cons (left)
    (Plet (right (parse$ 40))
        (cons-term 'CONS (yield) left right)
    )
)

(defun parse-add (left)
    (Plet (right (parse$ 20))
        (binary-term 'ADD (yield) left right)
    )
)

(defun parse-prod (left)
    (Plet (right (parse$ 5))
        (product-term 'PRODUCT (yield) nil left right)
    )
)

(defun parse-div (left)
    (Plet (right (parse$ 30))
        (binary-term 'DIV (yield) left right)
    )
)

(defun parse-spread ()
    (check$ TLparen 'spread)
    (Plet (val-term (parse$ 0))
        (check$ TScolon 'spread)
        (Plet (bound-term (parse-bound-id-term 2))
            (check$ TRparen 'spread)
            (spread-term 'SPREAD (yield) val-term bound-term)
        )
    )
)

(defun parse-mul (left)
    (Plet (right (parse$ 30))
        (binary-term 'MUL (yield) left right)
    )
)

(defun parse-univ ()
    (Pif (not (plusp activating-value)) -->
        (parse-error '|level number of a universe term must be > 0. |)
     fi)
    (universe-term 'UNIVERSE (yield) activating-value)
)

(defun parse-void ()
    (void-term 'VOID (yield))
)

(defun parse-term-of ()
    (check$ TLparen '|term of theorem|)
    (Plet (name (check$ TId '|term of theorem|))
        (check$ TRparen '|term of theorem|)
        (term-of-theorem-term 'TERM-OF-THEOREM (yield) name)
    )
)

(defun parse-atomeq ()
    (parse-decision-term 'ATOMEQ)
)

(defun parse-inteq ()
    (parse-decision-term 'INTEQ)
)

(defun parse-intless ()
    (parse-decision-term 'INTLESS)
)

(defun parse-decision-term (kind)
    (check$ TLparen 'decision)
    (Plet (left (parse$ 0))
        (check$ TScolon 'decision)
        (Plet (right (parse$ 0))
            (check$ TScolon 'decision)
            (Plet (if-term (parse$ 0))
                (check$ TScolon 'decision)
                (Plet (else-term (parse$ 0))
                    (check$ TRparen 'decision)
                    (decision-term
                        kind (yield) left right if-term else-term
                    )
                )
            )
        )
    )
)

(defun parse-bound-id-term (num-bound-ids)
    (open-action-stack)
    (Plet (bound-ids (list (check$ TId '|bound id|)))
        (<- num-bound-ids (1- num-bound-ids))
        (Ploop
            (while (> num-bound-ids 0))
            (do
                (check$ TComma '|bound id|)
                (<- bound-ids (cons (check$ TId '|bound id|) *-*))
	        (Pif (member (car bound-ids) (cdr bound-ids)) -->
		    (parse-error '|bound identifiers must be distinct|)
		 fi)
                (<- num-bound-ids (1- num-bound-ids))
            )
        )
        (check$ TPeriod '|bound id|)
        (Plet (body-of-term (parse$ 0))
            (prog1
                (bound-id-term
                    'BOUND-ID-TERM (yield) (nreverse bound-ids) body-of-term
                )
                (close-action-stack)
            )
        )
    )
)

(defun eat-token$ ()
    (flush-token-actions)
    (scan)
)

(defun check$ (type-needed term)
    (Pif (token-is$ type-needed) -->
        (Plet (val token-val)
            (eat-token$)
            val
        )

     || t -->
        (parse-error
            (concat
                '|expecting '| (sel delim-descr (type-needed))
                '|' in | term '| term.|
            )
        )
     fi)
)


;-- parse a declaration


(defun parse-declaration ()
    (open-action-stack)
    (<- parse-a-declaration$ 'yes)
    (Plet (term (parse$ 0))
        (<- parse-a-declaration$ 'no)
        (Pif (and (atom (car term)) (eql parse-a-declaration$ 'did-one)) -->
            (parse-error '|bad declaration|)

         || (atom (car term)) -->
            (declaration (yield) nil term)

         || t -->
            (yield)
            term

         fi)
    )                                    
)
   




(defun parse-tagged ()
    (let* ((tag (Pif (eql token-type TNbr)
		    --> token-val  ||
		    (eql token-type TStar)
		    --> 0  ||
		    t
		    --> (parse-error
			  '|missing "*" or number in tagged term.|) fi))
	   (term (progn
		   (eat-token$)
		   (check$ TScolon '|tagged|)
		   (parse$ 0))))
      (check$ TRsqrbrace '|tagged|)
      (check$ TRsqrbrace '|tagged|)
      (tagged-term 'TAGGED (yield) tag term)))














