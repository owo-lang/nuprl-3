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


;-- vi: set lisp ai :

;--       SCAN.L
;-- 
;-- The Lexical Scanner -- used by the Parser.
;--

;--
;-- Tokens returned:
;--
;--     TId                                for an identifier
;--                                          (letter followed by letters/digits)
;--     TNbr                               for a string of digits
;--     TUniv                              for U followed by a string of digits
;--     TEqual,TLess                       for  =,<
;--     TPsign,TQuotient,TArrow,TUnion     for # // => |
;--     TBslash                            for \
;--     TPlus, TMinus, TStar, TSlash, TDot for + - * / .
;--     TComma, TSColon, TColon            for , ; :
;--     TLparen, 
;--     TRparen, TLbrace, TRbrace          for ( ) { }
;--     TQuote                             for '
;--     TToken                             for a string of characters
;--                                            delimited by double quotes 
;--
;--

;--
;-- The token table:
;--
;--     token-type-of-char is a byte vector that maps characters to token types.
;--     E.g., (sel token-type-of-char (^|\+|)) is TPlus.  The digits 0-9
;--     all map to TNbr and that the alphabetic characters (a-z, A-Z, underscore,
;--     dollar sign, and at(@) sign) all map to TId.  The table is initialized
;--     by scan-table-init.  Note that this assumes that there are no more
;--     than 256 token types (since we use byte vectors).
;--
    (constant token-table-len 174)
    (Pdeftype token-table-type byte-vector (token-table-len))

    (global token-type-of-char token-table-type)

;--
;-- The globals used and set by the scanner.
;--

 (global curr-scan-char)      ;-- The character being scanned (i.e., the next
                              ;-- character to be parsed)

(defun CURR-CHAR$ () (implode (list curr-scan-char)))

(defun scan-table-init ()
    ;-- 
    ;-- Create a Ttree generator.
    ;--
        (TG-create)

    ;--
    ;-- Initialize the scanner tables: initialize the token-type table to map
    ;-- each possible input character to a token type.  Also, set the
    ;-- is-reserved-word property for each of the keywords 'mod, 'MOD, 'Mod,
    ;-- and so on: the property is set to the keyword's token type.  (TMod for
    ;-- the various spellings of 'mod', TIf for 'if', etc.)
    ;-- 

    (<- token-type-of-char (new token-table-type))
    (fillbyte-vector token-type-of-char 0 token-table-len TBADCHAR)

    (for (x in (list (list #.(ichar #\\) TBslash  ) (list #.(ichar #\:) TColon   )
                     (list #.(ichar #\,) TComma   ) (list #.(ichar #\") TDquote  ) 
                     (list #.(ichar #\=) TEqual   ) (list #.(ichar #\>) TGreater ) 
                     (list #.(ichar #\{) TLbrace  ) (list #.(ichar #\<) TLess    ) 
                     (list #.(ichar #\() TLparen  ) (list #.(ichar #\-) TMinus   ) 
                     (list #.(ichar #\|) TUnion   ) (list #.(ichar #\.) TPeriod  ) 
                     (list #.(ichar #\+) TPlus    ) (list #.(ichar #\#)  TPsign  ) 
                     (list #.(ichar #\') TQuote   ) (list #.(ichar #\}) TRbrace  ) 
                     (list #.(ichar #\)) TRparen  ) (list #.(ichar #\;) TScolon  )
                     (list #.(ichar #\!) TShriek  ) (list #.(ichar #\/) TSlash   )
                     (list #.(ichar #\*) TStar    ) (list #.(ichar #\`) TMlchar  )
                     (list #.(ichar #\[) TLsqrbrace) ;;;(list #.(ichar #\~) TTilda   )
                     (list #.(ichar #\]) TRsqrbrace)
         )     )
         (do (<- (sel token-type-of-char ((car x))) (cadr x)))
    )

    (for (i in '#.(istring "@_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"))
        (do (<- (sel token-type-of-char (i)) TId))
    )
    (for (i in *nonstandard-graphic-ichars*)
         (do (<- (sel token-type-of-char (i)) TId)))

    (for (i in '#.(istring "0123456789"))
        (do (<- (sel token-type-of-char (i)) TNbr))
    )
                                            
    (dcl-res-word TAny    '|any|   '|ANY|   '|Any|)
    (dcl-res-word TAt     '|at|    '|AT|    '|At|)
    (dcl-res-word TAxiom  '|axiom| '|AXIOM| '|Axiom|)
    (dcl-res-word TAtom   '|atom|  '|ATOM|  '|Atom|)
    (dcl-res-word TAtomeq '|atom_eq| '|ATOM_EQ| '|Atom_eq|)
    (dcl-res-word TDecide '|decide| '|DECIDE| '|Decide|)
    (dcl-res-word TFunction '|function| '|FUNCTION| '|Function|)
    (dcl-res-word TIn     '|in|    '|IN|    '|In|)
    (dcl-res-word TInd    '|ind|   '|IND|   '|Ind|)
    (dcl-res-word TInl    '|inl|   '|INL|   '|Inl|)
    (dcl-res-word TInr    '|inr|   '|INR|   '|Inr|)
    (dcl-res-word TInt    '|int|   '|INT|   '|Int|)     
    (dcl-res-word TInteq  '|int_eq|   '|INT_EQ| '|Int_eq|)
    (dcl-res-word TLeft   '|left|  '|LEFT|  '|Left|)
    (dcl-res-word TIntless '|less|  '|LESS|  '|Less|)
    (dcl-res-word TList-ind '|list_ind|  '|LIST_IND|  '|List_ind|)
    (dcl-res-word TList   '|list|  '|LIST|  '|List|)
    (dcl-res-word TMod    '|mod|   '|MOD|   '|Mod|) 
    (dcl-res-word TNew    '|new|   '|NEW|   '|New|)
    (dcl-res-word TNil    '|nil|   '|NIL|   '|Nil|)
    (dcl-res-word TOver   '|over|  '|OVER|  '|Over|)
    (dcl-res-word TProduct '|product| '|PRODUCT| '|Product|)
    (dcl-res-word TQuotient '|quotient| '|QUOTIENT| '|Quotient|)
    (dcl-res-word TRight  '|right| '|RIGHT| '|Right|)
    (dcl-res-word TSpread '|spread| '|SPREAD| '|Spread|)
    (dcl-res-word TSet    '|set|   '|SET|   '|Set|)
    (dcl-res-word TTofTh  '|term_of| '|TERM_OF| '|Term_of|)
    (dcl-res-word TUnion  '|union| '|UNION| '|Union|)
    (dcl-res-word TUniverse '|universe| '|UNIVERSE| '|Universe|)
    (dcl-res-word TUsing  '|using| '|USING| '|Using|)
    (dcl-res-word TVoid   '|void|  '|VOID|  '|Void|)
    (dcl-res-word TRec-ind '|rec_ind|  '|REC_IND|  '|Rec_ind|)
    (dcl-res-word TFix    '|fix|   '|FIX|   '|Fix|)
    (dcl-res-word TRec    '|rec|   '|REC|   '|Rec|)
    (dcl-res-word TDom    '|dom|   '|DOM|   '|Dom|)
    (dcl-res-word TLet    '|let|   '|LET|   '|Let|)
    (dcl-res-word TObject '|object| '|OBJECT| '|Object|)

    t
)

(defun dcl-res-word (tval spelling1 spelling2 spelling3)
    ;--
    ;-- Declare a reserved word: its token value will be tval, and it can
    ;-- be spelled three different ways.
    ;--
    ;-- Example: (dcl-res-word TIf 'if 'IF 'If)
    ;--
    ;--     will declare three spellings for the token TIf.
    ;--

    (setf (get spelling1 'is-reserved-word) tval)
    (setf (get spelling2 'is-reserved-word) tval)
    (setf (get spelling3 'is-reserved-word) tval)

    (<- token-val nil)

)

(defun scan-init (Ttree)
    ;-- Initialize things and return the list of def's referenced at the top
    ;-- level of this Ttree.

    ;-- Set up the Ttree generator so that it will generate the characters of
    ;-- given Ttree.
        (TG-init Ttree)

    ;-- Arrange for characters to be remembered for best Ttree computation.
        (activate-action-buffer)

    ;-- Initialize for the first call to scan by getting the first character
    ;-- and skipping over white space.
        (get-scan-char$)
        (skip-whitespace$)

    (referenced-defs Ttree)
)

(defun scan ()
    ;-- 
    ;-- Returns the type of the next token.
    ;-- As a side effect, token-type is set to that value, and if appropriate
    ;-- token-val is set to the value for the token else it is left nil.
    
    (<- token-val nil)

    ;-- It is assumed that the first character of the current token (i.e. the
    ;-- one whose type will be returned from this call) has been read and 
    ;-- is in curr-scan-char.

    ;-- Forget the actions for the previous token.  This is needed for the
    ;-- routines which use the scanner for purposes other than parsing terms
    ;-- and thus do not call flush-token-actions.
        (forget-previous-token-actions)

    ;-- Associate all left over white space characters and the first
    ;-- character of the current token with the current token.
        (add-all-to-token-actions)

    (scan-next-token)
    
    ;-- Make sure there is a non white space character in curr-scan-char,
    ;-- and associate the appropriate white space actions with this token.
        (skip-whitespace$)
        (add-white-space-to-token-actions)

    token-type

)

(defun scan-next-token ()
    ;--
    ;-- Scan for the next token, placing its type in token-type and its
    ;-- value in token-val.  Return the token type.
    ;--

    (Pif (null curr-scan-char) -->
        (<- token-type TEndInput)

     || t -->

        (<- token-type (sel token-type-of-char (curr-scan-char)))
        (<- token-type (check-token))

     fi)

)


(defun skip-whitespace$ ()
    (Ploop
        (while (member curr-scan-char white-space))
        (do
            (get-scan-char$)
        )
    )
)

(defun check-token ()
    ;--
    ;-- Check the token type; if necessary, change it to take into
    ;-- consideration the use of double quotes.  Return the token
    ;-- type.  Also has to worry about 2 character tokens.
    ;--
    ;-- Note:
    ;--     " is used in pairs to mark a string.  To get a double quote as
    ;--     part of a string, use !", as in "abc!"def", a 7 character string.
    ;--     A string indicates a list of integers, where the first integer is
    ;--     the ascii value of the first character, and so on.
    ;--

     (Pif (token-is$ TDquote) -->
         (scan-token$)

     || (token-is$ TId ) -->
        (scan-id$)    

     || (token-is$ TNbr) --> 
        (scan-nbr$)

     || (token-is$ TMinus) -->
        (Pif (equal (get-scan-char$) #.(ichar #\>)) -->
            (add-all-to-token-actions)
            (get-scan-char$)
            TArrow

         || t -->
            TMinus

         fi)

     || (token-is$ TLsqrbrace) -->
        (Pif (equal (get-scan-char$) #.(ichar #\[)) -->
            (add-all-to-token-actions)
            (get-scan-char$)
            TDblLsqrbrace

         || t -->
            TLsqrbrace

         fi)


     || (token-is$ TPlus) -->
        (Pif (equal (get-scan-char$) #.(ichar #\>)) -->
	    (add-all-to-token-actions)
	    (get-scan-char$)
	    TParFunArrow

	 || t -->
	    TPlus
	
	 fi)

     || (token-is$ TSlash) -->
        (Pif (equal (get-scan-char$) #.(ichar #\/)) -->
            (add-all-to-token-actions)
            (get-scan-char$)
            TQuot

         || t -->
            TSlash

         fi)

     || (token-is$ TBADCHAR) -->
        (throw 'process-err
               (list 'ERR
                     (concat '|illegal character "|
                             (CURR-CHAR$)
                             '|".|
                     )
               )
        )

     || t -->
        (get-scan-char$)
        token-type

     fi)
)

(defun scan-token$ ()
    ;-- 
    ;-- Scan a token.
    ;--
    (<- token-val
        (multiple-value-bind
            (next-char was-escaped) (get-scan-char$)
            (Ploop
                (local chars nil)
                (while (and next-char (or (not (= next-char #.(ichar #\"))) was-escaped)))
                (do
                    (add-all-to-token-actions)
                    (<- chars (cons next-char chars))
                    (multiple-value-setq (next-char was-escaped) (get-scan-char$))
                )
                (result
		    (Pif (not next-char) -->
			(scan-error "Premature eof after " (implode (nreverse chars)))
		     || t -->
			(nreverse chars)
		     fi)
		)
            )
        )
    )
    
    ;-- skip over the closing double quote
        (add-all-to-token-actions)
        (get-scan-char$)

    TToken
)

(constant id-chars (list TId TNbr))

(defun scan-id$ ()
    ;--
    ;-- Scan an identifier or keyword.  To distinguish a keyword from an
    ;-- identifier, we look at the is-reserved-word property of the atoms 'ALL',
    ;-- 'all', 'All', 'SOME', 'some', etc.  If the property is non-nil, then it
    ;-- is the token type of the keyword.  Return the token-type.
    ;--

    (Plet (chars      nil   ;-- the chars of the identifier, in reverse order
          res-word   nil   ;-- the is-reserved-word property of the identifier
         )

         (<- chars  (list curr-scan-char))
         (Ploop (while
                   (member (get-scan-char-and-yield-type$) id-chars)
               )
               (do
                   (add-all-to-token-actions)
                   (<- chars  (cons curr-scan-char chars))
               )
         )

         ;-- Make the order of characters in chars be "correct".
             (<- chars (nreverse chars))
         
         (Pif (and (= (car chars) #.(ichar #\U))
                  (all-nums$ (cdr chars))
             ) -->
             (<- token-val (get-value-from-chars (cdr chars)))
             (<- token-type TUniv)

          || t -->
             (<- token-val (implode chars))
             (<- res-word (get token-val 'is-reserved-word))
             (Pif (not (eql res-word nil)) --> 
                 (<- token-type res-word)
              fi)
          fi)

         token-type
     )
)

(defun all-nums$ (char-list)
    (and
        (not (null char-list))
        (Pevery #'(lambda (x) (= (sel token-type-of-char (x)) TNbr)) char-list)
    )
)

(defun get-value-from-chars (char-list)
    (Ploop
        (local l     char-list
               value 0
        )
        (while (not (null l)))
        (do
            (<- value (+ (* value 10) (- (car l) #.(ichar #\0))))
            (<- l (cdr l))
        )
        (result value)
    )
)

(defun scan-nbr$ ()
    ;--
    ;-- Scan a number.  Set token-val to the value of the number and return TNbr.
    ;--

    (<- token-val (- curr-scan-char #.(ichar #\0)))
    (Ploop 
        (while (= (get-scan-char-and-yield-type$) TNbr))
        (do
            (add-all-to-token-actions)
            (<- token-val
                (+ (* token-val 10) (- curr-scan-char #.(ichar #\0)))
            )
        )
    )

    TNbr
)


;--
;-- Scan the next character and yield its type.
;-- Pif the end of the chars is reached then yield TEndInput.
;--

(defun get-scan-char-and-yield-type$ ()

    (Plet (ch (get-scan-char$))
         (Pif (null ch) --> TEndInput 
          || t --> (sel token-type-of-char (ch))
          fi)
    )
)

(defun get-scan-char$ ()
    ;-- 
    ;-- Set curr-scan-char to the next character from the Ttree and return
    ;-- it.  One exception is when the next character is !, the escape
    ;-- character.  In this case the following character is unconditionally 
    ;-- returned.
    ;-- 
    
    (Plet (was-escaped nil)
        (<- curr-scan-char (TG-next-char))
        (Pif  (and curr-scan-char (= curr-scan-char #.(ichar #\!))) -->
               (<- curr-scan-char (TG-next-char))
               (<- was-escaped t) 
         fi)
        (values curr-scan-char was-escaped)
    )
)


(defun referenced-defs (Ttree)
    ;-- Returns a list of the definitions referenced at the top level of
    ;-- the given Ttree.
    (for (x in (cdr Ttree))
        (when (listp x))
        (save (car x))
    )
)

(defun scan-error (txt1 txt2)
    (throw 'process-err (list 'ERR (concat txt1 txt2))))

;--
;-- ml-prl scanner interface.
;--
;-- The interface is defined by the functions prl-scanner-initialize,
;-- prl-scanner-get-char and prl-parse-term.  ML calls
;-- prl-scanner-initialize with a Ttree argument to set things up.   The
;-- function prl-scanner-get-char returns the next character that ML should
;-- see, performing some conversions along the way.  The function
;-- prl-parse-term is called when ML sees an ml-quote-char (ie ').  It
;-- returns the result of parsing from the "current" position in the Ttree.
;-- 

(global ml-peek-char$)             ;-- If non nil, a character that should
                                   ;-- be seen by the ml scanner the next
                                   ;-- time prl-scanner-get-char is called.

(global ml-quote-flag$)            ;-- If non nil, indicates that an ml
                                   ;-- quote character should be returned by
                                   ;-- prl-scanner-get-char the next time
                                   ;-- this is called.  This takes
                                   ;-- precedence over ml-peek-char$.

;--  prl-scanner-initialize (ttree : a Ttree)
;--
;-- Initialize state variables and set the Ttree generator to generate the
;-- given Ttree.
;-- 
(defun prl-scanner-initialize (ttree)

    ;-- Since prl isn't doing the scanning, forget-previous-token-actions
    ;-- isn't being called, and if we don't shut off the action-buffer it will
    ;-- grow unnecessarily.
        (deactivate-action-buffer)

    (<- ml-quote-flag$ nil)
    (<- ml-peek-char$ nil)

    ;-- Set up the generator to give the characters of the given ttree.
    (TG-init ttree)

)

;-- prl-scanner-get-char
;--
;-- Return the next character that the ml scanner should see.
;-- 
(defun prl-scanner-get-char ()
           
    (Pif ml-quote-flag$ -->
        ;-- We skipped over an ml quote character.  Let ml see it.
        (<- ml-quote-flag$ nil)
        '|'|

     || ml-peek-char$ -->
        ;-- This is a character that was read by the prl scanner but which
        ;-- should be seen by the ml scanner.
        (prog1
            ml-peek-char$
            (<- ml-peek-char$ nil)
        )

     || t -->
        ;-- There are no saved characters, so just read the next character.
        (convert-prl-char-to-ml-char (get-scan-char$))

     fi)
)

;-- prl-parse-term
;--
;-- When this routine is called, ml must not have read anything past the ml
;-- quote character.  
;-- 
;-- attempt to parse a prl term
;-- if a successful parse is done, check to see if the first token following
;--    the last one included in the parsed item is a single quote (TQuote).
;--    if it is not, return (FAILURE . message)
;--    if it is , return (TERM . term) 
;-- if the parse attempt fails, return (FAILURE . message)
;--
;-- Upon leaving this routine the scanner, as ml views it, will be positioned
;-- just before the first ml quote character following the parsed item.
;-- I.e. the next call to prl-scanner-get-char will return the ml quote character
;-- (or nil if no ml quote was found after the parsed item).  Intervening
;-- white space characters between the ml quote character and the next non
;-- white space character will be lost.
;-- 

(defun prl-parse-term ()

    ;-- Set things up so that characters making up the tokens are
    ;-- remembered for the best Ttree computation.
    (activate-action-buffer)

    ;-- Initialize for the scanner by getting the first non white space
    ;-- character of the input.
    (get-scan-char$)
    (skip-whitespace$)

    ;-- Initialize for the parser by getting the first token.
    (scan)

    (Plet (result (catch 'process-err (parse-from-current-Ttree)))

        ;-- Stop remembering characters.
        (deactivate-action-buffer)
        
        (Pif (and (listp result) (eql 'ERR (car result))) -->
            ;-- The parse failed.  Return an indicator and the error message.
            (<- result (cons 'FAILURE (cadr result)))

         || (not (token-is$ TQuote)) -->
            ;-- The parse succeeded, but there is no ml quote directly after
            ;-- the term.
            (<- result (cons 'FAILURE '|closing term quote expected|))

         || t -->
            ;-- The parse succeeded and there was an ml quote directly
            ;-- following the term.  Return the result with a success
            ;-- indicator.
            (<- result (cons 'TERM result))

         fi)

        ;-- Make sure that the next thing ML will see is an ml quote
        ;-- character.
        (scan-up-to-closing-ml-quote$)

        ;-- At this point, the scanner has already read the first non white
        ;-- space character after the quote, so we save it in order that ml will
        ;-- see it.
        (<- ml-peek-char$ (convert-prl-char-to-ml-char curr-scan-char))

        result
    )
)       

(defun scan-up-to-closing-ml-quote$ ()
    ;-- Find an ml quote character (or end of input).
    (Ploop 
        (while (not (or (token-is$ TQuote) (token-is$ TEndInput))))
        (do
            (Plet (caught (catch 'process-err (scan)))
                (Pif (listp caught) -->  ;-- must be an error (bad scan char)
                    (get-scan-char$)
                 fi)
            )
        )
    )
    (Pif (token-is$ TQuote) -->  (<- ml-quote-flag$ t) fi)
)

(defun convert-prl-char-to-ml-char (char)
    ;-- ML wants to see Line Feeds, not New Lines.  Also, ML wants to see
    ;-- PRL-SCANNER-EOF-CHAR on end of input.
    (Pif (null char) --> 'PRL-SCANNER-EOF-CHAR
     || (= char NL) --> (implode (list LF))
     || t           --> (implode (list char))
     fi)
)
