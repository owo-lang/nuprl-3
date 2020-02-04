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

;-- (module defn)

;--
;-- Parser for template definitions.
;--
;--     Defn   ::= Lhs '==' Rhs
;--     Lhs    ::= Text { Formal Text } *
;--     Text   ::= zero or more chars, none of which is an unescaped "<".
;--     Formal ::= '<' Blanks Id Blanks { ':' Descr } '>'
;--     Blanks ::= { ' ' } *
;--     Descr  ::= zero or more chars, none of which is an unescaped ">".
;--     Rhs    ::= a Ttree
;--
;-- For a description of the metasyntax, see the term/formula parser.
;-- The escape character is the backslash, "\".
;--

    (global PRL-obj$ object)              ;-- the PRL object being checked.
    (global defn$    definition-object)   ;-- the new value of the PRL object.

    (global body$         )   ;-- body of template passed to parse-defn
    (global lhs$          )   ;-- left hand side of definition.
    (global rhs$          )   ;-- right hand side of definition.
    (global lhs-texts$    )   ;-- list of left hand side texts.
    (global lhs-formals$  )   ;-- list of left hand side formals.
    (global nbr-formals$  )   ;-- number of left hand side formals.
    (global formal-ids$   )   ;-- list of imploded formal ids.

    (global lhs-scan-chars$)   ;-- holds object to be scanned.
    (global curr-lhs-char$ )   ;-- the current lhs scan character
                               ;-- (nil if we're at the end of the scan).

    (global curr-lhs-char-was-escaped$)   ;-- true iff the current scan
                                          ;-- character was escaped.

(defun parse-defn (name)
    ;--
    ;-- Update the named PRL object and the definition object it contains.
    ;-- We parse the definition object's body as a template definition,
    ;--
    ;--     Defn ::= Lhs '==' Rhs
    ;--
    ;-- set the PRL object's status to COMPLETE, and return a list of the
    ;-- referenced objects, in the form (REFERENCED <obj> <obj> ...).
    ;--
    ;-- If the parse fails, return (ERR ... an explanation ...) and set
    ;-- the PRL object's status to BAD.
    ;--
    ;-- Note that the parse assumes the definition's "==" occurs as two
    ;-- adjacent unescaped characters at the top level of the Ttree.
    ;--

    (catch 'process-err

           (progn
	        ;-- This is here because of an optimization in ttree-gen.
	        ;-- A list of the formal names of a def is stored on the
	        ;-- property list of its name.
	            (<- (get name 'formal-names) nil)
                (<- body$ (body-of-obj$ name))
                (parse-defn$ body$)
                (check-lhs$)
                (check-rhs-formals$ rhs$)
                (build-defn$ name)
                (set-object-status name 'COMPLETE)

                (check-rhs-defs$ body$)
           )
)   )

(defun body-of-obj$ (name)
    ;--
    ;-- We are given the name of the PRL (defn) object; set the object's
    ;-- status to BAD and return the Ttree body of the object.
    ;--

    (Plet (defn nil)   ;-- the definition subobject holding the Ttree to return.

         (<- PRL-obj$ (is-lib-member name))

         (Derr-if$ name 7 (null PRL-obj$))

         (Derr-if$ name 8 (not (eql (sel PRL-obj$ kind) 'DEF)))
         (Derr-if$ name 9 (not (lib-member name)))

         (set-object-status name 'BAD)

         (<- defn (sel PRL-obj$ value))

         (<- (sel (definition-object defn) rhs) nil)

         (sel (definition-object defn) body)
)   )

(defun parse-defn$ (template)
    ;--
    ;-- Parse Defn ::= Lhs '==' Rhs.  Set up the globals used by check-formals$
    ;-- and build-defn$ to inspect the definition and build the defn object.
    ;-- Note the '==' must be two adjacent unescaped characters at the top
    ;-- level of the template.
    ;--

    (Plet (formals nil    ;-- reverse of the list of formals found.
          texts   nil    ;-- reverse of the list of lhs texts found.
          lhs     nil    ;-- reverse of the left hand side found.
          lhs-char nil   ;-- current lhs char (during search for '=='.
         )

         (Ploop (until (or (null template)
                          (equal '#.(istring "==") (list (car template) (cadr template)))
               )      )

               (do (<- lhs-char (car template))
                   (<- lhs      (cons lhs-char *-*))

                   (Pif (equal lhs-char #.(ichar #\\)) -->
                       
                       (<- template (cdr *-*))
                       (<- lhs-char (car template))
                       (<- lhs      (cons lhs-char *-*))
                    fi)

                   (<- template (cdr *-*))
         )     )

         (Derr-if$ () 1 (null template))

         (<- lhs$ (reverse lhs))
         (<- rhs$ (normal-Ttree (cons 'Ttree (cddr template))))

         (init-lhs-scan$ lhs$)

         (<- formals  (ncons '( nil nil )))   ;-- zeroth formal is always (nil nil).
         (<- texts     (list (scan$ 'lbracket$)))

         (<- nbr-formals$ 0)

         (Ploop (while lhs-scan-chars$)

               (do (<- formals (cons (scan-formal$)  *-*))
                   (<- texts   (cons (scan$ 'lbracket$) *-*))

                   (<- nbr-formals$  (1+ *-*))
         )     )

         (<- lhs-formals$ (nreverse formals))
         (<- lhs-texts$   (nreverse texts))

         (<- formal-ids$ (mapcar #'(lambda (x) (implode (car x))) lhs-formals$))
)   )

(defun init-lhs-scan$ (Ttree)
    ;--
    ;-- Initialize the lhs's scan by setting lhs-scan-chars$ to its gen.
    ;-- To generate the lhs of a template definition, drop the 'Ttree from the
    ;-- head of the lhs and replace each def ref by the splice of its gen. 
    ;-- Do not (repeat: do NOT) run through the lhs looking for '#.(istring "<id>").
    ;-- That is, ignore the character sequences that in a regular gen-Ttree
    ;-- are intepreted (via normal-Ttree) as a reference to a formal.
    ;--

    (<- lhs-scan-chars$ (flatten-chars-and-refs$ (cdr Ttree)))

    (scan-lhs-char$)
)

(defun flatten-chars-and-refs$ (x)
    ;--
    ;-- We take a list of characters and def refs, replace the def refs by
    ;-- their gen, and (conceptually) splice together the result.
    ;--

    (Plet (first-of-x      nil   ;-- first character or def ref of x.
          flatten-of-rest nil   ;-- result of flattening rest of x.
         )

         (Pif (null x) --> nil
          || t -->

             (<- first-of-x (car x))
             (<- flatten-of-rest (flatten-chars-and-refs$ (cdr x)))

             (Pif (atom first-of-x) --> (cons first-of-x flatten-of-rest)

              || t --> (append (gen-Ttree `(Ttree ,first-of-x)) flatten-of-rest)

              fi)
          fi)
)   )

;--
;-- Below: The routines that generate and expand Ttrees.
;--

(defun gen-Ttree (Ttree)
    ;--
    ;-- Given a Ttree, apply all its template and formal variable references
    ;-- and return the result, a list of fixnum chars.  We call gen-Ttree$ on
    ;-- the normal form of the Ttree, with the empty environment.  The env
    ;-- will associate formals with their actuals.
    ;--

    (gen-Ttree$ Ttree '(nil nil))

)

(defun gen-Ttree$ (Ttree env)
    ;--
    ;-- Given a normal form Ttree and an environment, apply all its template
    ;-- and formal variable references and return the result.
    ;--

    (for (x in (cdr Ttree))

         (splice

             (Pif (is-formal-ref$ x) --> (gen-formal-ref$ x env)
              || (is-defn-ref$   x) --> (gen-defn-ref$   x env)
              || (equal x NL      ) --> nil
              || t                  --> (list x)
              fi)
)   )    )

(defun gen-formal-ref$ (fref env)
    ;--
    ;-- Given a formal reference, fref, return the result of gen'g the actual
    ;-- to which it is bound in the current environment.
    ;--
    ;-- An environment is either nil or has the form (cons env assoc-list),
    ;-- say
    ;--
    ;--     (env' ( -(id expr)- ))
    ;--
    ;-- where the value of id is the value of expr in env'.
    ;--

    (Plet (formalid (cadr fref)   ;-- the formal's identifier.
          id.act nil             ;-- formal id dot its actual value in env.
         )

         (<- id.act (assoc formalid (cadr env)))

         (Terr-if$ formalid 3 (null id.act))

         (gen-Ttree$ (cdr id.act) (car env))
)   )

(defun gen-defn-ref$ (defn-ref env)
    ;--
    ;-- Given a definition reference, return the result of gen'g its right
    ;-- hand side in the new environment, which is an environment in which
    ;-- the formals for the template are bound to the actuals mentioned in
    ;-- the reference.
    ;--

    (Plet (defn-name (car defn-ref)   ;-- the name of the template being ref'd.
          act-list  (cdr defn-ref)   ;-- the actuals being supplied.
          alist     nil              ;-- the assoc list part of the new env.
         )

         (<- alist (build-alist$ defn-name act-list))

         (gen-Ttree$ (apply-defn defn-name) (list env alist))
)   )

(defun scan$ (fcn)
    ;--
    ;-- Scan a token from the front of lhs-scan-chars$.  The token we want is
    ;-- the shortest one such that
    ;--
    ;--     1.  We're at the end of the scan (i.e., curr-lhs-char$ = nil) or
    ;--     2.  (funcall fcn) is true.
    ;--
    ;-- The token will be a list of zero or more logical char, where
    ;-- "logical" char means that any backslashed char (i.e., any escaped
    ;-- char) will have its backslash removed.
    ;--
  
    (Plet (rtoken nil)   ;-- the reverse of the token to be returned.

         (Ploop (until (or (null curr-lhs-char$) (funcall fcn)))

               (do (<- rtoken (cons curr-lhs-char$ *-*))
                   (scan-lhs-char$)
         )     )

         (reverse rtoken)
)   )

(defun scan-lhs-char$ ()
    ;--
    ;-- Get the new current lhs scan character from the head of lhs-scan-char$.
    ;-- The new current char the 1st char of lhs-scan-char$ if that 1st char isn't
    ;-- a backslash; it's the 2nd char of lhs-scan-char$ otherwise.
    ;-- (We set curr-lhs-char-was-escaped$ accordingly.)
    ;--
    ;-- The scanned char(s) are removed from lhs-scan-char$.
    ;--

    (<- curr-lhs-char$ (car lhs-scan-chars$))
    (<- lhs-scan-chars$ (cdr *-*))

    (<- curr-lhs-char-was-escaped$ (equal #.(ichar #\\) curr-lhs-char$))

    (Pif curr-lhs-char-was-escaped$ -->

        (<- curr-lhs-char$  (car lhs-scan-chars$))
        (<- lhs-scan-chars$ (cdr lhs-scan-chars$))

     fi)

    curr-lhs-char$
)

(defun scan-formal$ ()
    ;--
    ;-- Parse Formal ::= '<' Blanks Id Blanks { ':' Descr } '>' and
    ;-- return the list ( id descr ).
    ;--

    (Plet (id     nil   ;-- identifier  of the formal.
          descr  nil   ;-- description of the formal.
         )

         (Derr-if$ () 2 (not (lbracket$)))
         (scan-lhs-char$)

         (scan$ 'not-blank$)

         (Derr-if$ () 3 (not-alphabetic$))
         (<- id (scan$ 'not-id$))

         (scan$ 'not-blank$)

         (Pif (equal curr-lhs-char$ #.(ichar #\:)) -->
             (scan-lhs-char$)
             (<- descr (scan$ 'rbracket$))
         fi)

         (Derr-if$ (implode id) 4 (not (rbracket$)))
         (scan-lhs-char$)

         (list id descr)
)   )

(defun check-lhs$ ()
    ;--
    ;-- Make sure that no identifier appears more than once in lhs-formals$.
    ;--

    (Plet (ids (mapcar 'car lhs-formals$))   ;-- the list of lhs identifiers.

         (Ploop (while ids)

               (do (Derr-if$ (car ids) 5 (member (car ids) (cdr ids)))

                   (<- ids (cdr *-*))
)   )    )     )

(defun check-rhs-formals$ (Ttree)
    ;--
    ;-- Make sure the Ttree's formals are all members of formal-ids$.  That
    ;-- is, make sure they were declared on the left hand side of the
    ;-- definition.  The Ttree is assumed to be a normal Ttree.
    ;--

    (Plet (form   nil   ;-- formal being referenced.
         )

         (for (elt in (cdr Ttree))

              (when (and (consp elt) (eql (car elt) 'FORMAL)))

              (do   (<- form (cadr elt))
                    (Derr-if$ form 6 (not (member form formal-ids$)))
)   )    )    )

(defun check-rhs-defs$ (Ttree)
    ;--
    ;-- Verify that all objects referenced in the Ttree are complete
    ;-- and in the library.
    ;--
    ;-- Return (REFERENCED - the objects referenced in the Ttree - )
    ;--

    (Plet (refd-defs nil   ;-- the objects referenced in the Ttree.
          bad-obj   nil   ;-- name of the first object in refd-defs that
                          ;-- isn't COMPLETE or isn't in the library.
         )

         (<- refd-defs (refd-defs-of-Ttree Ttree))

         (<- bad-obj (some-obj-not-complete refd-defs))

         (Derr-if$ bad-obj 10 bad-obj)

         (cons 'REFERENCED refd-defs)
)   )

(defun build-defn$ (name)
  (declare (ignore name))
    ;--
    ;-- Using the globals built by parse-defn$, create a definition object
    ;-- defn$ and insert the various globals into its fields.  Make defn$
    ;-- the value of the PRL object and return defn$.
    ;--

    (Plet (formals lhs-formals$   ;-- list of formals.
          texts   lhs-texts$     ;-- list of texts.
         )

         (<- num-formals nbr-formals$)
         (<- defn$ (new definition-object))

         (<- (sel defn$ body       ) body$)
         (<- (sel defn$ num-formals) nbr-formals$)
         (<- (sel defn$ rhs        ) rhs$)

         (Ploop (local i 0)
               (until (> i nbr-formals$))

               (do (<- (sel defn$ lhs-text (i)) (car texts))

                   (<- (sel defn$ formal (i) name) (caar formals))
                   (<- (sel defn$ formal (i) descriptor) (cadar formals))

                   (<- texts   (cdr *-*))
                   (<- formals (cdr *-*))

                   (<- i (1+ i))
         )     )

         (<- (sel PRL-obj$ value ) defn$)
)   )

;--
;-- The functions below are used to delimit the scanning.
;--

(defun lbracket$ ()
    (and (not curr-lhs-char-was-escaped$) (equal #.(ichar #\<) curr-lhs-char$))
)

(defun rbracket$ ()
    (and (not curr-lhs-char-was-escaped$) (equal #.(ichar #\>) curr-lhs-char$))
)

(defun not-blank$ ()
    (not (equal #.(ichar #\space) curr-lhs-char$))
)

(constant alpha$ '#.(istring "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"))
(constant num$   '#.(istring "_0123456789"))

(defun not-alphabetic$ ()
    (not (member curr-lhs-char$ alpha$))
)

(defun not-id$ ()
    (and (not (member curr-lhs-char$ num$))
         (not (member curr-lhs-char$ alpha$))
)   )

(constant alphanumeric$
    '#.(istring "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_0123456789#")
)

;--
;-- Support routines for Ttrees and complete PRL objects.
;--

(defun normal-Ttree (Ttree)
    ;--
    ;-- A normal form Ttree is a list of fixnum chars, definition references,
    ;-- and formal references, where a formal ref is `(FORMAL id).  The input
    ;-- Ttree is a list of fixnum chars, definition references, and formal
    ;-- references.  (Note that formal refs are spliced in as '#.(istring "<id>").)
    ;--

    (Plet (item (car Ttree)   ;-- first item of Ttree.
          rest (cdr Ttree)   ;-- rest of Ttree.
         )

         (Pif (null Ttree)      --> nil
          || (consp item)      --> (cons (normal-ref$ item) (normal-Ttree rest))
          || (equal item #.(ichar #\<)) --> (normal-formal-ref$ Ttree)

          || (equal item #.(ichar #\\)) -->

             (Pif (null (car rest)) --> '#.(istring "\\")

              || (atom (car rest)) -->
                 (cons #.(ichar #\\) (cons (car rest) (normal-Ttree (cdr rest))))

              || t                 --> (cons item (normal-Ttree rest))

              fi)

          || t --> (cons item (normal-Ttree rest))
          fi)
)   )

(defun normal-ref$ (defn-ref)
    ;--
    ;-- To normalize a definition reference (name a b ... c), we
    ;-- normalize its actuals and return (name A B ... C), where
    ;-- A is the normal form of a, B of b, and so on.
    ;--

    (cons (car defn-ref) (mapcar 'normal-Ttree (cdr defn-ref)))

)

(defun normal-formal-ref$ (Ttree)
    ;--
    ;-- The given Ttree begins with a #.(ichar #\<); if it begins 
    ;-- with '#.(istring "<id>"), we scan
    ;-- that sublist into a formal ref `(FORMAL id); if not, the '#.(istring "<" is
    ;-- returned as a regular character.  In either case, we normalize the rest
    ;-- of the tree and return the concatenation.
    ;--
    ;-- Here, an id is an alphabetic character optionally followed by some
    ;-- alphanumeric characters.
    ;--

    (Plet (id.tree   nil   ;-- the id dot the rest of tree.
          id        nil   ;-- the id, if any, else nil.
          rem-tree  nil   ;-- the remainder of the tree, if any.
         )

         (<- id.tree (leading-formal-ref$ Ttree))

         (<- id       (car id.tree))
         (<- rem-tree (cdr id.tree))

         (Pif (null id) -->
             (cons #.(ichar #\<) (normal-Ttree (cdr Ttree)))
          || t -->
             (cons (list 'FORMAL (implode id)) (normal-Ttree rem-tree))
          fi)
)   )

(defun leading-formal-ref$ (Ttree)
    ;--
    ;-- The given Ttree begins with a #.(ichar #\<); if there is a 
    ;-- matching #.(ichar #\>), we
    ;-- set id to the sublist between the < ... > and return
    ;-- (cons id rest-of-Ttree), otherwise we return (cons nil Ttree).
    ;--

    (Plet (char   nil     ;-- the current character.
          rev-id nil     ;-- the reverse of the id to return, if any (else nil).
          id     nil     ;-- the id to return, if any (else nil).
          orig   Ttree   ;-- the original value of Ttree.
         )

         (Ploop (do (<- Ttree (cdr Ttree))
                   (<- char  (car Ttree))
               )
               (until (or (null char) (equal char #.(ichar #\>))))
               (do (<- rev-id (cons char *-*)))
         )

         (<- id (nreverse rev-id))
             
         (Pif (null char)        --> (cons nil orig)
          || (is-formal-id$ id) --> (cons id (cdr Ttree))
          || t                  --> (cons nil orig)
          fi)
)   )

(defun is-formal-id$ (x)
    ;--
    ;-- Return true iff x is a formal identifier: it must be at least one
    ;-- character long, an alphabetic char followed by zero or more alphanumerics.
    ;--

    (Pif (null x)                      --> nil
     || (not (member (car x) alpha$)) --> nil

     || (not (all-alphanumerics$ (cdr x))) --> nil 

     || t --> t
     fi)
)

(defun all-alphanumerics$ (chars)
    (Ploop
      (local answer t)
      (while (and answer (not (null chars))))
      (do
	(<- answer (member (car chars) alphanumeric$))
	(<- chars (cdr chars))
      )
      (result answer)
    )
)

(defun refd-defs-of-Ttree (Ttree)
    ;--
    ;-- Return a list of the names of the (definition) PRL objects referenced
    ;-- in the Ttree.  Make sure that no object name appears twice in the list.
    ;--

    (Plet (result   nil   ;-- the list to be returned.
          item     nil   ;-- the current item in the Ttree.
          sub-item nil   ;-- the current Ttree in the defn ref.
          obj-name nil   ;-- the name of the definition currently being ref'd.
         )

         (for (item in Ttree)

              (do (Pif (and (consp item) (not (eql 'FORMAL (car item)))) -->

                      (<- obj-name (car item))

                      (Pif (and obj-name (not (member obj-name result))) -->

                          (<- result (cons obj-name result))

                       fi)

                      (for (sub-item in (cdr item))

                           (do (<- result (append
                                               (refd-defs-of-Ttree sub-item)
                                               result
                      )    )   )          )

                   fi)
         )    )

         result
)   )

(defun some-obj-not-complete (obj-list)
    ;--
    ;-- If some object in the list is not (COMPLETE and in the library), return
    ;-- the name of the first such object, otherwise return nil.
    ;--
    
    (Ploop
      (local answer nil)
      (while (and (null answer) (not (null obj-list))))
      (do
	(<- answer (obj-not-complete (car obj-list)))
	(<- obj-list (cdr obj-list))
      )
      (result answer)
    )

)

(defun obj-not-complete (obj-name)
    ;--
    ;-- Return the name of the object if it is not COMPLETE or not in the
    ;-- library.  Return nil if it is both COMPLETE and in the library.
    ;--

    (Plet (obj  nil   ;-- the PRL object named, if any.  (Else nil.)
          name nil   ;-- the name to return, if any.
         )

         (<- obj  (Prl-OBJ obj-name))
         ;???(<- name (list 'quote obj-name))
	 (<- name obj-name)

         (Pif (null obj) --> name

          || (not (lib-member obj-name)) --> name

          || (not (eql (sel (object obj) status) 'COMPLETE)) --> name

          || t --> nil

          fi)
)   )

(defun complete-object (obj-name)
    ;--
    ;-- Return t if the object is COMPLETE and in the library, else return nil.
    ;--

    (not (obj-not-complete obj-name))

)

(defun Prl-OBJ (id)
    ;--
    ;-- Return a PRL object given its name; return nil if it doesn't exist.
    ;--

    (is-lib-member id))

(defun is-formal-ref$ (x)
    ;--
    ;-- Return true iff x is a formal reference.
    ;--

    (and (consp x) (eql 'FORMAL! (car x)))

)

(defun is-defn-ref$ (x)
    ;--
    ;-- Return true iff x is a definition reference.
    ;--

    (and (consp x) (not (eql 'FORMAL! (car x))))

)

(defun build-alist$ (name actuals)
    ;--
    ;-- Given the name of the template being referenced and a list of actuals
    ;-- for its formals, we return an assoc list ( -(form act)- ) where
    ;-- form is a formal name and act its corresponding actual.
    ;--

    (Plet (bind-obj  nil   ;-- the binding for the object name of the template.
          defn-obj  nil   ;-- the template definition.
          nformals  nil   ;-- the number of formals in the template's defn.
          fname     nil   ;-- the name of the current formal.
          fnames    nil   ;-- the list of formal names.
         )

         (<- bind-obj (is-lib-member name))

         (Terr-if$ name 1 (null bind-obj))

         (Terr-if$ name 4 (not (eql 'COMPLETE (sel (object bind-obj) status))))
         (Terr-if$ name 5 (not (lib-member name)))
         (Terr-if$ name 6 (not (eql 'DEF (sel (object bind-obj) kind))))

         (<- defn-obj (sel (object bind-obj) value))
         (<- nformals (sel (definition-object defn-obj) num-formals))

         (Ploop (local i nformals)

               (do (<- fname (sel (definition-object defn-obj) formal (i) name))
                   (<- fnames (cons (implode fname) fnames))
               )

               (until (< (<- i (1- i)) 1))
         )

         (Terr-if$ name 2 (not (equal nformals (length actuals))))

         (mapcar 'cons fnames actuals)
)   )

(defun apply-defn (name)
    ;--
    ;-- Given the name of a template, return its right hand side.
    ;--
    ;-- We need the body of the definition object that is the value of the
    ;-- named PRL object.
    ;--

    (Plet (PRL-obj   nil   ;-- the PRL object for the defn.
          defn-obj  nil   ;-- its value, hopefully a definition object.
         )

         (<- PRL-obj (is-lib-member name))

         (Terr-if$ name 1 (null PRL-obj))

         (Terr-if$ name 4 (not (eql 'COMPLETE (sel (object PRL-obj) status))))

         (<- defn-obj (sel (object PRL-obj) value))

         (Terr-if$ name 5 (not (lib-member name)))
         (Terr-if$ name 6 (not (eql 'DEF (sel (object PRL-obj) kind))))

         (sel (definition-object defn-obj) rhs)

)   )

;--
;-- The error handler.
;--

(defun Terr-if$ (txt n condition)
    ;--
    ;-- Generate error number n, but only if the condition is true.
    ;--

    (Plet (err-txt  nil)   ;-- text of error message.

         (Pif condition -->

             (<- err-txt

               (Pif (equal n 1) --> (concat txt '| object does not exist|)
                || (equal n 2) --> (concat txt '| called with wrong #actuals|)
                || (equal n 3) --> (concat txt '| has no value in environment|)
                || (equal n 4) --> (concat txt '| is not COMPLETE|)
                || (equal n 5) --> (concat txt '| is not in the library|)
                || (equal n 6) --> (concat txt '| is not a defn|)
                || t           --> (concat '|No such err nbr | n)
                fi)
             )

             (throw 'process-err (list 'ERR err-txt nil nil))

          fi)
)   )

;--
;-- The error handler.
;--

(defun Derr-if$ (txt n condition)
    ;--
    ;-- Generate error number n, but only if the condition is true.
    ;--

    (Plet (err-txt  nil)   ;-- text of error message.

        (Pif condition -->

           (<- err-txt

             (Pif (equal n 1)  --> '|Missing '=='|
              || (equal n 2)  --> '|Missing '<'|
              || (equal n 3)  --> '|Missing identifier|
              || (equal n 4)  --> (concat '|Missing '>' after | txt)
              || (equal n 5)  --> (concat '|Duplicate identifier |
                                          (implode txt)
                                  )
              || (equal n 6)  --> (concat txt '| not defined on lhs|)
              || (equal n 7)  --> (concat txt '| does not exist|)
              || (equal n 8)  --> (concat txt '| is not a defn|)
              || (equal n 9)  --> (concat txt '| is not in the library|)
              || (equal n 10) --> (concat txt '| is not good|)
              || t            --> (concat '|No such err nbr | n)
              fi)
           )

           (throw 'process-err (list 'ERR err-txt nil nil))

         fi)
)   )

