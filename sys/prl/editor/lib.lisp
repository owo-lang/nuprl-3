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


(global library$)        ;-- List of names of the objects currently
                         ;--  in the library.

(global lib-window-top$) ;-- Name of the library object currently
                         ;--  displayed at the top of the library window.

(global in-lib-window$)  ;-- List of object names of objects which are
                         ;--  (partially) displayed in the library window.
                         ;--  (in reverse order).

(deftuple splitlist      ;-- Constructor for 2 element tuple
            head         ;--   Selector for first element
            tail         ;--   Selector for second
)


(defun lib-init ()

   ;; Initialize global variables for library-related data structures.

      (<- library$ nil)
      (<- lib-window-top$ nil)
      (<- in-lib-window$ nil)

   ;; Attach status display characters as properties of
   ;;  the status atoms RAW, BAD, COMPLETE, and PARTIAL.
      (setf (get 'RAW     'status-disp-char) '#.(istring "?") )
      (setf (get 'BAD     'status-disp-char) '#.(istring "-") )
      (setf (get 'PARTIAL 'status-disp-char) '#.(istring "#") )
      (setf (get 'COMPLETE 'status-disp-char) '#.(istring "*"))

)


(defun library-object (name)
  (get name ':library-object))

(defun bind-library-object (name object)
  (setf (get name ':library-object)
	object))

(defun unbind-library-object (name)
  (remprop name ':library-object))

;;; returns the library object if it exists.
(defun is-lib-member (name)
  (get name ':library-object))

(defun is-in-lib-window (obj-name)
  (member obj-name in-lib-window$))


(defun lib-create (obj-name obj-kind place)

   ;; Creates a library object whose name is 'obj-name' of
   ;;   type 'obj-kind' at 'place' in the library.
   ;; Returns 
   ;;   If everything went OK --> nil
   ;;   Else error msg string describing what went wrong.

      (Plet (temp-part nil)
          (Pif (split-lib$ library$ obj-name)  -->
              '#.(istring "Duplicate object name in library.")
           || t  -->
              (<- temp-part (split-lib-at-place$ library$ place))
              (Pif (null temp-part)  -->
                  '#.(istring "Place not in library")
               || t  -->
                  ;; Insert obj-name into library.
                     (<- library$ (nconc (nreverse (head-of-splitlist temp-part)
                                         )
                                         (list obj-name)
                                         (tail-of-splitlist temp-part)
                                  )
                     )
                  ;; Bind OBJ-obj-name to a new 
                  ;;  object of the correct kind.
                  ;;  Set 'num-formals' to 0 in case object is a DEF.
                     (<- num-formals 0)
                     (bind-library-object obj-name (lib-new-obj obj-kind))
                  ;; Refresh library window with the newly created object
                  ;;  as the center of attention.
                     (<- lib-window-top$ obj-name) 
			     (lib-display)
                  ;; Result nil=OK.
                     nil
               fi)
           fi)
      )
)


(defun lib-delete (objects)

   ;; Deletes a range of objects from the library, where 'objects' is
   ;;  a list of two object names.  The list of objects in
   ;;  the library is partitioned into three parts A,B,C, where B is the
   ;;  range to be deleted.  Then the library is set to A,C.
   ;; Returns
   ;;  If everything went OK --> nil
   ;;  Else error msg string describing the error.

      (Plet (temp-part (split-lib$ library$ (car objects))
            a-part    nil
            b-part    nil
            c-part    nil
            name      nil
            x         nil
            obj-refd  nil
           )
          (Pif (null temp-part)  -->
              '#.(istring "Object not in library.")
           || t  -->
              (<- a-part (head-of-splitlist temp-part))
              (<- temp-part (split-lib$ (tail-of-splitlist temp-part)
                                        (cadr objects)
                            )
              )
              (Pif (null temp-part) -->
                  '#.(istring "Object not in library or range not in order.")
               || t  -->
                  ;; Create b-part (reversed) and c-part from temp-part
                     (<- b-part (cons (car (tail-of-splitlist temp-part))
                                      (head-of-splitlist temp-part)
                                )
                     )
                     (<- c-part (cdr (tail-of-splitlist temp-part)))
                  ;; For all objects being deleted, if any object
                  ;;  is being viewed, then throw an error indicating
                  ;;  object cannot be deleted.
                     (for (x in b-part)
                         (do
                            (Pif (being-viewed$ x)  -->
                                (throw 'CMDERR
                                        (append '#.(istring "'") (istring x)
                                         '#.(istring "' being viewed -- nothing deleted.")
                                        )
                                )
                             fi)
                         )
                     )
		  ;; For all objects being deleted, if any object is referenced
		  ;;  by another object, then throw an error indicating
		  ;;  the object cannot be deleted.
		     (for (x in b-part)
			  (do
			    (let* ((refd-by (sel
					      (object (library-object x))
					      referenced-by))
				   (bad-refs (prl-set-difference refd-by b-part)))
			       (Pif bad-refs  -->
				  (throw 'CMDERR
					(append (istring x)
						'#.(istring " is referenced by ")
						(make-text-list bad-refs)
						'#.(istring " -- nothing deleted.")))
				fi)
			     )
			  )
		     )
                  ;; Invalidate objects in the c-part by objects 
                  ;;  being deleted (in the b-part).
                     (invalidate-lib$ c-part b-part)
                  ;; If lib-window-top was deleted (in b-part) then set
                  ;;  top to the last(a-part) if a-part non-nil. Else
                  ;;  to the first(c-part) if c-part non-nil.  Else nil.
                     (Pif (member lib-window-top$ b-part)  -->
                         ;; Try last(a-part).
                         (Pif a-part  -->
                             (<- lib-window-top$ (car a-part))
                          || t  -->
                             (Pif c-part  -->
                                 (<- lib-window-top$ (car c-part))
                              || t  -->
                                 (<- lib-window-top$ nil)
                              fi)
                          fi)
                      fi)
                  ;; remove instances of objects being deleted from the
                  ;; referenced-by fields of any objects that the deleted
                  ;; objects reference.
                      (for (name in b-part)
                           (do
                               (for (x in (sel (object (library-object name))
                                               references
                                          )
                                    )
                                    (do
                                        (<- obj-refd (library-object x))
                                        (<- (sel (object obj-refd) referenced-by)
                                            (delete name *-*)
                                        )
                                    )
                               )
                          )
                      )
                  ;; Unbind objects being deleted.
		      (mapc #'(lambda (x) (unbind-library-object x)) b-part)
                  ;; Create new library list from a-part and c-part and
                  ;;  refresh lib window.
                     (<- library$ (nconc (nreverse a-part) c-part))
                     (lib-display)
                  ;; Result nil=OK
                     nil
               fi)
           fi)
      )
)

(defun being-viewed$ (name)

   ;; Returns nil if named library object is NOT in any view, 
   ;; else non-nil.
      (or (assoc name view-stack))
)

(defun make-text-list (atom-list)
    ;; Takes a list of atoms, and returns a prl string which contains the
    ;; names of the atoms separated by commas.
    (nconc
      (istring (car atom-list))
      (for (name in (cdr atom-list))
	   (splice (append '#.(istring ", ") (istring name)))
      )
    )
)

(defun lib-display ()
   ;; Displays the current library list of objects
   ;;  starting from object 'lib-window-top' on.
  (let ((temp-part (split-lib$ library$ lib-window-top$)))
    (lib-disp$ (when temp-part (tail-of-splitlist temp-part)))))


(deftuple dumped-object    ;; Each object dumped in a PRL-LIB-DUMP
                           ;;   is represented by the following tuple
          name             ;;   Name of library object
          kind             ;;   Object kind DEF | THM | ML | EVAL
          cur-info         ;;   Dumped info from OBJ-name: for non-thm
                           ;;     objects this is the Ttree of the body,
                           ;;     for thm objects it is a list of the
                           ;;     goal-body and the result of 
                           ;;     dump-proof-tree applied to the proof
          old-info         ;;   Similar to cur-info, but for OLDOBJ-name
)


(defun lib-dump (objects dump-port)

   ;; Given 'objects' is a list of two library objects
   ;; specifying a range of library objects, write a description of the form
   ;;     (PRL-LIB-DUMP dumpobj1 dumpobj2 ...)
   ;; where each dumpobj is an sexpr representing an
   ;; object selected in the range.
   ;;        (name kind current-info archived-info)
   ;;     For DEF, and ML objects, the info fields are the
   ;; body of the object (a Ttree).  For THM objects the info is
   ;; a two element list, the goal-body (a Ttree) and a crunched
   ;; version of the proof (a proof-tree) in which only rule-bodys
   ;; appear.
   ;;
   ;; Returns nil if a failure of any sort
   ;;         t otherwise.

      (declare (special dump-port))

      (Plet (lib-list   (lib-member objects)
            cur-obj    nil
            cur-val    nil
            old-val    nil
            ndumped    0
           )

          (lib-dump-init)

          (dump-lparen)
          (dump 'PRL-LIB-DUMP)

          ;; Lib-list will be nil if object not found or
          ;; range out of order.
          (for (name in lib-list)
              (do

                 (<- cur-obj (library-object name))
                 (<- cur-val (sel (object cur-obj) value))

                 (dump-lparen)
                 (dump name)
                 (dump (sel (object cur-obj) kind))

                 (Pif (eql (sel (object cur-obj) kind) 'DEF)  -->
                     (dump (sel (definition-object cur-val) body))

                  || (eql (sel (object cur-obj) kind) 'ML)  -->
                     (dump (sel (ml-object cur-val) body))

                  || (eql (sel (object cur-obj) kind) 'EVAL)  -->
                     (dump (sel (eval-object cur-val) body))

                  || (eql (sel (object cur-obj) kind) 'THM)  -->
                     (dump-lparen)
                     (dump (sel (theorem-object cur-val) goal-body))
		     (Pif (eq
			   (sel (theorem-object cur-val) proof-rep-type)
			   'RULE-BODY-TREE
			 ) -->
			 (dump (sel (theorem-object cur-val) proof-representation))
		      || t -->
		         (dump-proof-tree$
                             (get-proof-of-theorem-object cur-val name)
                         )
		      fi)
		     (Pif (sel (theorem-object cur-val) extracted-term) -->
			 (dump
			   (term-to-ttree (sel (theorem-object cur-val) extracted-term)))
		      fi)
                     (dump-rparen)
		     (dump-lparen)(dump-rparen) ; nil for the old value.
                     (dump (sel (object cur-obj) status))

                  fi)


                 (dump-rparen)
                 (<- ndumped (1+ *-*))
              )
          )

          (dump-rparen)

          (Pif lib-list  -->
              ndumped
           || t  -->
              (display-message '#.(istring "Object not found or improper range."))
              ;; Result is nil -- failure.
                 nil
           fi)
      )
)


(defun dump-proof-tree$ (proof)
  ;; Walk the proof tree and at each level return a two-element list
  ;; containing the rule-body and a list of the dumped form of the children.
  ;; Don't output null rule bodies.
  (when (not (null proof))
    (dump-lparen)
    (dump (rule-body-of-proof-tree proof))
    (dump-lparen)
    (mapc #'dump-proof-tree$ (children-of-proof-tree proof))
    (dump-rparen)
    (dump-rparen)))

(defun lib-dump-init ()
  ;; Initialize the global vars for lib-dump
  (declare (special dump-need-space))
    
  (<- dump-need-space nil))

(defun dump-lparen ()
  ;; Output a left paren.
  (declare (special dump-need-space dump-port))
  
  ;(write-char #\( #||)||# dump-port)
  (write-char #\( dump-port)
  (<- dump-need-space nil))

(defun dump-rparen ()
  ;; Output a right paren
  (declare (special dump-need-space dump-port))
  ;(write-char #||(||# #\) dump-port)
  (write-char #\) dump-port)
  (<- dump-need-space nil))

(defun dump (object)
  ;; Output a list.
  (declare (special dump-need-space dump-port))
  
  (if (consp object)
      (progn (dump-lparen)
	     (mapc #'dump object)
	     (dump-rparen))
      (progn
	(when dump-need-space
	  (write-char #\Space dump-port))
	(dump-print object)
	(<- dump-need-space t))))

(defun dump-print (x)
  ;; Output an atom.
  (declare (special dump-port))

  (prin1 x dump-port))



(defun lib-jump (object)

   ;; Sets 'lib-window-top' to object name and displays library contents
   ;;  with object as the center of attention.
   ;; Returns
   ;;  If everything went OK  -->  nil
   ;;  Else error msg string describing the error.


      (Plet (temp-part (split-lib$ library$ object))
          (Pif (null temp-part)  -->
              '#.(istring "Object not in library.")
           || t  -->
              (<- lib-window-top$ object)
              (lib-disp$ (tail-of-splitlist temp-part) )
              ;; Result nil=OK.
                 nil
           fi)
      )
)


(defun lib-load (dumped-sexpr place expand-proofs)

   ;; Loads all the items within dumped-obj into the current
   ;; library at 'place'.  Ends with a redisplay of library window
   ;; with the last object loaded at the top.
   ;; If load went OK, then returns a list of the form
   ;;        (num-objects-loaded duplicate-object-name-list)
   ;;  or throws an error message (prlstring) with tag 'CMDERR
   ;;  if load failed some way.
                                                   
      (Plet (num-loaded   0
            temp-part    (split-lib-at-place$ library$ place)
            before-part  nil
            dup-list     nil
            obj-value    nil
            oldobj-value nil
            cur-obj      nil
           )
          (Pif (null temp-part)  -->
              (throw 'CMDERR '#.(istring "Place not in library."))
           fi)

          ;; List of all library object names before
          ;; 'place' (in reverse order).
             (<- before-part (head-of-splitlist temp-part))

          (for (dump-obj in (cdr dumped-sexpr))
              (do  
                 ;; Check if duplicate object found.
                    (Pif (or (member (name-of-dumped-object dump-obj) before-part)
                            (member (name-of-dumped-object dump-obj)
                                  (tail-of-splitlist temp-part)
                            )
                        )  -->
                        ;; Duplicate found.  Add to list of names of
                        ;; duplicates.
                           (<- dup-list (cons (name-of-dumped-object dump-obj)
                                              dup-list
                                        )
                           )
                     || t  -->
                        ;; Form new object OBJ-name with
                        ;; RAW status.
                           (<- num-formals 0)
                           (<- cur-obj
                                (lib-new-obj (kind-of-dumped-object dump-obj))
                           )
                           (bind-library-object (name-of-dumped-object dump-obj)
						cur-obj
                           )

                        ;; Copy the body field for OBJ-
                        ;; object from the dump-object tuple.
                           (<- obj-value (sel (object cur-obj) value))

                           (Pif (eql (kind-of-dumped-object dump-obj) 'DEF)  -->
                               (<- (sel (definition-object obj-value) body)
                                   (cur-info-of-dumped-object dump-obj)
                               )

                            || (eql (kind-of-dumped-object dump-obj) 'ML)  -->
                               (<- (sel (ml-object obj-value) body)
                                   (cur-info-of-dumped-object dump-obj)
                               )


                            || (eql (kind-of-dumped-object dump-obj) 'EVAL)  -->
                               (<- (sel (eval-object obj-value) body)
                                   (cur-info-of-dumped-object dump-obj)
                               )

                            || (eql (kind-of-dumped-object dump-obj) 'THM) -->
                               (<- (sel (theorem-object obj-value) goal-body)
                                   (first (cur-info-of-dumped-object dump-obj))
                               )
                               (set-proof-of-theorem-object
                                   obj-value
                                   'RULE-BODY-TREE
                                   (second (cur-info-of-dumped-object dump-obj))
                               )
			       (get-conclusion-of-theorem-object obj-value)
			       (Plet (extract (third (cur-info-of-dumped-object dump-obj)))
				    (Pif extract -->
					(<- (sel (theorem-object obj-value) extracted-term)
					    (Pif (eql (first extract) 'Ttree) -->
						(let* ((term
							 (catch 'process-err
								(parse extract))))
						  (cond ((eql (car term) 'ERR)
							 nil)
							(t term)))

					     || t -->
						extract
					     fi))
				     fi))

                            fi)

                        ;; Add name to the list of library objects loaded.
                           (<- before-part (cons (name-of-dumped-object
                                                     dump-obj
                                                 )
                                                 before-part
                                           )
                           )
                           (<- num-loaded (1+ num-loaded))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;    this checking should not occur, it is only                          
;;;;    here because at present theorems cannot be loaded                   
;;;;    unless the things they reference are good.                          
;;;;    eventually, bad theorems will be loadable                             
;;;;    and then nothing need be checked at load.                             
                        (<- library$ (append (reverse before-part)            
                                             (tail-of-splitlist temp-part)    
                                     )                                        
                        )                                                     
                        (Pif (member (kind-of-dumped-object dump-obj)            
                                  '(DEF ML EVAL)                              
                            ) -->                                            
                            (check-obj (name-of-dumped-object dump-obj))

                         || (not (null (cddddr dump-obj)))
			    -->
                            ;; This is a new format library with dumped
                            ;; status information.
                                (<- (sel (object cur-obj) status)
                                    (car (cddddr dump-obj))
                                )
				(when expand-proofs
				  (check-obj (name-of-dumped-object dump-obj)))

                         || t -->
                            ;; This is an old library.  Force the proof to
                            ;; be constructed.
                                (Plet (proof
				       (get-proof-of-theorem-object
					 obj-value
					 (name-of-dumped-object dump-obj)))
                                    (Pif (not (null proof)) -->
                                        (<- (sel (object cur-obj) status)
                                            (red-status-to-obj-status
                                                (status-of-proof-tree proof)
                                            )
                                        )
                                     || t -->
                                        (<- (sel (object cur-obj) status) 'BAD)
                                     fi)
                                )
                         fi)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

                     fi)

		    (display-message (istring (name-of-dumped-object dump-obj)))
              )
          )
          (Pif (plusp num-loaded)  -->
              ;; Fix up library and set lib-window-top to the name of
              ;; last object loaded.  Display library window
                 (<- lib-window-top$ (car before-part))
                 (<- library$ (nconc (nreverse before-part)
                                     (tail-of-splitlist temp-part)
                              )
                 )
                 (lib-display)
           fi)

          ;; Return a list of two items
          ;;   1. The number of library objects loaded
          ;;   2. A list of the names of objects which were 
          ;;      in the current library. (Duplicates)
             (list num-loaded dup-list)
      )
)


(defun load-proof-tree$ (dumped-info)

   ;; Examine the two-element list, dumped-info, which contains a goal-body
   ;; and the result of dump-proof-tree applied to the goal's proof tree.
   ;; Return a proof-tree reconstructed from this information.

    (build-proof-tree (car dumped-info) (cadr dumped-info))

)



(defun lib-member (objname)

   ;; If objname is an atom, then
   ;;    If objname is in the library, then return the object name
   ;;    else nil.
   ;; Else
   ;;    it's a list of two objnames, obj1 and obj2, specifying 
   ;;    a range of library objects.  If both names are in the library, and
   ;;    obj1 appears before obj2 then return the sublist of the library
   ;;    from obj1 to obj2.  Otherwise return nil.

      (Plet (partlib nil)
          (Pif (atom objname)  -->
	       (or (and (eql objname 'FIRST) (car library$))
		   (and (eql objname 'LAST) (car (last library$)))
		   (and (is-lib-member objname) objname))
              #|| 
	      (<- partlib (split-lib$ library$ objname))
              (Pif partlib  -->
                  (car (tail-of-splitlist partlib))
               || t  -->
                  nil
               fi)||#
           || t  -->
              ;; Here we have a range specified by two objectnames.
              (<- partlib (split-lib$ library$ (car objname)))
              (Pif partlib  -->
                  (<- partlib (split-lib$ (tail-of-splitlist partlib)
                                          (cadr objname)
                              )
                  )
                  (Pif partlib  -->
                      (<- partlib 
                          (nreverse (cons (car (tail-of-splitlist partlib))
                                          (head-of-splitlist partlib)
                                    )
                          )
                      )
                   fi)
               fi)
              ;; Result is in partlib.
                 partlib
           fi)
      )
)


(defun lib-move (objects place)

   ;; Moves a range of objects in the library to a new place.
   ;;  First divide the library list into three parts A,B,C where
   ;;  B is the range of objects to be moved.  'Place' may be somewhere
   ;;  in either A or C. 
   ;;    If in A, then invalidate objects in B by
   ;;    all objects in tail(A), where tail(A) is all objects in A after
   ;;    'place'. 
   ;;    If in C, then invalidate objects in head(C) by
   ;;    objects in B, where head(C) is all objects in C before 'place'.
   ;;  Finally do the move of objects in B to 'place' and refresh
   ;;  the library window.
   ;; Returns 
   ;;   If everything went OK  -->  nil
   ;;   Else error msg string descibing error.

      (Plet (temp-part (split-lib$ library$ (car objects))
            a-part    nil
            b-part    nil
            c-part    nil
           )
          (Pif (null temp-part)  -->
              '#.(istring "Object not in library.")
           || t  -->
              (<- a-part (nreverse (head-of-splitlist temp-part)))
              (<- temp-part (split-lib$
                                    (tail-of-splitlist temp-part)
                                    (cadr objects)
                            )
              )
              (Pif (null temp-part)  -->
                  '#.(istring "Object not in library or range not in order.")
               || t  -->
                  (<- b-part (cons (car (tail-of-splitlist temp-part))
                                   (head-of-splitlist temp-part)
                             )
                  )
                  (<- c-part (cdr (tail-of-splitlist temp-part)))
                  (Pif (eql (car place) 'BOTTOM) -->
                      ;; Special case since BOTTOM will be found at
                      ;; the end of a-part which is not really the
                      ;; bottom of te library.  Set 'temp-part' to
                      ;; nil, thus forcing a search into c-part.
                      ;; TOP will work correctly, however,
                      ;; since the beginning of a-part is also the
                      ;; beginning of the library.
                         (<- temp-part nil)
                   || t -->
                      (<- temp-part (split-lib-at-place$ a-part place))
                   fi)
                  (Pif temp-part  -->
                      ;; 'Place' is found within a-part.
                      (invalidate-lib$ b-part (tail-of-splitlist temp-part))
                      ;; Form new library list
                         (<- library$
                             (nconc
                                  (nreverse (head-of-splitlist temp-part))
                                  (nreverse b-part)
                                  (tail-of-splitlist temp-part)
                                  c-part
                             )
                         )
                      ;; Set top to (car b-part) and scroll to give 
                      ;;  user context around it.
                         (<- lib-window-top$ (car b-part))
                         (lib-display)
                      ;; Result nil=OK.
                         nil
                   || t  -->
                      ;; Check if 'place' is within c-part.
                         (<- temp-part (split-lib-at-place$ c-part place))
                         (Pif temp-part  -->
                             (invalidate-lib$ 
                                   (reverse (head-of-splitlist temp-part))
                                   b-part
                             )
                             (<- library$
                                 (nconc
                                      a-part
                                      (nreverse (head-of-splitlist temp-part))
                                      (nreverse b-part)
                                      (tail-of-splitlist temp-part)
                                 )
                             )
                             (<- lib-window-top$ (car b-part))
                             (lib-display)
                             ;; Result nil=OK.
                                nil
                          || t  -->
                             '#.(istring "Destination not in library or within source.")
                          fi)
                   fi)          
               fi)
           fi)
      )
)


(defun lib-scroll (amt)

   ;; Scrolls the library window up (positive 'amt') or down (negative 'amt')
   ;;  by 'amt' number of objects.
   ;;  Set 'lib-window-top' to the name of the object 'amt' objects 
   ;;  away from the current 'lib-window-top'.
   ;;  Redisplay the library window with objects from the library
   ;;  starting with the new 'lib-window-top'.
   ;; Returns 
   ;;   nil 

      (Pif library$ --> 
	  (Plet (temp-part (split-lib$ library$ lib-window-top$)
		head-part nil
		tail-part nil
	       )
	      (<- head-part (head-of-splitlist temp-part))
	      (<- tail-part (tail-of-splitlist temp-part))
	      (Pif (not (plusp amt))  -->
		  ;; Move 'amt' objects toward beginning of library list.
		     (Ploop (local i amt)
			   (while (not (or (zerop i) 
					   (null head-part)
				       )
				  )
			   )
			   (do
			      (<- i (1+ i))
			      (<- tail-part (cons (car head-part) tail-part))
			      (<- head-part (cdr head-part))
			   )
		     )
	       || t  -->
		  ;; Move 'amt' objects toward the end of the library list.
		     (Ploop (local i amt)
			   (while (not (or (null (cdr tail-part))
					   (zerop i)
				       )
				  )
			   )
			   (do 
			      (<- i (1- i))
			      (<- tail-part (cdr tail-part))
			   )
		     )
	       fi)
	      (<- lib-window-top$ (car tail-part))
	      (lib-disp$ tail-part)
	      ;; Result nil=OK
		 nil
	  )
      fi)
)


(defun lib-page (amt)

   ;; Pages the library window up (positive 'amt') or down (negative 'amt')
   ;;  by 'amt' number of pages.  If amt is 'bottom or 'top then pages to the
   ;;  bottom or top of the library.
   ;; Returns 
   ;;   nil 

      (Pif library$ -->
	  (Pif (eql amt 'top) -->
	      (<- lib-window-top$ (car library$))
	      (lib-display)

	   || (eql amt 'bottom) -->
	      (<- lib-window-top$
		  (nthelem (max 1 (- (length library$)
				     (truncate (* 2 (window-height lib-window)) 3)
				  )
			   )
			   library$
		  )
	      )
	      (lib-display)

	   || t -->
	      (lib-scroll (* amt (window-height lib-window)))

	   fi)
      fi)
)


(defun lib-shows-obj (objname)

   ;; Given an object name, return non-nil iff object is
   ;;  (partially) displayed in the library window.

      (Pif library$  -->
          (Pif (eql objname 'FIRST)  -->
              (<- objname (car library$))
           || (eql objname 'LAST)  -->
              (<- objname (car (last library$)))
           fi)
       fi)
      (member objname in-lib-window$)
)


(defun update-lib-display (names)

   ;; for any object in names that is displayed in the lib window,
   ;; update its display line

   (selectw lib-window)
   (Ploop (while (not (null names)))
	 (do
	   (Plet (name (car names)
		 tail nil
		 row  nil
		)
		(Pif library$  -->
		    (Pif (eql name 'FIRST)  -->
			(<- name (car library$))
		     || (eql name 'LAST)  -->
			(<- name (car (last library$)))
		     fi)
		 fi)
		(<- tail (member name in-lib-window$))
		(Pif tail -->
		    ;; since in-lib-window$ is reversed, the length of tail
		    ;; is the number of objects at or above the named one.
		    (<- row (1- (length tail)))
		    (movecursor row 1)
		    (erase-to-end-of-line)
		    (movecursor row 1)
		    (catch 'END-WINDOW 
		      (lib-putobj$ name
				   lib-window
				   (window-width lib-window)
				   row
				   row		;- don't put out a new line
				   ))
		 fi)
	   )
	   (<- names (cdr names))
	 )
   )
)


(defun map-mouse-to-lib-object (row col)

   ;; Return the name of the lib object that is displayed on specified
   ;; row of the library window, or nil if there is none.

      (Pif (plusp col) -->
	  (Plet (temp-part (split-lib$ library$ lib-window-top$))
	       (Pif (and (not (minusp row))
			(< row (window-height lib-window))
			(< row (length (tail-of-splitlist temp-part)))
		   ) -->
		   (nthelem (1+ row) (tail-of-splitlist temp-part))
		|| t -->
		   nil
		fi)
	  )

       || t --> ;; col is zero, so (row,col) is in scroll bar
          nil

       fi)
)
 

(defun mouse-scroll-lib (row col)

   ;; The mouse was clicked at row,col.  These are supposed to indicate a
   ;; scroll operation.  Do it if row, col are sensible.
   ;; This function must not change any of the variables denoting the currently
   ;; selected window, so it uses low level variables from win.lisp.

   (Plet (save-selected-prl-window (get-current-selected-window))

	(Pif (minusp row) -->  ;; scroll up a page
	    (lib-page -1)
     
	 || (not (< row (window-height lib-window))) -->  ;; scroll down a page
	    (lib-page 1)
     
	 || (zerop col) --> ;; click was in scroll bar, so scroll to point specified
	    (Pif library$ -->
		(Plet (ll (length library$)
		      wh (window-height lib-window)
		      n  0
		     )
		     (<- n (1+ (truncate (+ (* row ll) (1- wh)) wh)))
		     (<- lib-window-top$ (nthelem n library$))
		     (lib-display)
		)
	     fi)

	 fi)

        (selectw save-selected-prl-window)
   )
)

  
(defun display-lib-object-in-detail (name)

   ;; Display the named object in detail in the cmd/status window.
   ;; This is to provide more information than is visible in the
   ;; library, but not necessarily the as much (or the same) information
   ;; as is shown when an object is viewed.
   ;; This function must not change any of the variables denoting the currently
   ;; selected window, so it uses low level variables from win.lisp.

   (declare (special display-message-window))

   (Plet (save-selected-prl-window (get-current-selected-window)
         currobj  (library-object name)
	 obj-val  nil				;
	 row      0
         width    (window-width display-message-window)
         height   (window-height display-message-window)
	 namestr  (istring name)
	)

	(Pif (and (> height 2)
		 (> width  6)
		 (eql 'THM (sel (object currobj) kind))
	    ) -->
	    (selectw display-message-window)
	    (clear-window)
	    (<- obj-val (sel (object currobj) value))
	    ;; put out name (on one line)
		(Ploop
		    (local col 1)
		    (while (and namestr (< col width)))
		    (do
			(putc (car namestr))
			(<- namestr (cdr namestr))
			(<- col (1+ col))
		    )
		)
		(putnl)
	    ;; put out goal body Ttree
		(putstr '#.(istring "Thm:"))
		(<- row 
		    (ending-r-of-displayed-Ttree
			(display-Ttree 
			    (trim-NLs-and-spaces
				(sel (theorem-object obj-val) goal-body)
			    )
			    display-message-window
			    1             ;-- top
			    5             ;-- left
			    (- height 2)  ;-- bot
			    (- width 2)   ;-- right
			    0             ;-- lines-to-skip
			    nil           ;-- bracket-mode
			    nil           ;-- cursor
			    nil           ;-- early-exit-suffix
			    nil           ;-- early-exit-row
			    nil           ;-- blank-to-end-region
			    nil           ;-- first-blank-row
			)
		    )
		)
                (putnl)
	    ;; put out extracted term Ttree, if exists
                (<- row (+ row 1))
		(Pif (and (< row (1- height))
			 (sel (theorem-object obj-val) extracted-term)
		    ) -->
		    (mapcar 'putc '#.(istring "Ext:"))
		    (<- row 
			(ending-r-of-displayed-Ttree
			    (display-Ttree 
				(trim-NLs-and-spaces
				    (term-to-Ttree
				        (sel (theorem-object obj-val) extracted-term)
				    )
				)
				display-message-window
				row           ;-- top
				5             ;-- left
				(- height 2)  ;-- bot
				(- width 2)   ;-- right
				0             ;-- lines-to-skip
				nil           ;-- bracket-mode
				nil           ;-- cursor
				nil           ;-- early-exit-suffix
				nil           ;-- early-exit-row
				nil           ;-- blank-to-end-region
				nil           ;-- first-blank-row
			    )
			)
		    )
		    (putnl)
		 fi)

	    (selectw save-selected-prl-window)
         
	 fi)
   )
)
 
(defun trim-NLs-and-spaces (Tt)

   ;; remove leading and trailing NL chars and spaces from Tt

    (Ploop (while (or (equal (car Tt) NL) (equal (car Tt) SPACE)))
	  (do (<- Tt (cdr Tt)))
    )
    (<- Tt (reverse Tt))
    (Ploop (while (or (equal (car Tt) NL) (equal (car Tt) SPACE)))
	  (do (<- Tt (cdr Tt)))
    )
    (nreverse Tt)
)

(defun lib-disp$ (lib-list)
  (with-fast-redrawing lib-window #'lib-disp$$ lib-list))

(defun lib-disp$$ (lib-list)

   ;; Display all objects whose names are in 'lib-list'
   ;;   into window 'lib-window', starting at the top of the window,
   ;;   until the window is full or everything in lib-list  
   ;;   has been displayed.
   ;;   
   ;; A general idea of how the library display might look...
   ;;
   ;;    ,------------------------,
   ;;    | LIBRARY                |
   ;;    |------------------------|
   ;;    |.my-result(*T) goal     |
   ;;    |.result2(-T) goal       |
   ;;    |. :                     |
   ;;    ||my-def(?D) template    |
   ;;    |. :                     |
   ;;    '------------------------'
   ;;
   ;;   Each object gets one line in the library.  The line shows the
   ;;   name, status, type, and some of the information associated with
   ;;   the object.  Only enough to fit on one line is shown.  The first
   ;;   char of each line is the scroll bar.  It is | if the lib window
   ;;   is showing objects in the fraction of the lib represented by the
   ;;   line containing the |.  Otherwise, it is a dot.

     (Plet (wh       (window-height lib-window) 
	   ll       (length library$)
	   fd       0 ;- index in lib of first displayed object (starting at 0)
	   ld       0 ;- index in lib of last displayed object  (starting at 0)
	   currline 0
	   scroll-bar-char nil
	  )
          (selectw lib-window)
	  (clear-window)
          (<- in-lib-window$ nil)
          ;; Do output within the range of a 'catch' so that
          ;;  the end-of-screen condition can be handled neatly.
	     (Pif lib-list -->
		 (<- fd (- ll (length (member (car lib-list) library$))))
		 (<- ld (+ fd -1 (min wh (length lib-list))))
		 (catch 'END-WINDOW 
		     (Ploop
			  (while (and (< currline wh)
				      lib-list
				 )
			  )
			  (do
			      (<- in-lib-window$ (cons (car lib-list)
						       in-lib-window$
						 )
			      )
			      ;; determine if the range of lib objects represented
			      ;; by this line overlaps with the objects being displayed
			      ;; in the window (fd..ld).
			          (Pif (or (> fd (1- (truncate (* (1+ currline) ll) wh)))
					  (< ld (truncate (* currline ll) wh))
				      ) -->
				      (<- scroll-bar-char #.(ichar #\space))
				   || t -->
				      (<- scroll-bar-char #.(ichar #\|))
				   fi)
			      (movecursor currline 0)
			      (putc scroll-bar-char)
			      (<- currline (lib-putobj$ (car lib-list)
							lib-window
							(window-width lib-window)
							currline
							wh))
			      (<- lib-list (cdr lib-list))
			  )
		     )
		     (Ploop ;; finish scroll bar
			  (while (< currline wh))
			  (do
			      ;; determine if the range of lib objects represented
			      ;; by this line overlaps with the objects being displayed
			      ;; in the window (fd..ld).
			          (Pif (or (> fd (truncate (* (1+ currline) ll) wh))
					  (< ld (truncate (* currline ll) wh))
				      ) -->
				      (<- scroll-bar-char #.(ichar #\space))
				   || t -->
				      (<- scroll-bar-char #.(car (istring "|")))
				   fi)
			      (putc scroll-bar-char)
			      (<- currline (1+ currline))
			      (when (not (= currline wh))
				(putnl))
			  )
		     )
		 )
              fi)

    )
)


;;  Variables used by 'lib-putobj' and procedures it calls.

(fluid currpos$)
(fluid maxpos$)
(fluid curline$)
(fluid maxline$)
(fluid indent-val$)


(defun lib-putobj$ (name wnum maxpos$ curline$ maxline$)

   ;; Display object OBJ-name starting in the first position of 
   ;;  line 'currline' of the current window (which should be wnum).
   ;;  If at any time during the display, currline = maxline, then 
   ;;  exit to the caller via a 'throw' of type 'END-WINDOW'.
   ;; Returns the line number of the line following the last line
   ;;  of the displayed object.

    (declare (special disp-Ttree-map-NL-to-SPACE))

    (Plet (indent-val$ 6
	  currpos$    1   ; scroll bar is in the first column.
	  currobj     (library-object name)
	  currstatus  nil
	  statuschar  nil
	  *computing-red-or-lib-display-of-proof-p* T
	 )

	 (catch 'END-LINE

	      ;; Get status for current object.
		 (<- currstatus (sel (object currobj) status))
    
	      ;; Get status for OBJ-name.
		 (<- statuschar (get currstatus
				     'status-disp-char
				 )
		 )
    
	      ;; Depending on type of object...
		 (Pif (eql 'THM (sel (object currobj) kind))  -->
		     ;; Put out general info + goal.
		        (if (expanded-thm-p currobj)
			    (lib-putgeninfo$ name statuschar '#.(istring "T"))
			    (lib-putgeninfo$ name statuschar '#.(istring "t")))
			(<- indent-val$ 6)
			(<- disp-Ttree-map-NL-to-SPACE t)
			(Pif (not (> currpos$ (1- maxpos$))) -->
			     (setf currpos$	;lib-putnl needs to know.
				   (ending-c-of-displayed-ttree
				     (display-Ttree 
				       (sel (theorem-object
					      (sel (object currobj) value)
					      )
					    goal-body
					    )
				       wnum
				       curline$      ;; top
				       currpos$      ;; left
				       curline$      ;; bot
				       (1- maxpos$)  ;; right
				       0             ;; lines-to-skip
				       nil           ;; bracket-mode
				       nil           ;; cursor
				       nil           ;; early-exit-suffix
				       nil           ;; early-exit-row
				       nil           ;; blank-to-end-region
				       nil           ;; first-blank-row
				       )))
			 fi)
			(<- disp-Ttree-map-NL-to-SPACE nil)
    
		  || (eql 'DEF (sel (object currobj) kind))  -->
		     ;; Put out general info + template.
		        (lib-putgeninfo$ name statuschar '#.(istring "D"))
			(<- indent-val$ 6)
			(lib-puttemplate$ (sel (object currobj) value))

		  || (eql 'ML (sel (object currobj) kind))  -->
		     ;; Put out general info.
		        (lib-putgeninfo$ name statuschar '#.(istring "M"))
    
		  || (eql 'EVAL (sel (object currobj) kind)) -->
		     ;; Put out general info.
		        (lib-putgeninfo$ name statuschar '#.(istring "E"))
    
		  fi)
	  )

	  (lib-putnl$)
	  ;; Return line num of next line.
	      curline$

      )
)


(defun lib-putgeninfo$ (name status kind)
   (lib-putstr$ status)
   (lib-putstr$ kind)
   (lib-putstr$ '#.(istring " "))
   (lib-putstr$ (istring name))
   (Ploop (while (< currpos$ (truncate maxpos$ 4)))
	 (do (lib-putstr$ '#.(istring " ")))
   )
   (lib-putstr$ '#.(istring "  "))
   (Pif (> currpos$ (truncate maxpos$ 4)) -->
       (Ploop (while (not (equal (rem currpos$ 3) 0)))
	     (do (lib-putstr$ '#.(istring " ")))
       )
    fi)
)


(defun lib-puttemplate$ (def-obj)

   ;; Puts the template part of a definition object out to the library
   ;;  window starting at position 'currpos' of line 'currline'.

      (lib-putstr$ (sel (definition-object def-obj) lhs-text(0)))

      (Ploop (local i 1
                   num-formals (sel (definition-object def-obj) num-formals)
            )
            (while (not (> i num-formals)))
            (do
                (lib-putstr$ '#.(istring "<"))
                (lib-putstr$ (sel (definition-object def-obj)
                                  formal(i)
                                     descriptor
                             )
                )
                (lib-putstr$ '#.(istring ">"))

                (lib-putstr$ (sel (definition-object def-obj) lhs-text(i)))
                (<- i (1+ i))
            )
      )
)


(defun lib-putstr$ (str)

   ;; Put string 'str' out to library window starting in position
   ;;  'currpos' of line 'currline'.  Whenever 'currpos' = 'width',
   ;;  throw 'END-LINE. Leaves the values of 'currline' and 'currpos' at
   ;;  the position in the library window where the next character
   ;;  should be placed.  If 'currline' = 'maxline', then exit on the
   ;;  end of window condition by doing a throw on 'END-WINDOW'.

      (Ploop (while str)
            (do
	      (Pif (equal currpos$ maxpos$)  -->
		  (throw 'END-LINE nil)
               fi)
	      (Pif (equal (car str) NL) -->
		  (putc SPACE)
	       || t -->
		  (putc (car str))
	       fi)
 	      (<- currpos$ (1+ currpos$))
              (<- str (cdr str))
	    )
      )
)


(defun lib-putnl$ ()

   ;; Performs a newline function in the library window.
   ;;  Does a 'throw' to exit on 'END-WINDOW' condition.

      (<- curline$ (1+ curline$))
      (Pif (or
              (equal curline$ maxline$)
              (> curline$ maxline$)
          ) -->
          (throw 'END-WINDOW nil)
       fi)
       (Pif (not (equal currpos$ maxpos$))  -->
          (putnl)
       fi)
      (<- currpos$ 0)
)

 

(defun invalidate-lib$ (list-to-makebad list-of-spoilers)
  (declare (ignore list-to-makebad list-of-spoilers))

   ;; Invalidate (in head to tail order) all objects whose
   ;;   names are in 'list-to-makebad', by objects (which are
   ;;   about to be made inaccessible to them) whose names
   ;;   are in 'list-of-spoilers'.
      nil
)




(defun split-lib$ (lib-list objname)

   ;; Partitions lib-list into a head-list and tail-list
   ;;  where head-list consists of all names in lib-list from the 
   ;;  beginning up to (but not including) the first occurrence of
   ;;  objname, and tail-list consists of all names from objname to
   ;;  the end of lib-list.
   ;;  The special objname keywords FIRST and LAST are abbreviations
   ;;  for the first and last object names (respectively) in lib-list.
   ;; Returns
   ;;  If objname not found or null lib-list --> nil
   ;;  Else a splitlist tuple of (reverse head-list) and tail-list.

      (Pif lib-list  -->
          (Plet (tail (Pif (eql objname 'FIRST)  -->
                         (<- objname (car lib-list))
                         lib-list
                      || (eql objname 'LAST)  -->
                         (<- objname (car (last lib-list)))
                         (list objname)
                      || t  -->
                         (member objname lib-list)
                      fi)
               )
              (Pif tail  -->
                  (splitlist (cdr (member objname (reverse lib-list)))
                             tail
                  )
               || t  -->
                  nil
               fi)
          )
       || t  -->
          nil
       fi)
)


(defun split-lib-at-place$ (lib-list place)

   ;; Partitions lib-list into a head-list and tail-list 
   ;;  where head-list is the prefix of lib-list consisting of 
   ;;  the names of all objects before 'place' and tail-list is
   ;;  the suffix of lib-list consisting of the names of all objects
   ;;  after 'place'.  'Place' is a list of the form
   ;;  (BEFORE objname) (AFTER objname) (TOP) (BOTTOM).
   ;; Returns 
   ;;  If place not found or null lib-list --> nil
   ;;  Else a splitlist tuple of (reverse head-list),tail-list.

      (Pif (null (cdr place))  -->
          ;; Must be TOP or BOTTOM.
          (Pif (eql (car place) 'TOP)  -->
              (splitlist nil lib-list)
           || t  -->
              (splitlist (reverse lib-list) nil)
           fi)
       || t  -->
          (Plet (temp-part (split-lib$ lib-list (cadr place)))
              (Pif (and temp-part
                       (eql (car place) 'AFTER)
                  )  -->
                  ;; Move front of tail-list to the front of head-list.
                     (<- (head-of-splitlist temp-part)
                         (cons (car (tail-of-splitlist temp-part))
                               (head-of-splitlist temp-part)
                         )
                     )
                     (<- (tail-of-splitlist temp-part)
                         (cdr (tail-of-splitlist temp-part))
                     )
               fi)
              ;; Return the temp-part tuple.
                 temp-part
          )
       fi)
)


(defun lib-new-obj (kind)

   ;; Returns a new uninitialized object whose kind is 'kind',
   ;;  with 'RAW' status.  For DEF objects, 'num-formals' should be set
   ;;  before calling this routine.  

      (Plet (new-obj (new object)
            new-val nil
           )
          (<- (sel (object new-obj) status) 'RAW)
          (<- (sel (object new-obj) kind)   kind)
          (<- (sel (object new-obj) value)
              (Pif (eql kind 'THM)  -->
                  (<- new-val (new theorem-object))
                  (<- (sel (theorem-object new-val) goal-body)
                      (copy raw-object-Ttree)
                  )
		  (set-proof-of-theorem-object new-val 'PROOF-TREE nil)
                  new-val
               || (eql kind 'DEF)  -->
                  (<- new-val (new definition-object))
                  (<- (sel (definition-object new-val) body)
                      (copy raw-object-Ttree)
                  )
                  (<- (sel (definition-object new-val) num-formals) num-formals)
                  new-val
               || (eql kind 'ML) -->
                  (<- new-val (new ml-object))
                  (<- (sel (ml-object new-val) body)
                      (copy raw-object-Ttree)
                  )
                  new-val

               || (eql kind 'EVAL) -->
                  (<- new-val (new eval-object))
                  (<- (sel (eval-object new-val) body)
                      (copy raw-object-Ttree)
                  )
                  new-val
               fi)
          )
          ;; 'new-obj' is the result.
             new-obj
      )
)




(defun copy-arrays-and-trees (object)
  (cond ((arrayp object)
	 (map 'vector #'copy-arrays-and-trees
	      (common-lisp:copy-seq object)))
	((consp object)
	 (cons (copy-arrays-and-trees (car object))
	       (copy-arrays-and-trees (cdr object))))
	(t object)))



;;; Because of laziness of the coder, this function depends on object
;;; representations.
(defun copy-object (obj)
    (let* ((kind (sel (object obj) kind))
	   (new-obj (new object))
	   (value (sel (object obj) value)))
      (<- (sel (object new-obj) status) (sel (object obj) status))
      (<- (sel (object new-obj) kind) (sel (object obj) kind))
      (<- (sel (object new-obj) referenced-by) (sel (object obj) referenced-by))
      (<- (sel (object new-obj) references) (sel (object obj) references))
      (case kind
	(DEF (<- (sel (object new-obj) value)
		 (copy-arrays-and-trees (sel (object obj) value))))
	(THM
	 (let* ((new-value (new theorem-object)))
	   (common-lisp:replace new-value value)
	   (<- (sel (theorem-object new-value) goal-body)
	       (copy-tree (sel (theorem-object value) goal-body)))
	   (cond ((eql (sel (theorem-object value) proof-rep-type) 'PROOF-TREE)
		  (<- (sel (theorem-object new-value) proof-representation)
		      (cond ((sel (theorem-object value) proof-representation)
			     (copy-proof (sel (theorem-object value) proof-representation)))))))
	   (<- (sel (object new-obj) value) new-value)))
	(EVAL
	 (let* ((new-value (new ml-object)))
	   (<- (sel (ml-object new-value) body)
	       (copy-tree (sel (ml-object value) body)))
	   (<- (sel (object new-obj) value) new-value)))
	(ML
	 (let* ((new-value (new eval-object)))
	   (<- (sel (eval-object new-value) body)
	       (copy-tree (sel (eval-object value) body)))
	   (<- (sel (object new-obj) value) new-value))))
      new-obj))


