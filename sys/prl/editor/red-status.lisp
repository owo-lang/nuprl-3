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


;-- propagate-red-status (ptree:proof-tree cursor:proof-cursor)
;-- 
;--   Propagate status up a proof tree.  This is only called after a
;-- rule has been refined as that is the only event which causes a status
;-- change.  It returns t if there is a change in status at the current
;-- node, and nil otherwise.

(defun propagate-red-status (ptree cursor)

    (Pif (null cursor) -->

        ;-- The cursor is now pointed at the node which was refined.  This
        ;-- function is called only if there was a change in its status so
        ;-- we can return t.
            t
        
     || (propagate-red-status
            (nthelem
                (car cursor)
                (children-of-proof-tree ptree)
            )
            (cdr cursor)
        ) -->
         
        ;-- The status of this nodes child along the selected path has
        ;-- changed so we must recalculate the status of this node.
            (Plet (old-status (status-of-proof-tree ptree))
                (<- (status-of-proof-tree ptree)
                    (calculate-status-from-proof ptree)
                )
                (Pif (eql (status-of-proof-tree ptree) old-status) -->
                    nil

                 || t -->
                    t

                 fi)
            )

      || t -->
 
         ;-- The status of the selected child is unchanged so the status
         ;-- of this node and its ancestor's can't change. Return nil to
         ;-- inhibit any further status calculations.
             nil

      fi)
)

;(declare (localf status-calculator glb-of-set))

;-- calculate-status-from-proof (ptree:proof-tree)
;--  
;--   Returns the status of the top level of the given proof tree, assuming
;--   the status of all the children have been computed.
;--   This is accomplished by handing the status calculator a function which
;--   grabs the status field of a proof node.

(defun calculate-status-from-proof (ptree)
    (status-calculator
        ptree
	#'(lambda (child-proof-tree)
	    (status-of-proof-tree child-proof-tree)
            )
	)
    )

;-- calculate-status-from-children (children: list of proof-tree)
;--
;--   Calculates the status determined by the list of children.  It is
;--   assumed that the status of the children has been computed.

(defun calculate-status-from-children (children)
    (glb-of-set
        (mapcar
	 #'(lambda (child)
	     (status-of-proof-tree child)
	     )
            children
        )
    )
)

;-- calculate-red-status (ptree:proof-tree)
;--  
;--   Returns the status of the top level of the given proof tree,
;--   with the status of all the children of the node being calculated
;--   first.  This is accomplished by passing the definition of this
;--   function to the status calculator.

(defun calculate-red-status (ptree)
    (status-calculator
        ptree
        #'calculate-red-status
    )
)


;-- status-calculator (ptree:proof-tree, get-child-status: proof-tree->status)
;--  
;-- Return the status at the top level node of the proof tree, using the
;-- function get-child-status to calculate the status of the children of the
;-- node.

(defun status-calculator (ptree get-child-status)
    
    (Pif (null (rule-of-proof-tree ptree)) -->

        ;-- If the rule body hasn't been filled in then the object is
        ;-- incomplete otherwise it is bad.
            (Pif (null-Ttree (rule-body-of-proof-tree ptree)) -->
                'INCOMPLETE

             || t -->
                'BAD

             fi)
        
     || t -->

        ;-- The status of this node is the glb of the status of the
        ;-- children nodes
            (glb-of-set 
                (mapcar
                    get-child-status
                    (children-of-proof-tree ptree)
                )
            )
     fi)
)


;-- glb-of-set (status-set: set-of-status)
;-- 
;--    Compute the greatest lower bound of status in the status p.o.

(defun glb-of-set (status-set)
   (Ploop
       (local glb-so-far 'COMPLETE)
       (while 
           (and 
               status-set 
               (not (eql glb-so-far 'BAD))
           )
       )
       (do 
           (<- glb-so-far (glb-of-2 glb-so-far (car status-set)))
           (<- status-set (cdr status-set))
       )
       (result glb-so-far)
   )
)


;-- glb-of-2 (elmnt1, elmnt2: red-status-type)
;-- 
;--    Compute the glb of 2 elements

(defun glb-of-2 (el1 el2)

    (Pif (member el2 (member el1 '(BAD INCOMPLETE COMPLETE))) -->
        el1

     || t -->
        el2

     fi)
)

;-- red-status-form (status: red-status-type)
;-- 
;--   Return the print form for the given status

(defun red-status-form (status)
    (Plet
        (form (assoc
                  status
                  #.`'((BAD . ,'#.(istring "-"))
		       (INCOMPLETE . ,'#.(istring "#"))
		       (COMPLETE . ,'#.(istring "*")))
              )
        )
        (Pif form -->
            (cdr form)
         || t -->
            nil
         fi)
    )
)

(defun red-status-to-obj-status (red-status)
    (Pif (equal red-status 'INCOMPLETE) --> 'PARTIAL
     || t --> red-status
     fi)
)
