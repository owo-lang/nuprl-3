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


(defun prltype-to-string (prltype)

   ;-- Given a 'prltype', return a string which is its display form.

      (Pif (eql prltype 'INTEGER)  -->
          '#.(istring "int")
       || (eql prltype 'LIST)  -->
          '#.(istring "list")
       || t  -->
          (error "~a~^ ~a" '|Prltype-to-string -- Invalid type:| prltype)
       fi)
)

;
;-- A nasty global variable: this is used by lib to have disp-Ttree
;--   turn all NLs into SPACEs, so that lib can fit as much information
;--   as possible on each line of the lib window.

(global disp-Ttree-map-NL-to-SPACE)
(eval-when (load eval)
    (setq disp-Ttree-map-NL-to-SPACE nil)
)

;--  Fluid variables for 'display-Ttree', 'map-rc-to-cursor' and 
;--    'map-cursor-to-rc'.

;--    Inputs to put-ttree$

         (fluid mouse-r$)            ;-- When current output encounters
         (fluid mouse-c$)            ;--   this location, record the
                                     ;--   value of 'curr-ttree-cursor' in
                                     ;--   'mouse-cursor'.
         (fluid curr-cursor$)        ;-- When 'curr-ttree-cursor' encounters
                                     ;--   this ttree cursor (reversed),
                                     ;--   record 'out-r,out-c' into
                                     ;--   'curr-r,curr-c'.
         (fluid mapping$)            ;-- Nil if displaying, 
                                     ;--   'TO-RC if mapping cursor to rc
                                     ;--   'TO-CURSOR if mapping rc to cursor.
         (fluid top$)                ;-- Relative coords of window region to
         (fluid left$)               ;--   display/map Ttree into.
         (fluid bot$)
         (fluid right$)
         (fluid lines-to-skip$)      ;-- How many lines of displayed characters
                                     ;--   to ignore before starting actual 
                                     ;--   output into the region.  If this
                                     ;--   value is 0, then processing
                                     ;--   (displaying or mapping) is
                                     ;--   currently within the active area,
                                     ;--   i.e., within top,bot,left and right.
         (fluid early-exit-row$)     ;-- These two specify a way of exiting
         (fluid early-exit-suffix$)  ;--   display early.  If a NL character
                                     ;--   is encountered while displaying
                                     ;--   characters on row 'early-exit-row',
                                     ;--   then check if the suffix of the
                                     ;--   Ttree whose CAR is that NL char
                                     ;--   is 'eq' 'early-exit-suffix'.
                                     ;--   If so, then exit with 'ending-r',
                                     ;--   'ending-c' pointing to first char
                                     ;--   position of 'early-exit-row'.
                                     ;--   If 'early-exit-suffix' is nil,
                                     ;--   then cehcking for early exiting 
                                     ;--   is not performed.
         (fluid bracket-mode$)       ;-- Non-nil if all def references are to
                                     ;--   be displayed fully bracketed.  This
                                     ;--   means that '[' should precede them
                                     ;--   and ']' should follow them.  This is
                                     ;--   useful when one is using a point
                                     ;--   cursor, rather than a block cursor
                                     ;--   (a cursor that highlights the entire
                                     ;--   subtree (def ref) on which it sits).
         (fluid out-r$)              ;-- Where next output char should
         (fluid out-c$)              ;--   be put.
         (fluid curr-ttree-cursor$)  ;-- Ttree cursor (reversed) which points
                                     ;--   to part of original Ttree currently
                                     ;--   being processed

;--    Variables set by put-ttree$

         (fluid mouse-cursor$)       ;-- Ttree cursor (reversed) corresponding
                                     ;--   to 'mouse-r,mouse-c'.
         (fluid curr-r$)             ;-- Relative window coords of location
         (fluid curr-c$)             ;--   corresponding to the reversed
                                     ;--   Ttree cursor, 'curr-cursor'.
                                     ;--   These are set only if mapping$
                                     ;--   is not TO-CURSOR (ie, it is
                                     ;--   nil (displaying) or TO-RC).
         (fluid nl-suffix$)          ;-- The first NL char encountered after
                                     ;--   'cursor' has been encountered, 
                                     ;--   causes 'nl-suffix' to be set to
                                     ;--   the suffix of the (sub)Ttree
                                     ;--   being processed when that first NL
                                     ;--   character was encountered.
                                     ;--  (This is nil if 'cursor' was not
                                     ;--      encountered
                                     ;--   or no NL after 'cursor' encountered,
                                     ;--   or 'cursor' encountered before 'top' 
                                     ;--   of region (caused by lines-to-skip)
                                     ;--  )
         (fluid nl-row$)             ;-- This is undefined if nl-suffix is nil,
                                     ;--   else the row number of the NL
                                     ;--   character.


(defun display-Ttree (t-tree 
                   wnum
                   top$ left$ bot$ right$ 
                   lines-to-skip$
                   bracket-mode$
                   cursor
                   early-exit-suffix$ early-exit-row$
                   blank-to-end-region
                   first-blank-row
                  )

   ;-- Display the Ttree 't-tree' into window 'wnum', within the 
   ;--   rectangular area of the window specified by the relative
   ;--   window coordinates 'top,left,bot,right'.
   ;--   'Lines-to-skip' specifies how many lines from the beginning
   ;--   of the printed form of the Ttree to skip before actually 
   ;--   displaying characters.
   ;--   'Cursor' is a Ttree cursor location corresponding to where 
   ;--   the window cursor should be placed at the end of the display
   ;--   operation.
   ;--   'Blank-to-end-region' if non-nil, then checks if the Ttree 
   ;--   filled the whole region.  If not, then blanks out region from
   ;--   where Ttree ended, to either
   ;--              the end of the region if 'first-blank-row' is nil
   ;--         or   the row immediately preceding 'first-blank-row'.
   ;--   'Bracket-mode$' non-nil causes the Ttree to be displayed with
   ;--   with '[' preceding each def ref and ']' following each def ref.
   ;-- Return a tuple of type 'displayed-Ttree'.


      (Plet (curr-r$            nil   ;-- Default values in case 'curr-cursor'
            curr-c$            nil   ;--   is not reached in the display
                                     ;--   process.
            curr-cursor$       (reverse cursor)
            curr-ttree-cursor$ nil   ;-- This reversed Ttree-cursor records
                                     ;--   the currently displaying location
                                     ;--   within the original Ttree.
            mouse-r$           -1    ;-- Not interested in which Ttree cursor
            mouse-c$           -1    ;--   corresponds to some r,c -- so pick
                                     ;--   an r,c not on the window.
            mouse-cursor$      nil   ;-- Will be ignoring this also.
            mapping$           nil   ;-- Displaying, not mapping
            out-r$             top$  ;-- Start display in top,left of region.
            out-c$             left$
            nl-suffix$         nil   ;-- Holds suffix of ttree being
                                     ;--   processed when first NL after
                                     ;--   'cursor' encountered is reached.
            nl-row$            nil   ;-- The row on which we were displaying
                                     ;--   when the aforementioned
                                     ;--   NL was reached.
            end-reason               ;-- Holds the value thrown by put-ttree.
                                     ;--   nil | END-REGION | EARLY-EXIT
           )

          (selectw wnum)
          (movecursor out-r$ out-c$)

          (<- end-reason (catch 'END-REGION (put-ttree$ t-tree)))
          (Pif (and (null end-reason)
                   blank-to-end-region
              )  -->
              ;-- Put-ttree did not hit end of region
              ;-- nor did it take an early-exit.  So blank
              ;-- out from out-r,out-c to the end of the
              ;-- region (bot,right) if 'first-blank-row' is nil.
              ;-- Else blank out to (first-blank-row - 1,right)
              ;-- 
                 (Ploop (local r out-r$
                              c out-c$
                              real-bot (Pif (null first-blank-row)  -->  bot$
                                        || t  --> (1- first-blank-row)
                                        fi)
                       )
                       (while (not (> r real-bot)))
                       (do
                          (movecursor r c)
			  (erase-n-chars (1+ (- right$ c)))
                          (<- c left$)
                          (<- r (1+ r))
                       )
                 )
                 ;-- The new value of 'first-blank-row' is
                 ;-- 'out-r' if 'out-c' = 'left'
                 ;-- else 'out-r'+1.
                    (Pif (> out-c$ left$)  -->
                        (<- first-blank-row (1+ out-r$))
                     || t  -->
                        (<- first-blank-row out-r$)
                     fi)
           || (eql end-reason 'END-REGION)  -->
              ;-- Indicate there is no first blank row.
                 (<- first-blank-row nil)
           fi)

          (displayed-Ttree curr-r$ curr-c$ out-r$ out-c$ 
                           nl-suffix$ nl-row$ first-blank-row)
     )
)

(defun map-rc-to-cursor (t-tree top$ left$ bot$ right$ lines-to-skip$
                        bracket-mode$ mouse-r$ mouse-c$)

   ;-- Map a relative window location mouse-r,mouse-c to a Ttree cursor.
   ;--   Performs a function similar to the display-Ttree function, but
   ;--   without outputting actual characters to the window, 
   ;--   solely for the purpose of forming
   ;--   a Ttree cursor that would be displayed
   ;--   nearest to 'mouse-r,mouse-c' in the window.   
   ;--   If r,c are to the right of a NL char, then the cursor
   ;--   selects the NL.  If r,c are below the Ttree's display
   ;--   form, then the 'end-of-Ttree' cursor, '(len of ttree),
   ;--   is returned.
 
      (Plet (mouse-cursor$      nil    ;-- Default value in case 'mouse-r,
                                      ;--   mouse-c' not encountered during 
                                      ;--   mapping.
            curr-cursor$       nil    ;-- Not interested in where some
                                      ;--   Ttree cursor maps in the region,
                                      ;--   so supply an impossible Ttree
                                      ;--   cursor.
            curr-ttree-cursor$ nil    ;-- This reversed Tree-cursor keeps track
                                      ;--   of the Ttree location currently
                                      ;--   being mapped. 
            mapping$           'TO-CURSOR
                                      ;-- Indicate mapping from rc to a cursor.
            out-r$             top$   ;-- Start mapping into a virtual region
            out-c$             left$  ;--   at this location.
           )

          (catch 'END-REGION (put-ttree$ t-tree))
          ;-- If mouse-cursor is nil, then mouse-r,mouse-c was not found,
          ;--    so return a T-tree cursor whose one element is 
          ;--    1-past-end-of-list.
          ;-- Else result is the reverse of whatever 'mouse-cursor' is.
             (Pif mouse-cursor$  -->
                 (nreverse mouse-cursor$)
              || t  -->
                 (list (length t-tree))
              fi)
      )
)



(defun map-cursor-to-rc (t-tree top$ left$ bot$ right$
                       lines-to-skip$ bracket-mode$ cursor)

   ;-- Map a Ttree cursor to a relative location r,c in the window.
   ;--   This function is identical to display-Ttree except that no
   ;--   characters are output to the window.  
   ;-- Returns a tuple of type 'mapped-cursor'.

      (Plet (curr-r$            nil   ;-- Default values in case 'curr-cursor'
            curr-c$            nil   ;--   is not reached in the mapping
                                     ;--   process.
            curr-cursor$       (reverse cursor)
            curr-ttree-cursor$ nil   ;-- This reversed Ttree-cursor records
                                     ;--   location within the original
                                     ;--   Ttree corresponding to the
                                     ;--   character currently being mapped.
            mouse-r$           -1    ;-- Not interested in which Ttree cursor
            mouse-c$           -1    ;--   corresponds to some r,c -- so pick
                                     ;--   an r,c not on the window.
            mouse-cursor$      nil   ;-- Will be ignoring this also.
            mapping$           'TO-RC ;-- Mapping from a cursor to rc.
            out-r$             top$  ;-- Start mapping in top,left of region.
            out-c$             left$
            early-exit-suffix$ nil   ;-- Early exit not desired.
            early-exit-row$    nil   ;--
            nl-suffix$         nil   ;-- Holds suffix of ttree being
                                     ;--   processed when first NL after
                                     ;--   'cursor' encountered is reached.
            nl-row$            nil   ;-- The row on which mapping was 
                                     ;--   occurring when the aforementioned
                                     ;--   NL is reached.
           )
	    (catch 'END-REGION (put-ttree$ t-tree))
          (mapped-cursor curr-r$ curr-c$ nl-suffix$ nl-row$)
      )
)

(defun put-ttree$ (ttree)

   ;-- The characters of a T-tree are modifiable, so if out-r,out-c
   ;--   runs over mouse-r,mouse-c, then set mouse-cursor to current
   ;--   T-tree cursor, curr-ttree-cursor.

      ;-- Skip over 'Ttree' marker at start of Ttree.
         (<- ttree (cdr ttree))

      (<- curr-ttree-cursor$ (cons 1 curr-ttree-cursor$))

      (Plet (checkcursor (and (equal (length curr-ttree-cursor$)
                                    (length curr-cursor$)
                             )
                             (not (equal mapping$ 'TO-CURSOR))
                             (null curr-c$)
                        )
           )

          (Ploop
               (while ttree)
               (do
                  ;-- If checkcursor,
                  ;--  then check if curr-ttree-cursor matches curr-cursor.
                     (Pif checkcursor  -->
                         (Pif (equal curr-ttree-cursor$ curr-cursor$)  -->
                             ;-- We are at the character which corresponds
                             ;--   to curr-cursor, so mark it.
                                (<- curr-r$ (- out-r$ lines-to-skip$))
                                (<- curr-c$ out-c$)
                          fi)
                      fi)
                  ;-- Check kind of current item in Ttree.
                     (Pif (dtpr (car ttree))  -->
                         ;-- Must be a defref.
                            (put-defref$ (car ttree))
                      || t  -->
                         ;-- Must be a single character.  The check for
                         ;--   out-r,out-c = mouse-r,mouse-c is done
                         ;--   in 'putch-ttree'.
                            (putch-ttree$ ttree)
                      fi)

                  (<- (car curr-ttree-cursor$) (1+ (car curr-ttree-cursor$)))
                  (<- ttree (cdr ttree))
               )
          )

          ;-- Here we are at the end of the T-tree.  Check if curr-cursor
          ;--   is pointing to one-plus-end-of-list.
             (Pif checkcursor  -->
                 (Pif (equal curr-ttree-cursor$ curr-cursor$)  -->
                     (<- curr-r$ (- out-r$ lines-to-skip$))
                     (<- curr-c$ out-c$)
                  fi)
              fi)

          ;-- Restore curr-ttree-cursor to value upon entry.
             (<- curr-ttree-cursor$ (cdr curr-ttree-cursor$))

      )
)


(defun put-defref$ (defref)

   ;-- Displays/maps a reference to a DEF type object.
   ;--   'Defref' is a list of a DEF name followed by a (possibly empty)
   ;--   list of Ttree children which supply the actuals to match the
   ;--   formals of the DEF.
   ;--   There are two cases.  When the reference is to a 
   ;--   well-defined, complete DEF object, text strings from the DEF
   ;--   are output interspersed with calls to 'put-ttree' to display
   ;--   the children.
   ;--   When the defref is no good for various reasons, it is output in
   ;--   the following form:
   ;--       [ defname child1,child2,...,childn ]
   ;--   using calls to 'put-ttree' to output the children.

      (declare (special *computing-red-or-lib-display-of-proof-p*))

      (Plet (defref-to-do  t
            defref-cursor curr-ttree-cursor$
           )

          ;-- Check if DEF is defined and complete.  If so, use the
          ;--   definition object and put-ttree to display/map the
          ;--   children.

             (Pif (lib-member (car defref))  -->

                 ;-- Check if complete and a DEF.
                    (let ((obj (library-object (car defref))))
                        (Pif (and (eql 'COMPLETE (sel (object obj) status))
                                 (eql 'DEF (sel (object obj) kind))
                            )  -->

                            (<- defref-to-do nil)

                            ;-- Use the def object to get the text strings
                               (<- obj (sel (object obj) value))

                               ;-- Note that if mouse-r,mouse-c is encountered
                               ;--  while in 'putstr-defref', curr-ttree-cursor
                               ;--  will still be pointing to the defref, which
                               ;--  is where it should be pointing.

                               (Pif bracket-mode$ -->
                                    (putstr-defref$ '#.(istring "["))
                                fi)
                               (putstr-defref$ (sel (definition-object obj)
                                                    lhs-text(0)
                                               )
                               )

                            ;-- Now put out all children using 'put-ttree'
                            ;--   and the lhs-text strings which follow
                            ;--   each child.  If mouse-r,mouse-c is 
                            ;--   encountered while in 'putstr-defref' for 
                            ;--   lhs-text(i), curr-ttree-cursor should be
                            ;--   preset to point to one-past-end-of-list
                            ;--   for child(i).
                               (Ploop
                                    (local child-no    1
                                           num-formals (sel (definition-object
                                                             obj)
                                                            num-formals
                                                       )
                                           children    (cdr defref)
                                    )
                                    (while (not (> child-no 
                                                          num-formals
                                    )      )    )
                                    (do
                                       (<- curr-ttree-cursor$ 
                                           (cons child-no defref-cursor)
                                       )
                                       (Pif (and *computing-red-or-lib-display-of-proof-p*
						(equal (sel (definition-object obj)
							    formal(child-no)
							    descriptor)
						       '#.(istring "hidden"))) -->
					   ()
					|| (not (null (cdr (car children)))) -->
                                           ;-- Have a non-empty Ttree child,
                                           ;--  cursor is all set for call to
                                           ;--  'put-ttree'.
                                              (put-ttree$ (car children))
                                        || t  -->
                                           ;-- Here we have a null Ttree child.
                                           ;--  Output formal descriptor in
                                           ;--  brackets.  In case mouse-r,
                                           ;--  mouse-c encountered, set 
                                           ;--  curr-ttree-cursor to 1-past-
                                           ;--  end-of-null Ttree.  If mapping$
                                           ;--  isn't TO-CURSOR and curr-cursor
                                           ;--  matches curr-ttree-cursor, set
                                           ;--  curr-r,curr-c to the first char
                                           ;--  pos of <formal-description>,
                                           ;--  i.e., out-r,out-c.
                                              (<- curr-ttree-cursor$
                                                  (cons 1 curr-ttree-cursor$)
                                              )
                                              (Pif (and 
                                                    (not (eql mapping$
                                                             'TO-CURSOR
                                                         )
                                                    )
                                                    (null curr-c$)
                                                    (equal curr-ttree-cursor$
                                                           curr-cursor$
                                                    )
                                                  )  -->
                                                  (<- curr-r$ 
                                                      (- out-r$ lines-to-skip$) 
                                                  )
                                                  (<- curr-c$ out-c$)
                                               fi)
                                              (putstr-defref$ 
                                                  (append '#.(istring "<")
                                                    (sel (definition-object obj)
                                                         formal(child-no)
                                                         descriptor
                                                    )
                                                    '#.(istring ">")
                                              )   )
                                              (<- curr-ttree-cursor$
                                                  (cdr curr-ttree-cursor$)
                                              )
                                        fi)
                                       ;-- Now put out the lhs-text string to
                                       ;-- follow child(child-no).  
                                       ;-- Curr-ttree-cursor points to 
                                       ;-- child(child-no) -- set it to point 
                                       ;-- 1-past-end-of-list for child(child-
                                       ;-- no), so an encounter with mouse-r,
                                       ;-- mouse-c will yield the appropriate 
                                       ;-- Ttree-cursor.
                                          (<- curr-ttree-cursor$
                                              (cons (length (car children))
                                                    curr-ttree-cursor$
                                              )
                                          )
                                          (putstr-defref$ 
                                              (sel (definition-object obj)
                                                   lhs-text(child-no)
                                              )
                                          )
                                          (<- child-no (1+ child-no))
                                          (<- children (cdr children))
                                    )
                               )
                               ;-- if fully bracketing def refs then put out
                               ;-- closing ']'.  This code has the same effect
                               ;-- as appending ']' to the last lhs-text of
                               ;-- the def ref.  Thus, curr-ttree-cursor$ is
                               ;-- as explained a few lines above.
                                   (Pif bracket-mode$ -->
                                       (putstr-defref$ '#.(istring "]"))
                                    fi)
                         fi)
                    )
              fi)
             (Pif defref-to-do  -->
                 ;-- Must be a bad DEF of sorts.  Put out
                 ;--    [ defname children-separated-by-commas ]
                 ;-- If mouse-r,mouse-c encountered while in 
                 ;--    putstr-defref for '[defname:', curr-ttree-cursor 
                 ;--    will be pointing to the defref.
                    (putstr-defref$ (append '#.(istring "[")
                                            (istring (car defref))
                                            '#.(istring ":")
                                    )
                    )
                 ;-- Now put out all children using 'put-ttree' -- (including
                 ;-- any that may be nil) separated by commas and terminated
                 ;-- by ']'.  Calls to putstr-defref to output the commas
                 ;-- and ']' are preceded by setting curr-ttree-cursor to
                 ;-- point to one-past-end-of-list for the child preceding
                 ;-- the ',' or ']'.
                    (Ploop
                         (local child-no     1
                                num-children (length (cdr defref))
                                children     (cdr defref)
                         )
                         (while (not (> child-no num-children)))
                         (do
                            ;-- Put out the comma before child(i),
                            ;-- i=2..num-children.  Curr-ttree-cursor is
                            ;-- correct for the call to putstr-defref.
                               (Pif (> child-no 1)  -->
                                   (putstr-defref$ '#.(istring ","))
                                fi)

                            ;-- Set curr-ttree-cursor to point to
                            ;-- current child and put out child(child-no).
                               (<- curr-ttree-cursor$
                                   (cons child-no defref-cursor)
                               )
                               (put-ttree$ (car children))

                            ;-- Set up curr-ttree-cursor to point to 
                            ;-- one-past-end-of-list for child(child-no).
                               (<- curr-ttree-cursor$ 
                                   (cons (length (car children))
                                         (cons child-no defref-cursor)
                                   )
                               )
                            (<- child-no (1+ child-no))
                            (<- children (cdr children))
                         )
                    )
                 ;-- Output the ']' character -- curr-ttree-cursor points
                 ;-- to either the defref (if no children) or 1-past-end-
                 ;-- of-list for the last child -- in case ']' lands on
                 ;-- mouse-r,mouse-c.
                    (putstr-defref$ '#.(istring "]"))
              fi)

             ;-- Restore curr-ttree-cursor to point to defref.
                (<- curr-ttree-cursor$ defref-cursor)
      )
)

(defun putstr-defref$ (str)

    (Ploop (while str)
          (do 
             (putch-ttree$ str)
             (<- str (cdr str))
          )
    )
)

(defun putch-ttree$ (ttree)

   ;-- Displays/maps a Ttree character to selected window.
   ;-- The character to be displayed/mapped is (car ttree).

   (Plet (ch (car ttree))

      (Pif disp-Ttree-map-NL-to-SPACE -->
          (Pif (equal ch NL) -->
              (<- disp-Ttree-map-NL-to-SPACE 'skipping-leading-spaces)
	      (<- ch SPACE)

	   || (and (eql disp-Ttree-map-NL-to-SPACE 'skipping-leading-spaces)
		   (equal ch SPACE)
	      ) -->
	      (<- ch nil)

           || t -->
	      (<- disp-Ttree-map-NL-to-SPACE t)

	   fi)
       fi)

      (Pif ch -->
	  (Pif (zerop lines-to-skip$)  -->
	      ;-- Current output position is within the top,bot,left,right
	      ;-- region of the window.  If out-r,out-c = mouse-r,mouse-c
	      ;--      ..or..
	      ;-- if ch is a newline char, and out-r = mouse-r and
	      ;-- out-c <= mouse-c
	      ;-- then set mouse-cursor to curr-ttree-cursor.
		 (Pif (equal ch NL)  -->
		     (Pif (eql mapping$ 'TO-CURSOR)  -->
			 (Pif (and (equal out-r$ mouse-r$)
				  (null mouse-cursor$)
			     )  -->
			     ;-- Found cursor -- exit.
				(<- mouse-cursor$ (copy curr-ttree-cursor$))
				(throw 'END-REGION nil)
			  fi)
		      || (null mapping$)  -->
			 ;-- Displaying, so blank out rest of line to
			 ;-- right border of region.
		            (erase-n-chars (1+ (- right$ out-c$)))

			 ;-- Check if 'cursor' encountered (curr-r$ not null)
			 ;-- and if nl-suffix is still nil.  If nil, then this
			 ;-- is the first NL character after the 'cursor' was
			 ;-- encountered, so mark the current suffix and row.
			    (Pif (and curr-r$ (null nl-suffix$))  -->
				(<- nl-suffix$ ttree)
				(<- nl-row$ out-r$)
			     fi)
    
			 ;-- Check if early exit condition prevails.  If so, 
			 ;-- exit now.
			    (Pif (and early-exit-suffix$
				     (eql early-exit-suffix$ ttree)
				     (equal early-exit-row$ out-r$)
				)  -->
				(putnl-ttree$)
				;-- By throwing a non-nil, we indicate
				;-- that there is no need to write blanks
				;-- till the end of the region.
				(throw 'END-REGION 'EARLY-EXIT)
			     fi)
		      || t  -->
			 ;-- Mapping cursor to rc.
			 ;-- Check if 'cursor' encountered (curr-r$ not null)
			 ;-- If not null, then this is the first NL 
			 ;-- character after the 'cursor' was encountered,
			 ;-- so stop mapping and exit after setting
			 ;-- 'nl-suffix' and 'nl-row'.
			    (Pif curr-r$  -->
				(<- nl-suffix$ ttree)
				(<- nl-row$ out-r$)
				(throw 'END-REGION nil)
			     fi)
		      fi)
    
		     ;-- Perform the NL function.
			(putnl-ttree$)
		  || t  -->
		     ;-- Normal character
			(Pif (and (eql mapping$ 'TO-CURSOR)
				 (null mouse-cursor$)
				 (equal out-r$ mouse-r$)
				 (equal out-c$ mouse-c$)
			     )  -->
			     ;-- Found mouse-cursor -- exit.
				(<- mouse-cursor$ (copy curr-ttree-cursor$))
				(throw 'END-REGION nil)
			 fi)
    
			(Pif (null mapping$)  -->  (putc ch) fi)    
	    
			(<- out-c$ (1+ out-c$))    
			(Pif (> out-c$ right$)  -->    
			    (putnl-ttree$)    
			 fi)    
		  fi)
	   || t  -->
	      ;-- Not on displayable part of Ttree yet.  Simulate display
	      ;-- (without outputting any characters) keeping track of
	      ;-- how many lines would have been output.
		 (Pif (equal ch NL)  -->
		     ;-- Exit if cursor encountered, and we are mapping to rc.
		     ;-- We are at the first NL after cursor was encountered.
		     ;-- So set nl-suffix and nl-row, and exit.
			(Pif (and (eql mapping$ 'TO-RC)
				 curr-r$
			    )  -->
			    (<- nl-suffix$ ttree)
			    (<- nl-row$ (- out-r$ lines-to-skip$))
			    (throw 'END-REGION nil)
			 fi)
		     (<- lines-to-skip$ (1- lines-to-skip$))
		     (<- out-c$ left$)
		  || t  -->
		     (<- out-c$ (1+ out-c$))
		     (Pif (> out-c$ right$)  -->
			 (<- lines-to-skip$ (1- lines-to-skip$))
			 (<- out-c$ left$)
		      fi)
		  fi)
	   fi)
      fi)   
   )
)

(defun putnl-ttree$ ()
 
   ;-- Skips to the start of the next line of the region specified
   ;-- by top,bot,left,right.  If the bottom of the region is 
   ;-- reached, do a 'throw' to exit from 'put-ttree'.

      (<- out-r$ (1+ out-r$))
      (Pif (> out-r$ bot$)  -->
          (throw 'END-REGION 'END-REGION)
       fi)
      (<- out-c$ left$)
      (Pif (null mapping$)  -->  (movecursor out-r$ out-c$) fi)

)

