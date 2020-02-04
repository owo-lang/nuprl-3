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


;-------------------------------------;
;                                     ;
;       TED DATA DEFINITIONS          ;
;                                     ;
;-------------------------------------;


;-- Ttree data descriptor: these structures are kept in
;-- the region array for all active Ttree regions

(Pdeftype ted-descriptor
   (Tt              ; Ttree being edited
    cursor          ; current cursor into Tt
    cursor-r        ; row of cursor on screen
    cursor-c        ; col of cursor on screen
    nl-suffix       ; suffix of that subtree of Tt containing the first NL char
                    ;   encountered after the cursor during most recent display
                    ;   of Tt, if any such NL was found, else nil
    nl-row          ; row in window on which the above NL was placed, if any
    first-blank-row ; if region is blank after a certain point, the first row
                    ;   of the blank area, else nil
    lines-to-skip   ; num of lines to skip of display form of Tt
                    ;   when displaying it in the region
    bracket-mode    ; non-nil iff Tt is to be displyed fully bracketed
    long-count      ; number of presses of LONG button pending for this Ttree
   )
)

(defun Ttree-of-ted-descriptor (td)
    (sel (ted-descriptor td) Tt)
)

(global tdescr$ ted-descriptor)  ;-- descriptor of Ttree being edited

(global kill-buffer$)           ;-- sub-list of Ttree elements deleted by
                                ;-- the most recent successful kill action

(global select-list$)           ;-- list of selects made by user with sel and
                                ;-- mouse-sel actions.  Each select is a three
                                ;-- element list, (region Ttree cursor).  The
                                ;-- list is of length at most 2.  If it is of
                                ;-- length one, the selected entity is the
                                ;-- element to which the cursor points.  If it
                                ;-- is of length two, the cursors determine a
                                ;-- range of elements.  This list is reset
                                ;-- with every Ttree modification.

(deftuple selection             ;-- description of the element list selected
                                ;--   by the entries of select-list$
    region                      ;-- the region holding the selected Ttree
    Tt                          ;-- (sub)Ttree containing selected elem list
    left                        ;-- index of first selected element in Tt
    right                       ;-- index of last slelected element in Tt
)


(global ted-parsed-rule) ;-- when ^D is entered in a ted window while editting
                         ;-- a rule, ted parses the rule to see whether or not
                         ;-- to kill the window.  This variable is used to 
                         ;-- store the result of that parse so parse-rule-and
                         ;-- refine won't have to parse the rule again.


;-----------------------------------;
;                                   ;
;       GLOBAL TED ROUTINES         ;
;                                   ;
;-----------------------------------;


;--
;-- ted-init ()
;--
;--     Initialize ted.  This need be called only once
;--     when the system is started.
;--

(defun ted-init ()

    (<- kill-buffer$ nil)
    (<- select-list$ nil)

)


;--
;-- new-ted-region (reg:region#, Tt:Ttree)
;--
;--     Create a new ted descriptor for Tt in region reg,
;--     and place it in reg's descriptor field.
;--

(defun new-ted-region (reg Tt)

    (<- tdescr$ (new ted-descriptor))
    (<- (sel region (reg) descriptor) tdescr$)

    (<- (sel tdescr$ Tt)              Tt)
    (<- (sel tdescr$ cursor)          '(1))
    (<- (sel tdescr$ cursor-r)        (sel region (reg) top))
    (<- (sel tdescr$ cursor-c)        (sel region (reg) left))
    (<- (sel tdescr$ nl-suffix)       nil)
    (<- (sel tdescr$ nl-row)          0)
    (<- (sel tdescr$ first-blank-row) (sel region (reg) top))
    (<- (sel tdescr$ lines-to-skip)   0)
    (<- (sel tdescr$ bracket-mode)    t)
    (<- (sel tdescr$ long-count)      0)

    (redraw-Ttree$ reg 'SMALL-CURSOR-MOTION 'FULL-REFRESH)

)



;--
;-- ted (ch:prlchar)
;--
;--     Process the char ch as a Ttree editing char.  The current
;--     region holds the Ttree to be edited.  Successive chars come
;--     through this routine one by one, so all state info must be
;--     maintained in the region descriptor between chars.
;--

(defun ted (ch)

    (<- (sel region (cur-region) allowed-events) nil)

    (<- tdescr$ (sel region (cur-region) descriptor))
    (Pif (and (not (equal ch '(EXIT)))
             (sel region (cur-region) assoc-region)
        ) -->
        (Plet (descr (sel region ((sel region (cur-region) assoc-region))
                                                                      descriptor
                    )
             )
            (<- (sel (red-descriptor descr) previous-ch-was-exit) nil)
            
        )
     fi)

    (Pif (and (numberp ch)
             (eql (sel region (cur-region) view-kind) 'EDIT)
        ) -->

        ;-- insert the printable character into the Ttree and redraw
            (<- (sel tdescr$ cursor)
                (insert-Tt$ (list ch) (sel tdescr$ Tt) (sel tdescr$ cursor))
            )
            (redraw-Ttree$ cur-region 'SMALL-CURSOR-MOTION 'PARTIAL-REFRESH)
            (clear-selects$)


     || (and (equal ch '(NL))
             (eql (sel region (cur-region) view-kind) 'EDIT)
        ) -->

        ;-- insert a NL into the Ttree and redraw
            (<- (sel tdescr$ cursor)
                (insert-Tt$ (list NL) (sel tdescr$ Tt) (sel tdescr$ cursor))
            )
            (redraw-Ttree$ cur-region 'LARGE-CURSOR-MOTION 'PARTIAL-REFRESH)
            (clear-selects$)


     || (and (equal ch '(DEL))
             (eql (sel region (cur-region) view-kind) 'EDIT)
        ) -->

        ;-- delete the char to the left of the cursor from the Ttree
        ;-- and redraw
            (<- (sel tdescr$ cursor)
                (delete-Tt$ (sel tdescr$ Tt) (sel tdescr$ cursor))
            )
            (Pif (equal (sel tdescr$ cursor-c)
                       (sel region (cur-region) left)
                ) -->
                ;-- deleted char was on previous line
                    (redraw-Ttree$ cur-region
                                   'SMALL-CURSOR-MOTION
                                   'FULL-REFRESH
                    )

             || t -->
                ;-- deleted char was on current line,
                ;-- refresh starting there
                    (redraw-Ttree$ cur-region
                                   'SMALL-CURSOR-MOTION
                                   'PARTIAL-REFRESH
                    )

             fi)
            (clear-selects$)


     || (equal ch '(LONG)) -->
        
        ;-- increment count of contiguous LONG chars seen
            (<- (sel tdescr$ long-count) (1+ *-*))



     || (equal ch '(LEFT)) -->

        (Pif (zerop (sel tdescr$ long-count)) -->

            ;-- move cursor left one position in tree, redraw cursor
                (<- (sel tdescr$ cursor)
                    (cursor-left$ (sel tdescr$ Tt) (sel tdescr$ cursor))
                )

         || (onep (sel tdescr$ long-count)) -->

            ;-- move cursor left 4 positions in tree, redraw cursor
                (for (x in '(1 2 3 4))
                     (do
                         (<- (sel tdescr$ cursor)
                             (cursor-left$ (sel tdescr$ Tt) (sel tdescr$ cursor))
                         )
                     )
                )

         || t -->
    
            ;-- move cursor to leftmost position on current line, redraw cursor
                (Pif (and (zerop (sel tdescr$ lines-to-skip))
                         (equal (sel tdescr$ cursor-r)
                                (sel region (cur-region) top)
                         )
                    ) -->
                    
                    ;-- cursor is on top line of Ttree,
                    ;-- go to first Ttree position
                        (<- (sel tdescr$ cursor) '(1))

                 || t -->

                    ;-- not first line, go to right end of previous
                    ;-- line and then advance one position
                        (ted-cursor-from-rc$
                            (1- (sel tdescr$ cursor-r))
                            (sel region (cur-region) right)
                        )
                        (<- (sel tdescr$ cursor)
                            (cursor-right$ (sel tdescr$ Tt) (sel tdescr$ cursor))
                        )

                 fi)
                

         fi)

        (redraw-cursor$ cur-region)


     || (equal ch '(RIGHT)) -->

        (Pif (zerop (sel tdescr$ long-count)) -->

            ;-- move cursor right one position in tree, redraw cursor
                (<- (sel tdescr$ cursor)
                    (cursor-right$ (sel tdescr$ Tt) (sel tdescr$ cursor))
                )

         || (onep (sel tdescr$ long-count)) -->

            ;-- move cursor right 4 positions in tree, redraw cursor
                (for (x in '(1 2 3 4))
                     (do
                         (<- (sel tdescr$ cursor)
                             (cursor-right$ (sel tdescr$ Tt) (sel tdescr$ cursor))
                         )
                     )
                )

         || t -->
    
            ;-- move cursor to rightmost position on current line, redraw cursor
                (ted-cursor-from-rc$
                    (sel tdescr$ cursor-r)
                    (sel region (cur-region) right)
                )

         fi)

        (redraw-cursor$ cur-region)


     || (equal ch '(UP)) -->

        (Pif (zerop (sel tdescr$ long-count)) -->

            ;-- move cursor up one line to nearest valid position
                (ted-cursor-from-rc$
                    (1- (sel tdescr$ cursor-r))
                    (sel tdescr$ cursor-c)
                )
                (redraw-cursor$ cur-region)

         || (onep (sel tdescr$ long-count)) -->

            ;-- move cursor up 4 lines to nearest valid position
                (ted-cursor-from-rc$
                    (- (sel tdescr$ cursor-r) 4)
                    (sel tdescr$ cursor-c)
                )
                (redraw-cursor$ cur-region)

         || t -->
    
            ;-- move cursor back one region's worth of
            ;-- lines to nearest valid position
                (Plet (region-height
                         (1+ (- (sel region (cur-region) bot)
                                  (sel region (cur-region) top)
                               )
                         )
                     )
                     (ted-cursor-from-rc$
                         (- (sel tdescr$ cursor-r) region-height)
                         (sel tdescr$ cursor-c)
                     )
                     (<- (sel tdescr$ lines-to-skip)
                         (max 0
                              (- (sel tdescr$ lines-to-skip)
                                 region-height
                              )
                         )
                     )
                )
                (redraw-Ttree$ cur-region 'SMALL-CURSOR-MOTION 'FULL-REFRESH)

         fi)


     || (equal ch '(DOWN)) -->

        (Pif (zerop (sel tdescr$ long-count)) -->

            ;-- move cursor down one line to nearest valid position
                (ted-cursor-from-rc$
                    (1+ (sel tdescr$ cursor-r))
                    (sel tdescr$ cursor-c)
                )
                (redraw-cursor$ cur-region)

         || (onep (sel tdescr$ long-count)) -->

            ;-- move cursor down 4 lines to nearest valid position
                (ted-cursor-from-rc$
                    (+ (sel tdescr$ cursor-r) 4)
                    (sel tdescr$ cursor-c)
                )
                (redraw-cursor$ cur-region)

         || t -->
    
            ;-- move cursor forward one region's worth of
            ;-- lines to nearest valid position
                (Plet (region-height
                         (1+ (- (sel region (cur-region) bot)
                                  (sel region (cur-region) top)
                               )
                         )
                     )
                     (ted-cursor-from-rc$
                         (+ (sel tdescr$ cursor-r) region-height)
                         (sel tdescr$ cursor-c)
                     )
                     (<- (sel tdescr$ lines-to-skip)
                         (+ (sel tdescr$ lines-to-skip)
                            region-height
                         )
                     )
                )
                (redraw-Ttree$ cur-region 'SMALL-CURSOR-MOTION 'FULL-REFRESH)

         fi)


     || (equal ch '(DIAG)) -->

        (Pif (zerop (sel tdescr$ long-count)) -->

            ;-- move cursor to parent defref
                (cursor-diag$)

         || (onep (sel tdescr$ long-count)) -->

            ;-- move cursor to fourth parent defref up Ttree
                (for (x in '(1 2 3 4))
                     (do
                         (cursor-diag$)
                     )
                )

         || t -->
    
            ;-- move cursor to root of Ttree
                (<- (sel tdescr$ cursor)
                    '(1)
                )

         fi)

        (redraw-cursor$ cur-region)


     || (equal ch '(SEL)) -->

        (enter-select$ cur-region (sel tdescr$ Tt) (sel tdescr$ cursor))


     || (and (equal ch '(INS))
             (eql (sel region (cur-region) view-kind) 'EDIT) 
        ) -->

        ;-- read a def name, check its validity, insert an
        ;-- instantiation of it just before the current cursor
        ;-- position, and move the cursor right one position
        ;-- (thus leaving it pointing at the first child if any,
        ;--  otherwise after the def instantiation)

            (Plet (name    (nreverse (cdr (nreverse (readcmd '#.(istring "I>")
                                                            #'(lambda (x) (cmd-splicer x))
                                                   )
                                         )
                                    )
                          )
                  obj     nil
                  defref  nil
		  completed-name nil
                 )
		 (<- completed-name
		     (cond ((not (or (null name) (equal (car name) '(EXIT))))
			    (complete-object-name
			      (implode name)
			      #'(lambda (x)
				  (eql 'DEF
				      (sel (object (library-object x)) kind)))))))
                 (Pif (or (null name)
			 (equal (car name) '(EXIT))) -->
                     (display-message '#.(istring "Instantiate ignored."))
		     
            
                  || (not (is-lib-member completed-name)) -->
                     (display-message
		       (append name '#.(istring " does not match a library name.")))
                
                  || t -->
                     (<- name completed-name)
                     (<- obj (library-object name))
                     (Pif (not (eql (sel (object obj) kind)
                                  'DEF
                              )
                         ) -->
                         (display-message (append (istring name)
                                                  '#.(istring " is not a DEF object.")
                                          )
                         )

                      || (not (eql (sel (object obj) status)
                                  'COMPLETE
                              )
                         ) -->
                         (display-message (append (istring name)
                                                  '#.(istring " is not Complete.")
                                          )
                         )
        
                      || t -->
                         ;-- build an empty instantiation and insert it
                             (Ploop
                                 (local i 0)
                                 (while (< i
                                               (sel (definition-object
                                                       (sel (object obj) value)
                                                    )
                                                    num-formals
                                               )
                                        )
                                 )
                                 (do
                                     (<- defref (cons (copy the-null-Ttree) *-*))
                                     (<- i (1+ i))
                                 )
                             )
                             ;-- insert defref into Ttree, but ignore new cursor
                             ;-- returned: leaving cursor at head of defref
                                 (insert-Tt$ (list (cons name defref))
                                             (sel tdescr$ Tt)
                                             (sel tdescr$ cursor)
                                 )
                             ;-- move cursor right one position in Ttree
                                 (<- (sel tdescr$ cursor)
                                     (cursor-right$ (sel tdescr$ Tt)
                                                    (sel tdescr$ cursor)
                                     )
                                 )
                             (redraw-Ttree$ cur-region
                                            'LARGE-CURSOR-MOTION
                                            'PARTIAL-REFRESH
                             )

                      fi)

                  fi)

            )
        (clear-selects$)


     || (and (equal ch '(COPY))
             (eql (sel region (cur-region) view-kind) 'EDIT) 
        ) -->
             
        ;-- copy the selected element list (or the kill buffer if
        ;-- nothing has been selected) just left of the current
        ;-- cursor position

            (Pif (nothing-selected$) -->
                ;-- insert the kill buffer
                    (<- (sel tdescr$ cursor)
                        (insert-Tt$ kill-buffer$ 
                                    (sel tdescr$ Tt)
                                    (sel tdescr$ cursor)
                        )
                    )
                    (redraw-Ttree$ cur-region
                                   'LARGE-CURSOR-MOTION
                                   'PARTIAL-REFRESH
                    )

             || t -->
                (Plet (selection (extract-selection$)
                     )
                     (Pif (and (not (null selection))
                              (< (left-of-selection selection)
                                     (length (Tt-of-selection selection))
                              )
                         ) -->
                         (<- (sel tdescr$ cursor)
                             (insert-Tt$ (select-range$
                                             (Tt-of-selection    selection)
                                             (left-of-selection  selection)
                                             (right-of-selection selection)
                                         )
                                         (sel tdescr$ Tt)
                                         (sel tdescr$ cursor)
                             )
                         )
                         (redraw-Ttree$ cur-region
                                        'LARGE-CURSOR-MOTION
                                        'PARTIAL-REFRESH
                         )
                      fi)
                )

             fi)
        (clear-selects$)


     || (and (equal ch '(KILL))
             (eql (sel region (cur-region) view-kind) 'EDIT) 
        ) -->

        ;-- Make sure the selected region is the current one, then delete
        ;-- the selected element list from it and save the deleted section
        ;-- in kill-buffer$.  Update the cursor appropriately.

            (Plet (selection (extract-selection$)
                 )
                 (Pif (not (null selection)) -->
                     (Pif (equal (region-of-selection selection) cur-region) -->

                         (Pif (< (left-of-selection selection)
                                    (length (Tt-of-selection selection))
                             ) -->
                             (Plet (prior-to-killed
                                      (nthcdr
                                          (1- (left-of-selection selection))
                                          (Tt-of-selection selection)
                                      )
                                   last-of-killed
                                      (nthcdr
                                          (right-of-selection selection)
                                          (Tt-of-selection selection)
                                      )
                                  )
                                  (<- kill-buffer$ (cdr prior-to-killed))
                                  (<- (cdr prior-to-killed)
                                      (cdr last-of-killed)
                                  )
                                  (<- (cdr last-of-killed) nil)
                             )
                             (Tt-modified$)
                             (<- (sel tdescr$ cursor)
                                 (retract-cursor$
                                     (sel tdescr$ Tt)
                                     (sel tdescr$ cursor)
                                     (Tt-of-selection    selection)
                                     (left-of-selection  selection)
                                     (right-of-selection selection)
                                 )
                             )                 
                             (redraw-Ttree$ cur-region
                                            'SMALL-CURSOR-MOTION
                                            'FULL-REFRESH
                             )
                          fi)

                      || t -->
                         (display-message (append
                                              '#.(istring "Kill must be in current ")
                                              '#.(istring "region (selections cleared).")
                                          )
                         )
                                          
                      fi)

                  fi)
            )
        (clear-selects$)


     || (equal ch '(EXIT)) -->
        (Plet (proof-region (sel region (cur-region) assoc-region)
             )
            (Pif (and 
                  proof-region
                  (not
                    (sel (red-descriptor (sel region (proof-region) descriptor)) 
                                                            previous-ch-was-exit
                    )
                  )
                  (sel region (cur-region) modified)
                  (eql 
                    (sel (red-descriptor (sel region (proof-region) descriptor))
                         edited-part
                    )
                    'RULE
                  )
                  (member
                      (car 
                       (<- ted-parsed-rule
                        (parse-rule
                           (sel (red-descriptor
                                          (sel region (proof-region) descriptor)
                                )
                                current-level
                           )
                        )
                       )
                      )
                      '(HELP ERR)
                  )
                ) -->   
                (Pif (eql (car ted-parsed-rule) 'ERR) -->
                    (display-message (append (istring '|ERROR IN REFINEMENT: |)
                                             (istring (cadr ted-parsed-rule))
                                     )
                    )
                 || t -->
                    (display-message (append (istring '|HELP: |)
                                             (istring (cadr ted-parsed-rule))
                                     )
                    )
                 fi)
                (<- ted-parsed-rule nil)
                (<- (sel (red-descriptor (sel region (proof-region) descriptor)) 
                                                            previous-ch-was-exit
                    )                    
                    t
                )
;
;             || (and 
;                  (eql (sel region (cur-region) obj-kind) 'EVAL)
;                  (sel region (cur-region) modified)
;                ) -->
;                ;-- evaluate the Ttree as a term, if this succeeds then
;                ;-- replace it by the resulting term's Ttree, and re-display
;                ;-- the window
;
;                    (let (in-term   nil      ;-- the term to evaluate
;                          out-term  nil      ;-- the result of evaluation
;                         )
;
;                        (<- (sel region (cur-region) modified) nil)
;                        (<- in-term (catch 'process-err (parse (sel tdescr$ Tt))))
;                        (Pif (eql (car in-term) 'ERR) -->
;                            (display-message (istring (cadr in-term)))
;
;                         || t -->
;                            (Pif (not (eql token-type TEndInput)) -->
;                                (display-message
;                                    ^|Characters past end of term ignored.^|
;                                )
;                             fi)
;                            (<- out-term (eval-term in-term))
;                            (Pif (eql (car out-term) 'ERR)  -->  
;                                (display-message (istring (cadr out-term)))
;
;                             || t -->
;                                (<- (sel tdescr$ Tt)
;                                    (copy (term-to-Ttree out-term))
;                                       ;-- this is copied because the out-term
;                                       ;-- Ttree could share with the bodies
;                                       ;-- of some def (I believe -- joe)
;                                )
;                                (<- (sel tdescr$ cursor) '(1))
;                                (<- (sel tdescr$ lines-to-skip)   0)
;                                (<- (sel tdescr$ bracket-mode)    nil)
;                                (<- (sel tdescr$ long-count)      0)
;                                (redraw-Ttree$ cur-region
;                                               'SMALL-CURSOR-MOTION
;                                               'FULL-REFRESH
;                                )
;
;                             fi)
;
;                         fi)
;                    )

             || t -->
                (Pif proof-region -->          
                    ;-- this is a subsidiary Ttree view, let parent know
                        (red-subsidiary-killed cur-region)

                 fi)

                (destroyw (sel region (cur-region) window))
                (destroyview (car (Psome
                                      #'(lambda (view)
                                        (equal cur-region (region-of-view view))
                                       )
                                      view-stack
                                  )
                             )
                )
                (Pif (eql (sel region (cur-region) view-kind) 'SHOW) -->
                    (restore-edit (sel region (cur-region) obj-name))
                 fi)
                (<- num-regions (1- num-regions))
                (<- used-regions (delete cur-region used-regions))
                (<- free-regions (cons cur-region free-regions))
                (Pif (not (zerop num-regions)) -->
                    (Pif (not (zerop cur-region-index)) -->
                        (<- cur-region-index (1- *-*))
                     fi)
                    (<- cur-region (nthelem (1+ cur-region-index)
                                           used-regions
                                   )
                    )
		    (<- cur-window$ (sel region (cur-region) window))
		    (selectw cur-window$)

                 fi)

             fi)
        )

     || (equal ch '(BRACKET)) -->

        ;-- toggle bracket-mode in descriptor
            (<- (sel tdescr$ bracket-mode) (not *-*))
            (redraw-Ttree$ cur-region 'SMALL-CURSOR-MOTION 'FULL-REFRESH)


     || t -->
        ;-- indicate char not processed
            (display-message '#.(istring "Key invalid in this view."))


     fi)

    (Pif (not (equal ch '(LONG))) -->
        (<- (sel tdescr$ long-count) 0)
     fi)

    (<- (sel region (cur-region) allowed-events) '(KILL SIZE))

)


;--
;-- ted-kill-view (view:element-of-view-stack)
;--
;--     Remove the Ttree region associated with the specified view.
;--     Leave cur-region set to the desired value.  The caller must
;--     set and select the appropriate current window.
;--

(defun ted-kill-view (view)

    (Plet (reg (region-of-view view)
         )

        (Pif (not (null (sel region (reg) assoc-region))) -->
            ;-- this is a subsidiary Ttree view, let parent know
                (red-subsidiary-killed reg)

         fi)

        (<- num-regions (1- num-regions))
        (Pif (member cur-region (cdr (member reg used-regions))) -->
            ;-- cur-region is after the region to be killed in the
            ;-- used-regions list, so decrement cur-region-index to
            ;-- keep the current region current
                (<- cur-region-index (1- cur-region-index))
         fi)
        (<- used-regions (delete reg used-regions))
        (<- free-regions (cons reg free-regions))
        (Pif (not (zerop num-regions)) -->
            (<- cur-region-index (rem cur-region-index num-regions))
            (<- cur-region (nthelem (1+ cur-region-index) used-regions))
         fi)

    )
)


;--
;-- ted-size-view (view:element-of-view-stack)
;--
;--     Redraw the Ttree in the region associated with the specified view.
;--

(defun ted-size-view (view)

    (<- (sel (ted-descriptor
                 (sel region ((region-of-view view)) descriptor)
             )
             first-blank-row
        )
        (sel region ((region-of-view view)) top)
    )

    (redraw-Ttree$ (region-of-view view) 'LARGE-CURSOR-MOTION 'FULL-REFRESH)

)


;--
;-- ted-mouse-char (reg:region#, row, col, kind:{MOUSE-JUMP,MOUSE-SEL})
;--
;--     row,col have been selected by the mouse in reg.  If kind is
;--     MOUSE-SEL then enter a selection for the corresponding cursor.
;--     If kind is MOUSE-JUMP, reg must be cur-region, so move cur-region's
;--     cursor to the place corresponding to row,col.
;--

(defun ted-mouse-char (reg row col kind)

    (Plet (cursor nil
         )
        
         (<- tdescr$ (sel region (reg) descriptor))
         (<- cursor (map-rc-to-cursor (sel tdescr$ Tt)
                                      (sel region (reg) top)
                                      (sel region (reg) left)
                                      (sel region (reg) bot)
                                      (sel region (reg) right)
                                      (sel tdescr$ lines-to-skip)
                                      (sel tdescr$ bracket-mode)
                                      row
                                      col
                    )
         )
         (Pif (eql kind 'MOUSE-JUMP) -->
             (<- (sel tdescr$ cursor) cursor)
             (redraw-cursor$ cur-region)

          || t -->
             (enter-select$ reg (sel tdescr$ Tt) cursor)

          fi)
    )
)



;--
;-- ted-splicer (reg:region#, row, col, kind:{MOUSE-JUMP,MOUSE-SEL})
;--
;--     row,col have been selected by the mouse in reg.  If kind is
;--     MOUSE-SEL then return a list of fixnum characters that is the
;--     exploded version of the atom that names the defref pointed to
;--     by the corresponding cursor.  This is either the def itself if
;--     the cursor points to a def, or the enclosing def if the cursor
;--     points to a char or end-of-list.  Else return nil.
;--

(defun ted-splicer (reg row col kind)

    (Plet (cursor     nil
	  old-tdescr tdescr$
         )
        
         (<- tdescr$ (sel region (reg) descriptor))
         (<- cursor (map-rc-to-cursor (sel tdescr$ Tt)
                                      (sel region (reg) top)
                                      (sel region (reg) left)
                                      (sel region (reg) bot)
                                      (sel region (reg) right)
                                      (sel tdescr$ lines-to-skip)
                                      (sel tdescr$ bracket-mode)
                                      row
                                      col
                    )
         )
         (Pif (eql kind 'MOUSE-JUMP) -->
	     (<- tdescr$ old-tdescr)
             nil

          || (null (sel tdescr$ Tt)) -->
	     (<- tdescr$ old-tdescr)
	     nil

          || t -->
             (Plet (Tt      (sel tdescr$ Tt)
		   lastdef nil
                  )

		  (Ploop
		     (while (not (null (cdr cursor))))
		     (do
		        (<- lastdef (nthelem (1+ (car cursor)) Tt))
		        (<- Tt (nthelem (1+ (cadr cursor)) lastdef))
			(<- cursor (cddr cursor))
		     )
		  )
		  (<- Tt (nthelem (1+ (car cursor)) Tt))
		  (<- tdescr$ old-tdescr)
		  (Pif (atom Tt) -->
		      (Pif lastdef -->
			  (istring (car lastdef))

		       || t -->
		          nil

		       fi)
			
		   || t -->
                      (istring (car Tt))

                   fi)
             )
		   
          fi)
    )
)





;----------------------------------------------;
;                                              ;
;       CURSOR MANIPULATION ROUTINES           ;
;                                              ;
;----------------------------------------------;


;--
;-- cursor-right$ (Tt:Ttree, cur:Ttree cursor)
;--
;--     Return a Ttree cursor that is one past cur in
;--     the standard walk of Ttree (that is a pre-order
;--     walk).  If cur is already at the rightmost
;--     position possible, return cursor unchanged
;--     (a test for any motion can be done with eq).
;--

(defun cursor-right$ (Tt cur)

    (Pif (null (cdr cur)) -->

        (Pif (equal (car cur) (length Tt)) -->
            ;-- at end-of-list, cursor cannot be advanced
               cur

         || t -->
            (Plet (elem (nthelem (1+ (car cur)) Tt)
                    ;-- elem is the currently selected element
                 )

                 (Pif (and (dtpr elem) (not (null (cdr elem)))) -->
                     ;-- elem is a defref with children, advance
                     ;-- to the first child
                         (list (car cur) 1 1)

                  || t -->
                     ;-- either elem is a char or has no children, advance
                     ;-- to the element immediately following elem
                         (list (1+ (car cur)))
                
                  fi)
            )

         fi)

     || t -->
        (Plet (newcur (cursor-right$ (nthelem (1+ (cadr cur))
                                             (nthelem (1+ (car cur)) Tt )
                                    )
                                    (cddr cur)
                     )
             )

             (Pif (eql (cddr cur) newcur) -->
                 ;-- cursor into defref's child was at rightmost possible
                 ;-- position, we must advance cursor at this level
                     (Pif (equal (1+ (cadr cur))
                                (length (nthelem (1+ (car cur)) Tt))
                         ) -->
                         ;-- no children remain in this defref,
                         ;-- advance to next element of Tt
                             (list (1+ (car cur)))
                
                      || t -->
                         ;-- advance to next child of this defref
                             (list (car cur) (1+ (cadr cur)) 1)

                      fi)

              || t -->
                 ;-- newcur has been advanced, so leave cursor prefix alone
                     (cons (car cur)
                           (cons (cadr cur) newcur)
                     )

              fi)
        )
     fi)
)


;--
;-- cursor-left$ (Tt:Ttree, cur:Ttree cursor)
;--
;--     Return a Ttree cursor that is one before cur in
;--     the standard walk of Ttree (that is a pre-order
;--     walk).  If cur is already at the leftmost
;--     position possible, return cursor unchanged
;--     (a test for any motion can be done with eq).
;--

(defun cursor-left$ (Tt cur)

    (Pif (null (cdr cur)) -->

        (Pif (onep (car cur)) -->
            ;-- at first element of Tt, cursor cannot be retracted
               cur

         || t -->
            (Plet (prev-elem (nthelem (car cur) Tt)
                    ;-- prev-elem is just left of the currently selected element
                 )

                 (Pif (and (dtpr prev-elem) (not (null (cdr prev-elem)))) -->
                     ;-- prev-elem is a defref with children, retract
                     ;-- to the end-of-list of the last child
                         (list (1- (car cur))
                               (1- (length prev-elem))
                               (length (nthelem (length prev-elem) prev-elem))
                         )

                  || t -->
                     ;-- either prev-elem is a char or has no children,
                     ;-- retract cursor to select it
                         (list (1- (car cur)))
                
                  fi)
            )

         fi)

     || t -->
        (Plet (newcur (cursor-left$ (nthelem (1+ (cadr cur))
                                            (nthelem (1+ (car cur)) Tt )
                                   )
                                   (cddr cur)
                     )
             )

             (Pif (eql (cddr cur) newcur) -->
                 ;-- cursor into defref's child was at leftmost possible
                 ;-- position, we must retract cursor at this level
                     (Pif (onep (cadr cur)) -->
                         ;-- no children remain in this defref,
                         ;-- retract to the entire defref
                             (list (car cur))
                
                      || t -->
                         ;-- retract to end-of-list of the previous
                         ;-- child of this defref
                             (list (car cur)
                                   (1- (cadr cur))
                                   (length (nthelem
                                                (cadr cur)
                                                (nthelem (1+ (car cur)) Tt)
                                           )
                                   )
                             )

                      fi)

              || t -->
                 ;-- newcur has been retracted, so leave cursor prefix alone
                     (cons (car cur)
                           (cons (cadr cur) newcur)
                     )

              fi)
        )
     fi)
)


;--
;-- cursor-diag$ ()
;--
;--     move cursor to parent if one exists,
;--     else leave cursor alone
;--

(defun cursor-diag$ ()

    (Pif (not (null (cdr (sel tdescr$ cursor)))) -->
        (<- (sel tdescr$ cursor) (reverse (cddr (reverse *-*))))
     fi)
)


;--
;-- ted-cursor-from-rc$ (r:window-row, c:window-column)
;--
;--     set cur-region's cursor so that its corresponding r,c is
;--     nearest to specified r,c for any value of r and for c within
;--     left through right region boundaries
;--

(defun ted-cursor-from-rc$ (r c)

    (<- (sel tdescr$ cursor)
        (map-rc-to-cursor
            (sel tdescr$ Tt)
            (sel region (cur-region) top)
            (sel region (cur-region) left)
            (sel region (cur-region) bot)
            (sel region (cur-region) right)
            (max 0
                 (+ (sel tdescr$ lines-to-skip)
                    (- r (sel region (cur-region) top))
                 )
            )
            (sel tdescr$ bracket-mode)
            (sel region (cur-region) top)
            c
        )
    )
)


;--
;-- retract-cursor$ (Tt-for-cur:Ttree, cur:Ttree-cursor,
;--                  Tt-for-range:Ttree, left:elem-number, right:elem-number)
;--
;--     Compute a new cursor from cur on the assumption that elements
;--     left through right inclusive of Tt-for-range have been deleted.
;--     cur is a cursor into Tt-for-cur, which may or may not have
;--     Tt-for-range as a subtree.  Neither left nor right may be one
;--     past the end of list.
;--

(defun retract-cursor$ (Tt-for-cur cur Tt-for-range left right)

    (Pif (eql Tt-for-cur Tt-for-range) -->
        (Pif (< (car cur) left) -->
            ;-- cur passes left of range, return it unchanged
                cur

         || (> (car cur) right) -->
            ;-- cur passes right of range, decrease its first selector
            ;-- by the length of the deleted range
                (cons (- (car cur)
                         (1+ (- right left))
                      )
                      (cdr cur)
                )
         || t -->
            ;-- cursor passes through the range, return left -- the post-kill
            ;-- index of the element following the range
                (list left)

         fi)

     || (null (cdr cur)) -->
        ;-- cursor does not pass through range, return it unchanged
            cur
       
     || t -->
        ;-- keep on walking down the tree, cur is OK so far
            (cons (car cur)
                  (cons (cadr cur)
                        (retract-cursor$
                            (nthelem (1+ (cadr cur))
                                     (nthelem (1+ (car cur))
                                              Tt-for-cur
                                     )
                            )
                            (cddr cur)
                            Tt-for-range
                            left
                            right
                        )
                  )
            )

     fi)
)



;-------------------------------------------;
;                                           ;
;       TTREE MODIFICATION ROUTINES         ;
;                                           ;
;-------------------------------------------;


;--
;-- delete-Tt$ (Tt:Ttree, cur:Ttree-cursor)
;--
;--     Delete the character before the element selected by cur
;--     from Tt.  If there is no such char (the selected element
;--     is the first in the Ttree, or the previous element is not
;--     a character) then do nothing.  Return a cursor specifying
;--     the same element as before the delete.  Assume Tt is the
;--     for the cur-region and thus call Tt-modified$ if delete occurs.
;--

(defun delete-Tt$ (Tt cur)

    (Pif (null (cdr cur)) -->
        ;-- have reached selected element - delete the previous
        ;-- character, if possible
            (Pif (and (> (car cur) 1)
                     (not (dtpr (nthelem (car cur) Tt)))
                ) -->
                (<- (cdr (nthcdr (- (car cur) 2) 
                                 Tt
                         )
                    )
                    (cdr *-*)
                )
                (Tt-modified$)
                (list (1- (car cur)))

             || t -->
                cur

             fi)

     || t -->
        ;-- proceed to the selected defref's selected child
            (cons (car cur)
                  (cons (cadr cur)
                        (delete-Tt$ (nthelem (1+ (cadr cur))
                                             (nthelem (1+ (car cur))
                                                      Tt
                                             )
                                    )
                                    (cddr cur)
                        )
                  )
            )

     fi)
)


;--
;-- insert-Tt$ (elem-list:list-of-Ttree-elements, Tt:Ttree, cur:Ttree-cursor)
;--
;--     Insert elem-list just before the element of Tt
;--     specified by cur.  Make a copy of elem-list since
;--     Ttrees are mutable objects and sharing must be
;--     prevented.  Return a cursor specifying the same
;--     element in the constructed Ttree as cur did in Tt.
;--     Assume Tt is for the cur-region and call Tt-modified$.
;--

(defun insert-Tt$ (elem-list Tt cur)

    (Pif (null (cdr cur)) -->
        ;-- insert elem-list before the (car cur)'th element of Tt
            (<- (cdr (nthcdr (1- (car cur))
                             Tt
                     )
                )
                (nconc (copy elem-list) *-*)
            )
            (Tt-modified$)

            (list (+ (car cur) (length elem-list)))

     || t -->
        ;-- cursor selects some element of a child of a defref -
        ;-- insert elem-list into that child, return the full cursor
            (cons (car cur)
                  (cons (cadr cur)
                        (insert-Tt$ elem-list
                                    (nthelem (1+ (cadr cur))
                                             (nthelem (1+ (car cur))
                                                      Tt
                                             )
                                    )
                                    (cddr cur)
                        )
                  )
            )

     fi)
)


;--
;-- Tt-modified$ ()
;--
;--     The Tt of the current region has been modified.  Set the
;--     modified field in its region to t and if there is an named
;--     object defined for this region then change its status to RAW.

(defun Tt-modified$ ()

    (Pif (not (sel region (cur-region) modified)) -->
        (<- (sel region (cur-region) modified) t)
        (Pif (and
	      (not (null (sel region (cur-region) obj-name)))
	      (null (sel region (cur-region) assoc-region))) -->
            (set-object-status (sel region (cur-region) obj-name)
                               'RAW
            )
         fi)
     fi)
)



;--------------------------------;
;                                ;
;       SELECTION ROUTINES       ;
;                                ;
;--------------------------------;


;--
;-- enter-select$ (reg:region#, Tt:Ttree, cur:Ttree-cursor)
;--
;--     Add the selected entity to select-list$.  Keep the length of
;--     the list at most 2 by deleting the oldest entry, if necessary.
;--     Correctness of the selections is checked by extract-selection$.
;--

(defun enter-select$ (reg Tt cur)

    (Pif (null select-list$) -->
        (<- select-list$ (list (list reg Tt cur)))

     || t -->
        (<- select-list$ (list (list reg Tt cur)
                               (car select-list$)
                         )
        )

     fi)
)


;--
;-- nothing-selected$ ()
;--
;--     Return non-nil iff select-list$ is null.
;--

(defun nothing-selected$ ()
    (null select-list$)
)


;--
;-- clear-selects$ ()
;--
;--     Empty select-list$ of any selects
;--

(defun clear-selects$ ()
    (<- select-list$ nil)
)

                                    
;--
;-- extract-selection$ ()
;--
;--     Return a selection object defined by select-list$.
;--     If select-list$ does not properly define a selection,
;--     then return nil.
;--

(defun extract-selection$ ()
    
    (Plet (reg   nil
          Tt    nil
          cur1  nil
          cur2  nil
         )

         (Pif (null select-list$) -->
             ;-- extract element pointed to by cur-regions's cursor
                 (<- reg  cur-region)
                 (<- Tt   (sel tdescr$ Tt))
                 (<- cur1 (sel tdescr$ cursor))
                 (<- cur2 (sel tdescr$ cursor))

          || (null (cdr select-list$)) -->
             ;-- extract the single element selected
                 (<- reg  (car   (car select-list$)))
                 (<- Tt   (cadr  (car select-list$)))
                 (<- cur1 (caddr (car select-list$)))
                 (<- cur2 cur1)

          || t -->
             ;-- extract the selected range, if it is valid
                 (Pif (or (not (equal (car (car  select-list$))
                                     (car (cadr select-list$))
                              )
                         )
                         (not (equal (cadr (car  select-list$))
                                     (cadr (cadr select-list$))
                              )
                         )
                     ) -->
                     (display-message (append
                                         '#.(istring "Selections are incompatible")
                                         '#.(istring " (selections cleared).")
                                      )
                     )

                  || t -->
                     (<- reg  (car   (car  select-list$)))
                     (<- Tt   (cadr  (car  select-list$)))
                     (<- cur1 (caddr (car  select-list$)))
                     (<- cur2 (caddr (cadr select-list$)))

                  fi)

          fi)
    
         (Plet (sel-Tt nil
              )
              (Pif (null Tt) -->
                  nil

               || t -->
                  (<- sel-Tt (extract-selected-Ttree$ Tt cur1 cur2))
                  (Pif (atom sel-Tt) -->
                      (display-message (append
                                          '#.(istring "Selections do not properly denote")
                                          '#.(istring " a range (selections cleared). ")
                                       )
                      )
                      nil

                   || t -->
                      (selection reg
                                 (car sel-Tt)
                                 (cadr sel-Tt)
                                 (caddr sel-Tt)
                      )
                   fi)
               fi)
         )
    )
)


;--
;-- select-range$ (Tt:Ttree, left:element-number, right:element-number)
;--
;--     left and right are indices into Tt.  The first elem of Tt is
;--     considered to be numbered 0.  Return the sublist of Tt from
;--     element left through right inclusive.
;--

(defun select-range$ (Tt left right)
    
    (Pif (zerop right) -->
        (list (car Tt))

     || (zerop left) -->
        (cons (car Tt)
              (select-range$ (cdr Tt) 0 (1- right))
        )

     || t -->
        (select-range$ (cdr Tt) (1- left) (1- right))

     fi)
)


;--
;-- extract-selected-Ttree$ (Tt:Ttree, cur1:Ttree-cursor, cur2:Ttree-cursor)
;--
;--     cur1 and cur2 are cursors into Tt.  The selected Ttree is
;--     a sub-list of some level of Tt.  If cur1 and cur2 match down to
;--     some level, there diverge by choosing different list elements,
;--     and cur1 (cur2) proceeds down the left(right)most path in its
;--     sub-tree, then the selected Ttree is the sublist at which they
;--     diverge from the left element through the right element (through
;--     the last list element if cur2 selects past end-of-list).  If cur1
;--     and cur2 match down to some level, select the same defref, but
;--     cur1 (cur2) selects the left(right)most child and then proceeds
;--     down the left(right)most path in that child, then the selected
;--     Ttree is the one element sub-list holding the defref on which
;--     they diverge.  If cur1 and cur2 match fully, then the element
;--     specified is selected (past end-of-list is selected if cur1/cur2
;--     point past end-of-list).  If cur1 is to the right of cur2, they
;--     are treated as if they were interchanged.  The selected Ttree
;--     is returned as a selected-Ttree, containing a Ttree with left
;--     and right element numbers.  If the above conditions for sensible
;--     selection are not met, the atom BAD-SELECTION is returned.
;--

(deftuple selected-Ttree Tt left right)

(defun extract-selected-Ttree$ (Tt cur1 cur2)

    (Pif (not (equal (car cur1) (car cur2))) -->
        ;-- cursors diverge on choice of list elements -
        ;-- the entire interval is selected
            (Pif (and (< (car cur1) (car cur2))
                     (leftmost$ (nthelem (1+ (car cur1)) Tt)
                                (cdr cur1)
                     )
                ) -->

                    (Pif (equal (car cur2) (length Tt)) -->
                        (selected-Ttree Tt (car cur1) (1- (car cur2)))
                     
                     || (rightmost$ (nthelem (1+ (car cur2)) Tt)
                                    (cdr cur2)
                        ) -->
                        (selected-Ttree Tt (car cur1) (car cur2))

                     || t -->
                        'BAD-SELECTION

                     fi)

             || (and (> (car cur1) (car cur2))
                     (leftmost$ (nthelem (1+ (car cur2)) Tt)
                                (cdr cur2)
                     )
                ) -->

                    (Pif (equal (car cur1) (length Tt)) -->
                        (selected-Ttree Tt (car cur2) (1- (car cur1)))
                     
                     || (rightmost$ (nthelem (1+ (car cur1)) Tt)
                                    (cdr cur1)
                        ) -->
                        (selected-Ttree Tt (car cur2) (car cur1))

                     || t -->
                        'BAD-SELECTION

                     fi)
        
             || t -->
                'BAD-SELECTION

             fi)

     || (and (null (cdr cur1)) (null (cdr cur2))) -->
        ;-- both cursors end at same element -
        ;-- the singleton interval is selected
            (selected-Ttree Tt (car cur1) (car cur1))

     || (null (cdr cur1)) -->
        ;-- cur1 ends at element, cur2 continues down -
        ;-- the singleton interval is selected
            (Pif (rightmost$ (nthelem (1+ (car cur1)) Tt)
                            (cdr cur2)
                ) -->
                (selected-Ttree Tt (car cur1) (car cur1))

             || t -->
                'BAD-SELECTION
             fi)

     || (null (cdr cur2)) -->
        ;-- cur2 ends at element, cur1 continues down -
        ;-- the singleton interval is selected
            (Pif (rightmost$ (nthelem (1+ (car cur1)) Tt)
                            (cdr cur1)
                ) -->
                (selected-Ttree Tt (car cur1) (car cur1))

             || t -->
                'BAD-SELECTION
             fi)

     || (equal (cadr cur1) (cadr cur2)) -->
        ;-- both select the same child of a defref - extract from the child
            (extract-selected-Ttree$
                (nthelem
                    (1+ (cadr cur1))
                    (nthelem (1+ (car cur1)) Tt)
                )
                (cddr cur1)
                (cddr cur2)
            )

     || (< (cadr cur1) (cadr cur2)) -->
        ;-- both select a given defref, but cur1 selects an earlier child -
        ;-- the singleton interval is selected
            (Pif (and (leftmost$ (nthelem (1+ (car cur1)) Tt)
                                (cdr cur1)
                     )
                     (rightmost$ (nthelem (1+ (car cur1)) Tt)
                                 (cdr cur2)
                     )
                ) -->
                (selected-Ttree Tt (car cur1) (car cur1))

             || t -->
                'BAD-SELECTION

             fi)

     || t -->
        ;-- both select a given defref, but cur1 selects a later child -
        ;-- the singleton interval is selected
            (Pif (and (leftmost$ (nthelem (1+ (car cur1)) Tt)
                                (cdr cur2)
                     )
                     (rightmost$ (nthelem (1+ (car cur1)) Tt)
                                 (cdr cur1)
                     )
                ) -->
                (selected-Ttree Tt (car cur1) (car cur1))

             || t -->
                'BAD-SELECTION

             fi)

     fi)
)


;--
;-- leftmost$ (elem:Ttree-element, elcur:Ttree-element-cursor)
;--
;--     elem is a Ttree element, ie., a char or a defref.  cur is a
;--     cursor into that element, ie., a normal cursor with the initial
;--     element selector deleted.  This boolean valued function
;--     determines whether cur moves down the leftmost possible path
;--     in elem, ie., whether it always chooses the leftmost children
;--     and leftmost elements.
;--

(defun leftmost$ (elem elcur)
    
    (or (null elcur)
        (and (onep (car elcur))               ;the first child is selected
             (or (null-Ttree (cadr elem))     ;the child is the empty Ttree
                 (and (onep (cadr elcur))     ;the first element of the child
                                              ;  is selected
                      (leftmost$              ;the rest of cursor is leftmost
                          (cadadr elem)       ;  in the first element of the
                          (cddr elcur)        ;  first child     
                      )
                 )
             )
        )
    )
)


;--
;-- rightmost$ (elem:Ttree-element, elcur:Ttree-element-cursor)
;--
;--     elem is a Ttree element, ie., a char or a defref.  cur is a
;--     cursor into that element, ie., a normal cursor with the initial
;--     element selector deleted.  This boolean valued function
;--     determines whether cur moves down the rightmost possible path
;--     in elem, ie., whether it always chooses the rightmost children
;--     and rightmost elements (or ends by selecting one past end-of-list).
;--

(defun rightmost$ (elem elcur)
    
    (or (null elcur)
        (and (equal (1+ (car elcur))          ;the last child is selected
                    (length elem)
             )
             (Plet (child (nthelem
                             (1+ (car elcur))
                             elem
                         )
                  ) 
                  (or (null-Ttree child)        ;the child is the empty Ttree
                      (equal (cadr elcur)       ;the child is selected past
                             (length child)     ;  its end-of-list
                      )
                      (Plet (len (length child)
                           )
                           (and
                               (equal           ;the last element of the child
                                   len          ;  is selected
                                   (1+ (cadr elcur))
                               )
                               (rightmost$      ;the rest of cursor is
                                   (nthelem     ;  rightmost in the last
                                       len      ;  element of the last child
                                       child
                                   )
                                   (cddr elcur)
                               )
                           )
                      )
                  )
             )
        )
    )
)



;-------------------------------;
;                               ;
;       DISPLAY ROUTINES        ;
;                               ;
;-------------------------------;


(global tdescr2$ ted-descriptor)

;--
;-- redraw-Ttree$ (reg:     region#
;--                motion:  {SMALL-CURSOR-MOTION, LARGE-CURSOR-MOTION},
;--                refresh: {PARTIAL-REFRESH, FULL-REFRESH}
;--               )
;--
;--     Redraw the Ttree found in region reg.  If motion is SMALL, the
;--     cursor is probably still n the region, so redisplay immediately
;--     and do it again if the cursor turns out to be off region.
;--     If motion is LARGE, compute exactly where the cursor is and
;--     redisplay once.  If the cursor is in the region and refresh
;--     is PARTIAL, display from the row previously holding the cursor
;--     toward the bottom of the region -- thus, Ttree prior to this must
;--     not have changed.  Have this partial display terminate early if
;--     the first NL character encountered after the cursor is the same
;--     as the first one encountered during the last display -- thus,
;--     Ttree after this NL must not have changed.
;--
;--

(defun redraw-Ttree$ (reg motion refresh)

    (<- tdescr2$ (sel region (reg) descriptor))

    (Plet (top    (sel region (reg) top)
          bot    (sel region (reg) bot)
          left   (sel region (reg) left)
          right  (sel region (reg) right)
          Tt     (sel tdescr2$ Tt)
          cur    (sel tdescr2$ cursor)
          rc     nil
          newrow nil
         )

         (Pif (eql motion 'LARGE-CURSOR-MOTION) -->
             ;-- cursor is not expected to be in region, find out
             ;-- where it is and adjust ted descriptor if necessary
                 (<- rc (map-cursor-to-rc Tt top left bot right
                                          999999  ;lines-to-skip - to make
                                                  ;  sure cursor is reached
                                          (sel tdescr2$ bracket-mode)
                                          cur
                        )
                 )

                 (<- newrow (+ (cursor-r-of-mapped-cursor rc)
                               (- 999999
                                  (sel tdescr2$ lines-to-skip)
                               )
                            )
                 )
   
                 (Pif (or (< newrow top)
                         (> newrow bot)
                     ) -->
                     ;-- cursor is not on screen, must do full refresh
                         (<- (sel tdescr2$ lines-to-skip)
                             (max 0 (- (+ 999999 (cursor-r-of-mapped-cursor rc))
                                       (truncate (+ top bot) 2)
                                    )
                             )
                         )
                         (<- refresh 'FULL-REFRESH)
                  fi)
          fi)
        
         (Pif (eql refresh 'FULL-REFRESH) -->
             ;-- display entire Ttree, with no early exit
                 (<- rc (with-fast-redrawing (sel region (cur-region) window)
					     #'display-Ttree
					     Tt 
					     (sel region (reg) window)
					     top left bot right
					     (sel tdescr2$ lines-to-skip)
					     (sel tdescr2$ bracket-mode)
					     cur
					     nil	;-- early-exit-suffix
					     0	;-- early-exit-row
					     t	;-- blank-to-end-of-region
					     (sel tdescr2$ first-blank-row)
					     )
                 )
                 (<- (sel tdescr2$ cursor-r)  (cursor-r-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ cursor-c)  (cursor-c-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-suffix) (nl-suffix-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-row)    (nl-row-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ first-blank-row)
                     (first-blank-row-of-displayed-Ttree rc)
                 )

          || t -->
             ;-- display Ttree from cursor-r to end, with possible early exit
                 (<- rc (display-Ttree Tt
                                       (sel region (reg) window)
                                       (sel tdescr2$ cursor-r)
                                       left bot right
                                       (+ (sel tdescr2$ lines-to-skip)
                                          (- (sel tdescr2$ cursor-r) top)
                                       )
                                       (sel tdescr2$ bracket-mode)
                                       cur
                                       (sel tdescr2$ nl-suffix)
                                       (sel tdescr2$ nl-row)
                                       t        ;-- blank-to-end-of-region
                                       (sel tdescr2$ first-blank-row)
                        )
                 )
                 (<- (sel tdescr2$ cursor-r)  (cursor-r-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ cursor-c)  (cursor-c-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-suffix) (nl-suffix-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-row)    (nl-row-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ first-blank-row)
                     (first-blank-row-of-displayed-Ttree rc)
                 )
    
          fi)
             

         (Pif (null (sel tdescr2$ cursor-r)) -->
             ;-- Though it was likely, the cursor is not now in the region.
             ;-- It is below the region, so determine exactly where it is,
             ;-- adjust lines-to-skip to assure the cursor's presence, and
             ;-- redisplay the Ttree.
                 (<- rc (map-cursor-to-rc Tt top left bot right
                                          999999  ;lines-to-skip - to make
                                                  ;  sure cursor is reached
                                          (sel tdescr2$ bracket-mode)
                                          cur
                        )
                 )
                 (<- (sel tdescr2$ lines-to-skip)
                     (max 0 (- (+ 999999 (cursor-r-of-mapped-cursor rc))
                               (truncate (+ top bot) 2)
                            )
                     )
                 )
                 (<- rc (with-fast-redrawing (sel region (cur-region) window)
					     #'display-Ttree
					     Tt
					     (sel region (reg) window)
					     top left bot right
					     (sel tdescr2$ lines-to-skip)
					     (sel tdescr2$ bracket-mode)
					     cur
					     nil	;-- early-exit-suffix
					     0	;-- early-exit-row
					     t	;-- blank-to-end-of-region
					     (sel tdescr2$ first-blank-row)
					     )
                 )
                 (<- (sel tdescr2$ cursor-r)  (cursor-r-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ cursor-c)  (cursor-c-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-suffix) (nl-suffix-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-row)    (nl-row-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ first-blank-row)
                     (first-blank-row-of-displayed-Ttree rc)
                 )

          || (< (sel tdescr2$ cursor-r) top) -->
             ;-- Though it was likely, the cursor is not now in the region.
             ;-- It is above the region's top, so adjust lines-to-skip to
             ;-- assure the cursor's presence and redisplay the Ttree.
                 (<- (sel tdescr2$ lines-to-skip)
                     (max 0 (- (sel tdescr2$ lines-to-skip)
                               (- (truncate (+ top bot) 2)
                                  (sel tdescr2$ cursor-r)
                               )
                            )
                     )
                 )
                 (<- rc (with-fast-redrawing (sel region (cur-region) window)
					     #'display-Ttree
					     Tt
					     (sel region (reg) window)
					     top left bot right
					     (sel tdescr2$ lines-to-skip)
					     (sel tdescr2$ bracket-mode)
					     cur
					     nil	;-- early-exit-suffix
					     0	;-- early-exit-row
					     t	;-- blank-to-end-of-region
					     (sel tdescr2$ first-blank-row)
					     )
                 )
                 (<- (sel tdescr2$ cursor-r)  (cursor-r-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ cursor-c)  (cursor-c-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-suffix) (nl-suffix-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-row)    (nl-row-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ first-blank-row)
                     (first-blank-row-of-displayed-Ttree rc)
                 )

          fi)

         (movecursor (sel tdescr2$ cursor-r) (sel tdescr2$ cursor-c))

    )
)


;--
;-- redraw-cursor$ (reg: region#)
;--
;--     Based on the the Ttree cursor of the descriptor found in region reg,
;--     determine a new value for lines-to-skip and derive cursor-r,cursor-c
;--     so that the latter fall into the viewable region.  Reposition the
;--     screen cursor to cursor-r,cursor-c.
;--

(defun redraw-cursor$ (reg)

    (<- tdescr2$ (sel region (reg) descriptor))

    (Plet (top    (sel region (reg) top)
          bot    (sel region (reg) bot)
          left   (sel region (reg) left)
          right  (sel region (reg) right)
          Tt     (sel tdescr2$ Tt)
          cur    (sel tdescr2$ cursor)
          rc     nil
          newrow nil
         )

         (<- rc (map-cursor-to-rc Tt top left bot right
                                  999999  ;lines-to-skip - to make sure
                                          ;                cursor is reached
                                  (sel tdescr2$ bracket-mode)
                                  cur
                )
         )

         (<- newrow (+ (cursor-r-of-mapped-cursor rc)
                       (- 999999
                          (sel tdescr2$ lines-to-skip)
                       )
                    )
         )

         (Pif (or (< newrow top)
                 (> newrow bot)
             ) -->
             ;-- cursor is not on screen, must redraw it
                 (<- (sel tdescr2$ lines-to-skip)
                     (max 0 (- (+ 999999 (cursor-r-of-mapped-cursor rc))
                               (truncate (+ top bot) 2)
                            )
                     )
                 )
                 (<- rc (with-fast-redrawing (sel region (cur-region) window)
					     #'display-Ttree
					     Tt
					     (sel region (reg) window)
					     top left bot right
					     (sel tdescr2$ lines-to-skip)
					     (sel tdescr2$ bracket-mode)
					     cur
					     nil	;-- early-exit-suffix
					     0	;-- early-exit-row
					     t	;-- blank-to-end-of-region
					     (sel tdescr2$ first-blank-row)
					     )
                 )
                 (<- (sel tdescr2$ cursor-r)  (cursor-r-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ cursor-c)  (cursor-c-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-suffix) (nl-suffix-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ nl-row)    (nl-row-of-displayed-Ttree rc))
                 (<- (sel tdescr2$ first-blank-row)
                     (first-blank-row-of-displayed-Ttree rc)
                 )

          || t -->
             ;-- cursor is on screen, just get coordinates
                 (<- (sel tdescr2$ cursor-r)  newrow)
                 (<- (sel tdescr2$ cursor-c)  (cursor-c-of-mapped-cursor rc))
                 (<- (sel tdescr2$ nl-suffix) (nl-suffix-of-mapped-cursor rc))
                 (Pif (sel tdescr2$ nl-suffix) -->
                     (<- (sel tdescr2$ nl-row)
                         (+ (nl-row-of-mapped-cursor rc)
                            (- 999999
                               (sel tdescr2$ lines-to-skip)
                            )
                         )
                     )
                  fi)
          fi)

         (movecursor (sel tdescr2$ cursor-r) (sel tdescr2$ cursor-c))
    )
)

