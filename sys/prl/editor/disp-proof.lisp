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

;----------------------------;
;                            ;
;   PROOF LAYOUT ROUTINES    ;
;                            ;
;----------------------------;


(global current-line$)      ;-- line number in view of next entry to layout

(defvar *computing-red-or-lib-display-of-proof-p* nil)


;--
;-- layout-proof-level (reg:region#)
;--
;--     For the specified region, layout the current-level
;--     into level-map.  If level-cursor is defined, this
;--     allows the level to be displayed.
;--

(defun layout-proof-level (reg)

    (<- rdescr$ (sel region (reg) descriptor))
    
    (Plet (current-level (sel rdescr$ current-level)
          left          (sel region (reg) left)
          right         (sel region (reg) right)
          body          nil
          body-len      0
          major         0
          label         nil
	  *computing-red-or-lib-display-of-proof-p* T
         )
        
         ;-- Calculate the display form of the proof cursor
             (<- (sel rdescr$ displayed-cursor-body)
                 (proof-cursor-to-prlstr (sel rdescr$ proof-cursor) left right)
             )


         (Pif (null current-level) -->
             ;-- root goal is not known good -- displayed view
             ;-- should show only an indicator for root goal

                 (Pif (or (equal (sel rdescr$ thm goal-body) the-null-Ttree)
                         (equal (sel rdescr$ thm goal-body) raw-object-Ttree)
                     ) -->
                     ;-- goal is not present
                         (<- body (cons 'Ttree '#.(istring "<main proof goal>")))

                  || t -->
                     ;-- goal is present and is bad
                         (<- body (cons 'Ttree '#.(istring "??bad main proof goal??")))

                  fi)

                 (<- (sel rdescr$ level-map)
                     (list (level-map-entry
                                (level-cursor '(GOAL) '(CONCL))
                                1   ;-- start line
                                (layout-Ttree$
                                    body
                                    left
                                    right
                                )   ;-- end line
                                body
                                label
                           )
                     )
                 )

                 (<- (sel rdescr$ first-displayed-entry)
                     (car (sel rdescr$ level-map))
                 )

          || t -->
             ;-- root goal is good - display this level normally

                 (<- current-line$ 1)
                 (<- (sel rdescr$ level-map) nil)
                 (layout-goal$ '(GOAL) current-level left right)
                 (Pif (null (rule-of-proof-tree current-level)) -->
                     ;-- layout missing or bad rule

                         (Pif (null-Ttree
                                 (rule-body-of-proof-tree current-level)
                             ) -->
                             (<- body (cons 'Ttree '#.(istring "<refinement rule>")))

                          || t -->
                             (<- body (cons 'Ttree '#.(istring "??bad refinement rule??")))

                          fi)

                         (<- (sel rdescr$ level-map)
                             (cons (level-map-entry
                                        (level-cursor '(RULE) nil)
                                        (1+ current-line$)
                                        (+ current-line$
                                           (layout-Ttree$
                                                 body
                                                 (+ left 3)
                                                 right
                                           )
                                        )
                                        body
                                        '#.(istring "BY ")
                                   )
                                   *-*
                             )
                         )

                  || t -->
                     ;-- rule is good -- layout it and the subgoals

                         (<- body (Ttree-for-rule-of-proof current-level))
                         (<- body-len (layout-Ttree$ body (+ left 3) right))
                         (<- (sel rdescr$ level-map)
                             (cons (level-map-entry
                                        (level-cursor '(RULE) nil)
                                        (1+ current-line$)
                                        (+ current-line$ body-len)
                                        body
                                        '#.(istring "BY ")
                                   )
                                   *-*
                             )
                         )
                         (<- current-line$ (+ *-* body-len 2))
                         (<- major 1)
                         (for (subgoal$ in 
                                  (children-of-proof-tree current-level)
                              )
                              (do
                                  (layout-goal$ (list 'SUBGOAL major)
                                                subgoal$
                                                left
                                                right
                                  )
                                  (<- major (1+ *-*))
                                  ;-- leave a blank line
                                      (<- current-line$ (1+ *-*))
                              )
                         )
                  fi)

          fi)

         (<- (sel rdescr$ level-map) (nreverse *-*))

    )
)

;--
;-- layout-goal$ (major:major-stopping-point, proof:proof-tree,
;--               left:integer, right:integer)
;--
;--     Layout the goal contained in the proof-tree (and named by the
;--     major-stopping-point) with indent and label appropriate to major,
;--     in a view of width left..right.  Increase current-line$ by the
;--     length of the layout and cons the laid out entries onto the front
;--     of rdescr$'s level-map in reverse order.
;--

(defun layout-goal$ (major proof left right)

    (Plet (body      nil     ;-- Ttree of the level-map-entry being built
          body-len  0       ;-- number of lines required to display body
          assum-num 0       ;-- the assumption number of body
          label     nil     ;-- the label for body in the view
          spaces    nil     ;-- list of blanks of same length as label
          hidden    nil     ;-- Is assumption number asssum-num hidden?
          laid-out-assum-yet? nil   
         )

        (Pif (eql (car major) 'SUBGOAL) -->
            (<- label (append
                          (istring (cadr major))
                          (red-status-form (status-of-proof-tree proof))
                          '#.(istring " ")
                      )
            )
            (<- spaces (mapcar #'(lambda (c) #.(ichar #\space)) label))
         fi)

						;-- layout assumptions

             (<- assum-num 1)
	     (<- laid-out-assum-yet? nil)
             (for (asm$ in (assumptions-of-proof-tree proof))
                  (do
		    (cond
		      ((not (and (eql 'SUBGOAL (car major))
				 (member
				   asm$
				   (assumptions-of-proof-tree
				     (sel rdescr$ current-level)))))
		       (<- hidden
			   (member assum-num (hidden-of-proof-tree proof))
			   )
		       (<- body (declaration-to-Ttree asm$))
		       (<- label (append
				   (Pif (not laid-out-assum-yet?) -->
				       (<- laid-out-assum-yet? t)
				       label
				       || t -->
				       spaces
				       fi)
				   (Pif hidden --> (list #.(ichar #\[))
				       || t --> nil
				       fi)
				   (istring assum-num)
				   (Pif hidden --> (list #.(ichar #\]))
				       || t --> nil
				       fi)
				   '#.(istring ". ")
				   )
			   )
		       (<- body-len (layout-Ttree$ body
						   (+ left (length label))
						   right
						   )
			   )
		       (<- (sel rdescr$ level-map)
			   (cons (level-map-entry
				   (level-cursor major
						 (list 'ASSUM assum-num)
						 )
				   current-line$
				   (+ current-line$ body-len -1)
				   body
				   label
				   )
				 *-*
				 )
			   )
		       (<- current-line$ (+ *-* body-len))))
                      (<- assum-num (1+ *-*))
                  )
             )

						;-- layout conclusion

             (<- body (term-to-Ttree (conclusion-of-proof-tree proof)))
             (<- label
                 (append
                     (Pif laid-out-assum-yet? -->
                         spaces
                      || t -->
                         label
                      fi)
                     '#.(istring ">> ")
                 )
             )
             (<- body-len (layout-Ttree$ body (+ left (length label)) right))
             (<- (sel rdescr$ level-map)
                 (cons (level-map-entry (level-cursor major '(CONCL))
                                        current-line$
                                        (+ current-line$ body-len -1)
                                        body
                                        label
                       )
                       *-*
                 )
             )
             (<- current-line$ (+ *-* body-len))

    )
)

             

;--
;-- layout-Ttree$ (Tt:Ttree, left:integer, right:integer)
;--
;--     Return the number of lines required to display Tt in
;--     a region of width left..right.
;--

(defun layout-Ttree$ (Tt left right)

    (Plet (rc (map-cursor-to-rc Tt
                               0            ;-- top
                               left
                               0            ;-- bot
                               right
                               999999       ;-- lines-to-skip
                               nil          ;-- bracket-mode
                               (list 
                                 (length Tt)
                               )            ;-- cursor for end of Tt
             )
         )

         (max 1
              (+ 999999
                (cursor-r-of-mapped-cursor rc)
                (Pif (equal left (cursor-c-of-mapped-cursor rc)) --> 0
                 || t --> 1
                 fi)
              )
         )
    )
)



;-----------------------------;
;                             ;
;   PROOF DISPLAY ROUTINES    ;
;                             ;
;-----------------------------;


;--
;--
;--
;--
;--
;--
;--

(defun display-proof-level (reg)
  (with-fast-redrawing (sel region (reg) window)
		       #'display-proof-level$ reg))

(defun display-proof-level$ (reg)

    (<- rdescr$ (sel region (reg) descriptor))

    (Plet (top               (sel region (reg) top)
          bot               (sel region (reg) bot)
          left              (sel region (reg) left)
          right             (sel region (reg) right)
          level-map         (sel rdescr$ level-map)
          level-cursor      (sel rdescr$ level-cursor)
          level-cursor-entry nil  ;-- entry in level-map for level-cursor
          first-line-to-show 0    ;-- first line of level to show in view so
                                  ;--   that level-cursor-entry is centered
          display-list       nil  ;-- suffix of level-map starting at first
                                  ;--   entry after first-line-to-show
	  *computing-red-or-lib-display-of-proof-p* t
         )

        (selectw (sel region (reg) window))

        ;-- set level-cursor-entry to the entry in level-map for level-cursor
            (<- level-cursor-entry level-map)
            (Ploop
                (while (not (equal-level-cursors
                                (level-cursor-of-level-map-entry
                                    (car level-cursor-entry)
                                )
                                level-cursor
                            )
                       )
                )
                (do
                    (<- level-cursor-entry (cdr *-*))
                )
            )
            (<- level-cursor-entry (car *-*))

        (<- first-line-to-show
            (- (start-of-level-map-entry level-cursor-entry)
               (max 1
                    (truncate (- (- bot top)
                          (- (end-of-level-map-entry level-cursor-entry)
                             (start-of-level-map-entry level-cursor-entry)
                          )
                       )
                       2
                    )
               )
            )
        )

        ;-- set display-list to the portion of level-map from the first
        ;-- entry with starting line >= first-line-to-show to the end
            (<- display-list level-map)
            (Ploop
                (while (> first-line-to-show
                                 (start-of-level-map-entry
                                       (car display-list)
                                 )
                       )
                )
                (do
                    (<- display-list (cdr *-*))
                )
            )

        (<- (sel rdescr$ first-displayed-entry) (car display-list))
        
        ;-- Clear display and print the proof-cursor and the status of the
        ;-- current proof node.
	(clear-window)
            (movecursor 0 0)
            (Plet (status-form
                     (Pif (null (sel rdescr$ current-level)) -->
                         (Pif (null-Ttree (sel rdescr$ thm goal-body)) -->
                             '#.(istring "?")
                          || t -->
                             (red-status-form 'BAD)
                          fi)
                       || t -->
                          (red-status-form
                              (status-of-proof-tree
                                  (sel rdescr$ current-level)
                              )
                          )
                      fi)
                 )
                (putstr
                    (append
                        status-form
                        '#.(istring " ")
                        (sel rdescr$ displayed-cursor-body)
                    )
                )
            )

        ;-- display the display-list until the list ends or
        ;-- we run out of lines (in the view) on the screen
            (Ploop
                (local line-num 1     ;-- line of window to place next entry
                )
                (while (and (not (null display-list))
                            (not (> line-num bot))
                       )
                )
                (do
                    (movecursor line-num 0)
                    (putstr (label-of-level-map-entry (car display-list)))
                    (display-Ttree (body-of-level-map-entry (car display-list))
                                   (sel region (reg) window)
                                   line-num
                                   (+ left
                                      (length (label-of-level-map-entry
                                                    (car display-list)
                                              )
                                      )
                                   )
                                   bot
                                   right
                                   0    ;-- lines-to-skip
                                   nil  ;-- bracket-mode
                                   nil  ;-- cursor
                                   nil  ;-- early-exit-suffix
                                   nil  ;-- early-exit-row
                                   nil  ;-- blank-to-end-of-region
                                   nil  ;-- first-blank-row
                    )
                    (Pif (not (null (cdr display-list))) -->
                        (<- line-num
                            (+ *-*
                               (- (start-of-level-map-entry (cadr display-list))
                                  (start-of-level-map-entry (car display-list))
                               )
                            )
                        )
                     fi)
                    (<- display-list (cdr *-*))
                )
            )

        ;-- position the screen cursor
            (movecursor
                (1+
                    (- (start-of-level-map-entry level-cursor-entry)
                       (start-of-level-map-entry
                           (sel rdescr$ first-displayed-entry)
                       )
                       
                    )
                )
                (length (label-of-level-map-entry level-cursor-entry))
            )

    )
)


;--
;--
;--
;--
;--
;--

(defun move-displayed-level-cursor (reg)

    (<- rdescr$ (sel region (reg) descriptor))

    (Plet (level-cursor       (sel rdescr$ level-cursor)
          level-cursor-entry (sel rdescr$ level-map)
         )

        (selectw (sel region (reg) window))

        ;-- set level-cursor-entry to the entry of level-map for level-cursor
            (Ploop
                (while (not (equal-level-cursors
                                (level-cursor-of-level-map-entry
                                    (car level-cursor-entry)
                                )
                                level-cursor
                            )
                       )
                )
                (do
                    (<- level-cursor-entry (cdr *-*))
                )
            )
            (<- level-cursor-entry (car *-*))

        (Pif (or (< (start-of-level-map-entry level-cursor-entry)
                       (start-of-level-map-entry
                           (sel rdescr$ first-displayed-entry)
                       )
                )
                (and (>
                         (end-of-level-map-entry level-cursor-entry)
                         (+ (start-of-level-map-entry
                                (sel rdescr$ first-displayed-entry)
                            )
                            (- (sel region (reg) bot)
                               (1+ (sel region (reg) top))
                            )
                         )
                     )
                     (not (equal level-cursor-entry
                                 (sel rdescr$ first-displayed-entry)
                          )
                     )
                )
            ) -->
            ;-- level-cursor-entry is not maximally visible
                (display-proof-level reg)

         || t -->
            ;-- level-cursor-entry is visible, just move the cursor
                (movecursor
                    (1+
                        (- (start-of-level-map-entry level-cursor-entry)
                           (start-of-level-map-entry
                               (sel rdescr$ first-displayed-entry)
                           )
                        )
                    )
                    (length
                        (label-of-level-map-entry level-cursor-entry)
                    )
                )

         fi)

    )
)



;-----------------------------------------;
;                                         ;
;   LEVEL CURSOR MANIPULATION ROUTINES    ;
;                                         ;
;-----------------------------------------;

;-- 
;-- equal-level-cursors (lc1,lc2:level-cursors)
;-- 
;--     Returns t iff lc2 is a level cursor which means the same thing as
;--     lc1.
;-- 

(defun equal-level-cursors (lc1 lc2)

    (equal lc1 lc2)

)
            

;--
;-- slide-level-cursor-far (reg:region#, direction:{UP,DOWN})
;--
;--     Move the level cursor 'several' minor stopping points in
;--     specified direction.  Motion is to the next major stopping
;--     point, except that at the bottom the cursor may end at the
;--     last minor stopping point in the level.
;--

(defun slide-level-cursor-far (reg direction)

    (<- rdescr$ (sel region (reg) descriptor))

    (Pif (eql direction 'DOWN) -->

        (Plet (last-cursor (sel rdescr$ level-cursor)
             )
 
            (slide-level-cursor reg direction)

            (Ploop
                (while (and (let ((major (major-of-level-cursor
					   (sel rdescr$ level-cursor)))
				  (minor (minor-of-level-cursor
					   (sel rdescr$ level-cursor))))
			      (not (or (equal major '(RULE))
				       (and (equal (car major) 'SUBGOAL)
					    (equal minor '(CONCL))))))
                            (not (equal-level-cursors
                                     last-cursor
                                     (sel rdescr$ level-cursor))))
                )
                (do (<- last-cursor (sel rdescr$ level-cursor))
                    (slide-level-cursor reg direction)
                )
            )
    
        )

     || t --> ;-- direction is 'UP

        (Plet (new-cursor nil
             )

            (slide-level-cursor reg direction)
            (<- new-cursor (sel rdescr$ level-cursor))
            (slide-level-cursor reg direction)

            (Ploop
                (while (and (equal (major-of-level-cursor new-cursor)
                                   (major-of-level-cursor
                                        (sel rdescr$ level-cursor)
                                   )
                            )
                            (not (equal-level-cursors
                                     new-cursor
                                     (sel rdescr$ level-cursor)
                                 )
                            )
                       )
                )
                (do
                    (<- new-cursor (sel rdescr$ level-cursor))
                    (slide-level-cursor reg direction)
                )
            )
            
            (<- (sel rdescr$ level-cursor) new-cursor)

        )

     fi)

)


;--
;-- slide-level-cursor (reg:region#, direction:{UP,DOWN})
;--
;--     Move the level-cursor in region reg UP or DOWN to the next
;--     minor stopping point.  Leave it alone if it is at the farthest
;--     point in the given direction.
;--

(defun slide-level-cursor (reg direction)

    (<- rdescr$ (sel region (reg) descriptor))

    (Plet (level-map-tail    (sel rdescr$ level-map)
          level-cursor      (sel rdescr$ level-cursor)
          prev-entry        nil
         )

        ;-- set level-map-tail to the part of the level-map starting
        ;-- with level-cursor, and prev-entry to the level-map-entry
        ;-- just prior to the tail
            (Ploop
                (while (not (equal-level-cursors
                                (level-cursor-of-level-map-entry
                                    (car level-map-tail)
                                )
                                level-cursor
                            )
                       )
                )
                (do
                    (<- prev-entry (car level-map-tail))
                    (<- level-map-tail (cdr *-*))
                )
            )

        ;-- based on direction, set the level cursor appropriately
            (Pif (eql direction 'UP) -->
                (Pif (not (null prev-entry)) -->
                    (<- (sel rdescr$ level-cursor)
                        (level-cursor-of-level-map-entry prev-entry)
                    )
                 fi)

             || t -->
                (Pif (not (null (cdr level-map-tail))) -->
                    (<- (sel rdescr$ level-cursor)
                        (level-cursor-of-level-map-entry (cadr level-map-tail))
                    )
                 fi)

             fi)

    )
)



;-------------------------------------;
;                                     ;
;   SCREEN CURSOR MAPPING ROUTINES    ;
;                                     ;
;-------------------------------------;


;--
;--
;--
;--
;--

(defun map-rc-to-level-cursor (reg row col)
  (declare (ignore col))

    (<- rdescr$ (sel region (reg) descriptor))

    (Plet (entry (map-row-to-level-map-entry$ row)
         )

        (Pif (null entry) -->
            nil

         || t -->
            (level-cursor-of-level-map-entry entry)

         fi)

    )
)


;--
;--
;--
;--
;--

(fluid mapped-entry$)

(defun map-rc-to-formula (reg row col)
  (declare (ignore col))

    (<- rdescr$ (sel region (reg) descriptor))
    
    (Plet (mapped-entry$ (map-row-to-level-map-entry$ row)
         )

        (Pif (or (null mapped-entry$)
                (eql 'RULE
                    (car (major-of-level-cursor
                            (level-cursor-of-level-map-entry mapped-entry$)
                         )
                    )
                ) ;-- rc point to the rule
            ) -->
            nil

         || (eql 'CONCL
                (car (minor-of-level-cursor
                         (level-cursor-of-level-map-entry mapped-entry$)
                     )
                )

            ) -->
            ;-- rc point to a conclusion
                (list '(CONCL) (body-of-level-map-entry mapped-entry$))

         || t -->
            ;-- rc point to an assumption -- if this assumption is unique
            ;-- then return it as is, else append an assum# to its Ttree
                (Pif (Psome
                        #'(lambda (entry)
                            (and (equal
                                     (major-of-level-cursor
                                         (level-cursor-of-level-map-entry
                                               mapped-entry$
                                         )
                                     )
                                     (major-of-level-cursor
                                         (level-cursor-of-level-map-entry
                                               entry
                                         )
                                     )
                                 ) ;-- we have an entry in the same goal
                                 (eql 'ASSUM
                                     (car (minor-of-level-cursor
                                              (level-cursor-of-level-map-entry
                                                    entry
                                              )
                                          )
                                     )
                                 ) ;-- it too is an assumption
                                 (not (eql entry mapped-entry$)
                                 ) ;-- it isn't this very same assumption
                                 (equal (body-of-level-map-entry entry)
                                        (body-of-level-map-entry mapped-entry$)
                                 ) ;-- yet it has the same Ttree form
                            )
                         )
                        (sel rdescr$ level-map)
                    ) -->
                    ;-- this assumption has another that looks the same
                        (list (list 'ASSUM
                                    (cadr (minor-of-level-cursor
                                              (level-cursor-of-level-map-entry
                                                    mapped-entry$
                                              )
                                          )
                                    )
                              )
                              (append (body-of-level-map-entry mapped-entry$)
                                      '#.(istring "[")
                                      (istring
                                          (minor-of-level-cursor
                                              (level-cursor-of-level-map-entry
                                                    mapped-entry$
                                              )
                                          )
                                      )
                                      '#.(istring "]")
                              )
                        )

                 || t -->
                    ;-- this assumption is unique
                        (list (list 'ASSUM
                                    (cadr (minor-of-level-cursor
                                              (level-cursor-of-level-map-entry
                                                    mapped-entry$
                                              )
                                          )
                                    )
                              )
                              (body-of-level-map-entry mapped-entry$)
                        )

                 fi)

         fi)
    )
)


;--
;--
;--
;--
;--

(fluid row-to-map$)
(fluid logical-row$)

(defun map-row-to-level-map-entry$ (row-to-map$)

    (Plet (logical-row$ (+ (1- row-to-map$)
                          (start-of-level-map-entry
                              (sel rdescr$ first-displayed-entry)
                          )
                       )
         )

        (Plet (level-map-tail (Psome #'(lambda (entry)
                                        (not (<
                                                 (end-of-level-map-entry entry)
                                                 logical-row$
                                             )
                                        )
                                    )
                                   (sel rdescr$ level-map)
                             )
             )
    
            (Pif (null level-map-tail) -->
                nil
    
             || (not (> (start-of-level-map-entry (car level-map-tail))
                               logical-row$
                     )
                ) -->
                (car level-map-tail)
    
             || t -->
                nil
            
             fi)
        )
    )
)


;-- proof-cursor-to-prlstr (proof-cursor left right)
;--
;--   Return a prlstr which is the display form of the current cursor.
;--   Display only as much cursor as will fit on the line (left..right): if
;--   necessary, truncate the first entries in the cursor and display '...'.
;--   Note below we need two columns for status of proof, so we can't use
;--   them for the cursor.

(defun proof-cursor-to-prlstr (proof-cursor left right)
    (Plet (rpc   (reverse proof-cursor)   ;-- we want it from last to first.
          width (- right left 1)         ;-- max allowable length of line.
          ssf   nil                      ;-- computed string so far.
          lssf  nil                      ;-- length of ssf.
         )

         (Pif (null rpc) --> (<- ssf nil)
          || t          --> (<- ssf (istring (car rpc)))
          fi)

         (<- lssf (length ssf))

         (proof-cursor-to-prlstr$ (cdr rpc) width ssf lssf)
    )
)

;-- proof-cursor-to-prlstr$
;--
;--   The string so far must have length <= width - 4.  The first time through,
;--   we believe it because red windows must be at least 10 cols wide.

(defun proof-cursor-to-prlstr$ (rpc width ssf lssf)

    (Plet (index  nil   ;-- prlstr for first number in rpc.
          lindex nil   ;-- length of index.
         )
         (Pif (null rpc) --> (append '#.(istring "top ") ssf)
          || t -->
             (<- index  (append (istring (car rpc)) '#.(istring " ")))
             (<- lindex (length index))

             (Pif (< (+ lssf lindex 3) width) -->
                 (proof-cursor-to-prlstr$ (cdr rpc) width (append index ssf)
                                          (+ lindex lssf)
                 )
              || t --> (append '#.(istring "... ") ssf)
              fi)
          fi)
    )
)

;--------------------------------------------------;
;                                                  ;
;   DATA STRUCTURE TO TTREE CONVERSION ROUTINES    ;
;                                                  ;
;--------------------------------------------------;


;--
;-- Ttree-for-rule-of-proof (proof:proof-tree)
;--
;--     Return a Ttree for displaying the rule of proof.
;--

(defun Ttree-for-rule-of-proof (proof)

    (Pif (or (null (rule-of-proof-tree proof))
            (not (null-Ttree (rule-body-of-proof-tree proof)))
        ) -->
        (rule-body-of-proof-tree proof)

     || t -->
        (rule-to-Ttree (rule-of-proof-tree proof))

     fi)

)


;--
;--
;--
;--
;--
(defun pf-to-show-Ttree (pt)
    ;--
    ;-- Take a proof tree an return a Ttree suitable for SHOWing it as a goal:
    ;--
    ;--     hyp,
    ;--     ...,
    ;--     hyp
    ;--     >> conclusion
    ;--

    (Plet (h nil   ;-- Ttree for hypotheses.
          c nil   ;-- Ttree for conclusion.
         )

         (<- h (declaration-list-to-Ttree (assumptions-of-proof-tree pt)))
         (<- c (term-to-Ttree (conclusion-of-proof-tree pt)))

         (append (Pif (null-Ttree h) --> () || t --> (cons #.(ichar #\space) (cdr h)) fi)

		 (list NL)

                 '#.(istring ">> ")

                 (cdr c)
         )
)   )


(defun declaration-list-to-Ttree (forms)
    ;--
    ;-- Build a Ttree for the declaration list by concatenating the Ttrees for
    ;-- the individual declarations.  (We separate the Ttrees with commas.)
    ;--

    (Pif (null forms) --> '(Ttree)
     || (null (cdr forms)) --> (declaration-to-Ttree (car forms))
     || t -->
        (append (declaration-to-Ttree (car forms))
                (list NL)
                (cdr (declaration-list-to-Ttree (cdr forms)))
        )
     fi)
)

(defun declaration-to-Ttree (decl)
    (Pif (Ttree-of-declaration decl) -->
        (Ttree-of-declaration decl)
     || (null (id-of-declaration decl)) -->
        (term-to-Ttree (type-of-declaration decl))

     || t -->
        (cons 'Ttree (append (istring (id-of-declaration decl))
                             '#.(istring ": ")
                             (cdr (term-to-Ttree (type-of-declaration decl)))
                     )
        )
     fi)
)

     
(defvar *term-to-ttree-buffer* (make-array 1000 :fill-pointer 0 :adjustable t)
  "An array holding the intermediate results of term-to-ttree")

(defun add-to-ttt-buffer (x)
  ;; Add an item to *term-to-ttree-buffer*.
  (vector-push-extend x *term-to-ttree-buffer*))

(defun add-string (s)
  ;; Add the characters of the string s to the buffer.
  (let ((len (length s)))
    (dotimes (i len)
      (add-to-ttt-buffer (ichar (aref s i))))))
 
(defun add-number (n)
  ;; Add the characters representing the number n to the buffer.
  (add-string (princ-object-to-string n)))

(defun add-list (l)
  ;; Add the elements of the list l to the buffer.
  (dolist (x l) (add-to-ttt-buffer x)))

(defun add-ttree (ttree)
  ;; Add the elements of the Ttree ttree to the buffer (excluding
  ;; the initial 'Ttree).
  (add-list (cdr ttree)))

(defun add-atom (a)
  ;; Add the characters of the print name of the atom a to the buffer.
  (add-string (symbol-name a)))

(defun term-to-ttree (term)
  ;; Returns a Ttree which represents the display form of 'term'.
  (setf (fill-pointer *term-to-ttree-buffer*) 0)
  (term-to-ttree$ term 0)
  (concatenate 'list '(Ttree) *term-to-ttree-buffer*))

(defun term-to-Ttree-with-parens (term)
  ;; Returns a Ttree which represents the display form of 'term.
  ;; Outermost term will be parenthesized if there is any context in
  ;; which it should be parenthesized, so call term-to-ttree$
  ;; with parent-precedence set to +infinity.  For example, identifiers,
  ;; numbers, spread(...) never need parens, but a*b, \x.b, do.
  (setf (fill-pointer *term-to-ttree-buffer*) 0)
  (term-to-ttree$ term 10000)
  (concatenate 'list '(Ttree) *term-to-ttree-buffer*))

(defun term-to-ttree$ (term parent-prec)
  ;; Returns a Ttree (without its first element) which represents the
  ;; display form of 'term'.  If parent-prec > precedence of the main
  ;; connective of 'term', the Ttree will be parenthesized.
  (let* ((lprec (get (kind-of-term term) 'lprecedence))
	 (rprec (get (kind-of-term term) 'rprecedence))
	 (need-parens-p
	   (or (and lprec
		    (not (< parent-prec lprec)))
	       (and rprec
		    (not (< parent-prec rprec))))))
    (when need-parens-p (add-string "("))
    (if (Ttree-of-term term)
	(add-ttree (Ttree-of-term term))
	(case (kind-of-term term)
	  (INT (add-string "int"))
	  (OBJECT (add-string "object"))
	  (ATOM (add-string "atom"))
	  ((NIL) (add-string "nil"))
	  (VOID (add-string "void"))
	  (AXIOM (add-string "axiom"))
	  (INCOMPLETE (add-string "incomplete"))
	  (TERM-OF-THEOREM
	   (add-string "term_of(")
	   (add-atom (name-of-term-of-theorem-term term))
	   (add-string ")"))
	  ((ATOMEQ INTEQ INTLESS)
	   (add-string 
	     (case (kind-of-term term)
	       (ATOMEQ "atom_eq(")
	       (INTEQ "int_eq(")
	       (INTLESS "less(")))
	   (term-to-ttree$ (leftterm-of-decision-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (rightterm-of-decision-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (if-term-of-decision-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (else-term-of-decision-term term) 0)
	   (add-string ")"))
	  (EQUAL
	   (term-to-ttree$ (car (terms-of-equal-term term)) (1+ lprec))
	   (dolist (term (cdr (terms-of-equal-term term)))
	     (add-string "=")
	     (term-to-ttree$ term (1+ lprec)))
	   (add-string " in ")
	   (term-to-ttree$ (type-of-equal-term term) (1+ lprec)))
	  (LIST
	   (term-to-ttree$ (type-of-list-term term) lprec)
	   (add-string " list"))
	  (LAMBDA
	   (add-string "\\") #|"|#
	   (add-atom (bound-id-of-lambda-term term))
	   (add-string ".")
	   (term-to-ttree$ (term-of-lambda-term term) rprec))
	  (UNION
	   (term-to-ttree$ (lefttype-of-union-term term) lprec)
	   (add-string "|")
	   (term-to-ttree$ (righttype-of-union-term term) rprec))
	  (PRODUCT
	   (when (bound-id-of-product-term term)
	     (add-atom (bound-id-of-product-term term))
	     (add-string ":"))
	   (term-to-ttree$ (lefttype-of-product-term term) lprec)
	   (add-string "#")
	   (term-to-ttree$ (righttype-of-product-term term) rprec))
	  (FUNCTION
	   (when (bound-id-of-function-term term)
	     (add-atom (bound-id-of-function-term term))
	     (add-string ":"))
	   (term-to-ttree$ (lefttype-of-function-term term) lprec)
	   (add-string "->")
	   (term-to-ttree$ (righttype-of-function-term term) rprec))
	  (PARFUNCTION
	   (when (bound-id-of-parfunction-term term)
	     (add-atom (bound-id-of-parfunction-term term))
	     (add-string ":"))
	   (term-to-ttree$ (lefttype-of-parfunction-term term) lprec)
	   (add-string "+>")
	   (term-to-ttree$ (righttype-of-parfunction-term term) rprec))
	  (SET
	   (add-string "{")
	   (when (bound-id-of-set-term term)
	     (add-atom (bound-id-of-set-term term))
	     (add-string ":"))
	   (term-to-ttree$ (lefttype-of-set-term term) lprec)
	   (add-string "|")
	   (term-to-ttree$ (righttype-of-set-term term) rprec)
	   (add-string "}"))
	  (QUOTIENT
	   (add-string "(")
	   (add-atom (car (bound-ids-of-quotient-term term)))
	   (add-string ",")
	   (add-atom (cadr (bound-ids-of-quotient-term term)))
	   (add-string "):")
	   (term-to-ttree$ (lefttype-of-quotient-term term) lprec)
	   (add-string "//")
	   (term-to-ttree$ (righttype-of-quotient-term term) rprec))
	  (PAIR
	   (add-string "<")
	   (term-to-ttree$ (leftterm-of-pair-term term) 0)
	   (add-string ",")
	   (term-to-ttree$ (rightterm-of-pair-term term) 0)
	   (add-string ">"))
	  (SPREAD
	   (add-string "spread(")
	   (term-to-ttree$ (value-of-spread-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (term-of-spread-term term) 0)
	   (add-string ")"))
	  (DECIDE
	   (add-string "decide(")
	   (term-to-ttree$ (value-of-decide-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (leftterm-of-decide-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (rightterm-of-decide-term term) 0)
	   (add-string ")"))
	  (BOUND-ID-TERM
	   (add-atom (car (bound-ids-of-bound-id-term term)))
	   (dolist (rest (cdr (bound-ids-of-bound-id-term term)))
	     (add-string ",")
	     (add-atom rest))
	   (add-string ".")
	   (term-to-ttree$ (term-of-bound-id-term term) 0))
	  (IND
	   (add-string "ind(")
	   (term-to-ttree$ (value-of-ind-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (downterm-of-ind-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (baseterm-of-ind-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (upterm-of-ind-term term) 0)
	   (add-string ")"))
	  (LIST-IND
	   (add-string "list_ind(")
	   (term-to-ttree$ (value-of-list-ind-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (baseterm-of-list-ind-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (upterm-of-list-ind-term term) 0)
	   (add-string ")"))
	  (BOUND-ID-LIST
	   (do ((bound-ids (bound-ids-of-bound-id-list-term term) (cdr bound-ids))
		(terms (term-list-of-bound-id-list-term term)))
	       ((null bound-ids))
	     (add-atom (first bound-ids))
	     (add-string ",")
	     (term-to-ttree$ (first terms) 0)))
	  (RECURSIVE
	   (add-string "rec(")
	   (term-to-ttree$ (bound-id-list-term-of-recursive-term term) 0)
	   (add-string ";")
	   (when (fix-term-of-recursive-term term)
	     (term-to-ttree$ (fix-term-of-recursive-term term) 0)
	     (add-string ";"))
	   (add-atom (id-of-recursive-term term))
	   (add-string ",")
	   (term-to-ttree$ (term-of-recursive-term term) 0)
	   (add-string ")"))
	  (SIMPLE-REC
	   (add-string "rec(")
	   (add-atom (bound-id-of-simple-rec-term term))
	   (add-string ".")
	   (term-to-ttree$ (term-of-simple-rec-term term) 0)
	   (add-string ")"))
	  (FIX
	   (add-string "fix(")
	   (term-to-ttree$ (bound-id-list-term-of-fix-term term) 0)
	   (add-string ";")
	   (add-atom (id-of-fix-term term))
	   (add-string ")"))
	  (REC-IND
	   (add-string "rec_ind(")
	   (term-to-ttree$ (term-of-rec-ind-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (bound-id-list-term-of-rec-ind-term term) 0)
	   (add-string ";")
	   (add-atom (id-of-rec-ind-term term))
	   (add-string ")"))
	  (SIMPLE-REC-IND
	   (add-string "rec_ind(")
	   (term-to-ttree$ (value-of-simple-rec-ind-term term) 0)
	   (add-string ";")
	   (term-to-ttree$ (term-of-simple-rec-ind-term term) 0)
	   (add-string ")"))
	  (VAR (add-atom (id-of-var-term term)))
	  (APPLY
	   (term-to-ttree$ (function-of-apply-term term) lprec)
	   (add-string "(")
	   (term-to-ttree$ (arg-of-apply-term term) 0)
	   (add-string ")"))
	  (APPLY-PARTIAL
	   (term-to-ttree$ (function-of-apply-partial-term term) lprec)
	   (add-string "[")
	   (term-to-ttree$ (arg-of-apply-partial-term term) 0)
	   (add-string "]"))
	  (POS-NUMBER
	   (add-number (number-of-pos-number-term term)))
	  ((ADD SUB MUL DIV MOD)
	   (term-to-ttree$ (leftterm-of-binary-term term) lprec)
	   (add-string
	     (case (kind-of-term term)
	       (ADD "+")
	       (SUB "-")
	       (MUL "*")
	       (DIV "/")
	       (MOD " mod ")))
	   (term-to-ttree$ (rightterm-of-binary-term term) rprec))
	  (CONS
	   (term-to-ttree$ (head-of-cons-term term) lprec)
	   (add-string ".")
	   (term-to-ttree$ (tail-of-cons-term term) rprec))
	  (LESS
	   (term-to-ttree$ (leftterm-of-less-term term) lprec)
	   (add-string "<")
	   (term-to-ttree$ (rightterm-of-less-term term) rprec))
	  ((INL INR)
	   (add-string
	     (case (kind-of-term term)
	       (INL "inl(")
	       (INR "inr(")))
	   (term-to-ttree$ (term-of-injection-term term) rprec)
	   (add-string ")"))
	  (ANY
	   (add-string "any(")
	   (term-to-ttree$ (term-of-any-term term) 0)
	   (add-string ")"))
	  (DOM
	   (add-string "dom(")
	   (term-to-ttree$ (term-of-dom-term term) 0)
	   (add-string ")"))
	  (MINUS
	   (add-string "-")
	   (term-to-ttree$ (term-of-minus-term term) rprec))
	  (UNIVERSE
	   (add-string "U")
	   (add-number (level-of-universe-term term)))
	  (TOKEN
	   (add-string "\"" #||"||#)		;The junk is to keep zmacs happy.
	   (add-list (atom-of-token-term term))
	   (add-string "\"" #||"||#))
	  (TAGGED
	   (add-string "[[")
	   (let ((n (tag-of-tagged-term term)))
	     (if (zerop n)
		 (add-string "*")
		 (add-number n)))
	   (add-string ";")
	   (term-to-ttree$ (term-of-tagged-term term) 0)
	   (add-string "]]"))
	  (otherwise
	   (error "~a~^ ~a" '|TERM-TO-TTREE: Invalid term kind: | (kind-of-term term)))))
    (when need-parens-p (add-string ")"))))
