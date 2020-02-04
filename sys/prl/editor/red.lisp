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

;=========================================;
;                                         ;
;                RED.L                    ;
;                                         ;
;   Main routines of Refinement Editor    ;
;                                         ;
;=========================================;


(global show-parens)    ;-- = t iff calls to term-to-ttree$ should yield Ttrees representing
                         ;-- fully parenthesized forms of terms.

;-----------------------------------;
;                                   ;
;       GLOBAL RED ROUTINES         ;
;                                   ;
;-----------------------------------;



;--
;-- red-init ()
;--
;--     Initialize red.  This need be called only once
;--     when the system is started.
;--

(defun red-init ()

   (<- show-parens nil)

)


;--
;-- new-red-region (reg:region#, thm:theorem-object)
;--
;--     Create a new red descriptor for thm in region reg,
;--     and place it in reg's descriptor field.
;--

(defun new-red-region (reg thm)

    (<- rdescr$ (new red-descriptor))
    (<- (sel region (reg) descriptor) rdescr$)

    (<- (sel rdescr$ thm) thm)
    (set-current-level$ nil)
    (<- (sel rdescr$ long-count) 0)
    (<- (sel rdescr$ previous-ch-was-exit) nil)
  
    (layout-proof-level cur-region)
    (display-proof-level cur-region)

)


;--
;-- red (ch:prlchar)
;--
;--     Process the char ch as a refinement proof editing char.
;--     The current region holds the thm to be edited.  Successive
;--     chars come through this routine one by one, so all state info
;--     must be maintained in the region descriptor between chars.
;--     The only actions allowed in a red region when it has an 
;--     associated TTREE region are cursor motions within the
;--     current level -- even EXIT must wait until the associated
;--     region is EXITed first.
;--

(defun red (ch)
  (declare (special cur-window$))

    (<- (sel region (cur-region) allowed-events) nil)

    (<- rdescr$ (sel region (cur-region) descriptor))


    (Pif (equal ch '(LONG)) -->
        
        ;-- increment count of contiguous LONG chars seen
            (<- (sel rdescr$ long-count) (1+ *-*))


     || (equal ch '(UP)) -->

        (Pif (zerop (sel rdescr$ long-count)) -->

            ;-- move level-cursor up one minor stopping point
                (slide-level-cursor cur-region 'UP)

         || (onep (sel rdescr$ long-count)) -->

            ;-- move level-cursor up approx one major stopping point
                (slide-level-cursor-far cur-region 'UP)

         || t -->
    
            ;-- move level-cursor to top-most position
                (Plet (last-cursor (sel rdescr$ level-cursor)
                     )

                    (slide-level-cursor cur-region 'UP)
                    (Ploop
                        (while (not (equal last-cursor
                                           (sel rdescr$ level-cursor)
                                    )
                               )
                        )
                        (do
                            (<- last-cursor (sel rdescr$ level-cursor))
                            (slide-level-cursor cur-region 'UP)
                        )
                    )
                )

         fi)

        (move-displayed-level-cursor cur-region)


     || (equal ch '(DOWN)) -->

        (Pif (zerop (sel rdescr$ long-count)) -->

            ;-- move level-cursor down one minor stopping point
                (slide-level-cursor cur-region 'DOWN)

         || (onep (sel rdescr$ long-count)) -->

            ;-- move level-cursor down approx one major stopping point
                (slide-level-cursor-far cur-region 'DOWN)

         || t -->
    
            ;-- move level-cursor to bottom-most position
                (Plet (last-cursor (sel rdescr$ level-cursor)
                     )

                    (slide-level-cursor cur-region 'DOWN)
                    (Ploop
                        (while (not (equal last-cursor
                                           (sel rdescr$ level-cursor)
                                    )
                               )
                        )
                        (do
                            (<- last-cursor (sel rdescr$ level-cursor))
                            (slide-level-cursor cur-region 'DOWN)
                        )
                    )
                )

         fi)

        (move-displayed-level-cursor cur-region)


     || (not (null (sel region (cur-region) assoc-region))) -->

        (display-message (append '#.(istring "Requested action forbidden in this region ")
                                 '#.(istring "until the associated view is killed.")
                         )
        )


     || (equal ch '(DIAG)) -->

        (Pif (zerop (sel rdescr$ long-count)) -->

            ;-- move cursor to parent goal
                (Pif (eql 'GOAL (car (major-of-level-cursor
                                       (sel rdescr$ level-cursor)
                                   )
                              )
                    ) -->
                    ;-- go to parent (changing level)
                        (proof-cursor-diag$)
                        (layout-proof-level cur-region)
                        (display-proof-level cur-region)

                 || t -->
                    ;-- go to parent (in same level)
                        (proof-cursor-diag$)
                        (move-displayed-level-cursor cur-region)

                 fi)

         || (onep (sel rdescr$ long-count)) -->

            ;-- move cursor to fourth parent goal up proof
                (for (x in '(1 2 3 4))
                     (do
                         (proof-cursor-diag$)
                     )
                )
                (layout-proof-level cur-region)
                (display-proof-level cur-region)

         || t -->
    
            ;-- move cursor to root of proof
                (set-current-level$ nil)
                (layout-proof-level cur-region)
                (display-proof-level cur-region)

         fi)


     || (equal ch '(RIGHT)) -->

        (Pif (zerop (sel rdescr$ long-count)) -->

            (Plet (maj-cursor (major-of-level-cursor (sel rdescr$ level-cursor))
                  pf-cursor  (sel rdescr$ proof-cursor)
                 )

                 (Pif (eql 'SUBGOAL (car maj-cursor)) -->   ;-- Go into child.

                     ;-- descend into the level of the specified child

                     (set-current-level$ (append pf-cursor (cdr maj-cursor)))
                     (layout-proof-level cur-region)
                     (display-proof-level cur-region)
                  fi)
            )

         || t -->

            (red-find-unproved-leaf$)   ;-- LONG RIGHT: go to next unproved leaf

         fi)


     || (equal ch '(LEFT)) -->

            (Pif (not (null (sel rdescr$ proof-cursor))) -->
                (Plet (revcur         (reverse (sel rdescr$ proof-cursor))
                      subgoal-assums (assumptions-of-proof-tree
                                         (sel rdescr$ current-level)
                                     )
                     )

                    (set-current-level$ (reverse (cdr revcur)))
                    (<- (sel rdescr$ level-cursor) 
                        (level-cursor (list 'SUBGOAL (car revcur))
                                      '(CONCL) 
                        )
                    )
                    (layout-proof-level cur-region)
                    (display-proof-level cur-region)
                )
             fi)


     || (equal ch '(SEL)) -->

        (red-select$)

     || (and (equal ch '(INS))
             (eql (sel region (cur-region) view-kind) 'EDIT) 
        ) -->
        nil ;;;;;;;;;;;;;;;;;;

     || (and (equal ch '(TRANSFORM))
            (eql (sel region (cur-region) view-kind) 'EDIT)
        ) -->

        (Pif (null free-regions) -->
            (display-message '#.(istring "Too many active views.  Please kill some."))

         || (null (sel rdescr$ current-level)) -->
            (display-message
                (append '#.(istring "Bad or missing goal.  ")
                        '#.(istring "Transformation cannot be applied.")
                )
            )

         || t -->
            (Plet (proof-region    0   ;-- the region holding the proof
                  bot             0   ;-- coordinates in view of bottom
                  right           0   ;--     and right limits of view
                  level           nil ;-- the current-level of the proof
                  level-cursor    nil ;-- the level-cursor for current-level
                  view-kind       nil ;-- view-kind for new view, EDIT or SHOW
                  view-part       nil ;-- sort of thing shown in new view
                  view-descr      nil ;-- descriptor returned from createview
                 )

                (<- proof-region cur-region)
                (<- level (sel rdescr$ current-level))
                (<- level-cursor (sel rdescr$ level-cursor))

                ;-- grab a free region, insert it into used-regions list just
                ;-- after cur-region, and make it current
          
                    (<- num-regions (1+ *-*))
                    (<- cur-region (car free-regions))
                    (<- free-regions (cdr free-regions))
       
                    (Pif (onep num-regions) -->
                        (<- used-regions (list cur-region))
                        (<- cur-region-index 0)
   
                     || t -->
                        (<- (cdr (nthcdr cur-region-index used-regions))
                            (cons cur-region *-*)
                        )
                        (<- cur-region-index (1+ *-*))
    
                     fi)

                ;-- create a new view with nil name,
                ;-- indicating this region is associated with a proof
                    (<- view-descr (createview nil cur-region 'small))

                    (<- cur-window$ (car view-descr))
                    (<- bot (cadr view-descr))
                    (<- right (caddr view-descr))

                    (selectw cur-window$)

                ;-- fill in most fields of this new region
                    (<- (sel region (cur-region) obj-name)
			(sel region (proof-region) obj-name))
                    (<- (sel region (cur-region) obj-kind)       'TTREE)
                    (<- (sel region (cur-region) window)         cur-window$)
                    (<- (sel region (cur-region) top)            0)
                    (<- (sel region (cur-region) left)           0)
                    (<- (sel region (cur-region) bot)            bot)
                    (<- (sel region (cur-region) right)          right)
                    (<- (sel region (cur-region) allowed-events) '(KILL SIZE))
                    (<- (sel region (cur-region) modified)       nil)

                ;-- link together associated regions
                    (<- (sel region (cur-region) assoc-region) proof-region)
                    (<- (sel region (proof-region) assoc-region) cur-region)

                ;-- Initialize the new region.
                    (<- (sel rdescr$ edited-part) 'TRANSFORMATION)
                    (new-ted-region cur-region (copy the-null-Ttree))

                ;-- set view-kind field of new view and set view header        
                    (<- (sel region (cur-region) view-kind) 'EDIT)
                    (setheaderw
                        nil
                        '#.(istring "Transformation Tactic")
                    )

            )
         fi)


     || (and (equal ch '(COPY))
             (eql (sel region (cur-region) view-kind) 'EDIT) 
        ) -->
        nil ;;;;;;;;;;;;;;;;     

     || (equal ch '(EXIT)) -->

        (remove-active-region)


     || (equal ch '(SHOW-PARENS)) -->
        (let ((show-parens t))
	  (red-select$))

     || t -->
        ;-- indicate char not processed
            (display-message '#.(istring "Key invalid in this view."))


     fi)

    (Pif (not (equal ch '(LONG))) -->
        (<- (sel rdescr$ long-count) 0)
     fi)

    (<- (sel region (cur-region) allowed-events)
        (Pif (null (sel region (cur-region) assoc-region)) --> '(KILL SIZE)

         || t --> '(SIZE)  ;-- no KILL when subsidiary region exists

         fi)
    )

)

;--
;-- red-find-unproved-leaf$
;--
;-- LONG RIGHT: search (in preorder) for the next unproved leaf and make it
;-- the new current node.  If necessary, have the search wraparound from the
;-- end of the tree to the front.  If there aren't any unproved leaves, go to
;-- the root.  If the cursor is in a subgoal, start the search from it.
;--

(defun red-find-unproved-leaf$ ()

    (Plet (thm        (sel rdescr$ thm)
	  name       (sel region (cur-region) obj-name)
	  object     nil
          maj-cursor (major-of-level-cursor (sel rdescr$ level-cursor))
          thm-obj    nil   ;-- PRL (theorem) object being edited.
          proof      nil   ;-- its proof.
          pf-cursor  nil   ;-- cursor to current point in proof.
          newcursor  nil   ;-- cursor to unproved leaf (or root).
          subnbr     nil   ;-- subgoal nbr, if any.
          subproof   nil   ;-- subproof pointed to by subnbr, if any.
         )

	 (<- object (library-object name))

         (Pif (eql 'COMPLETE
		 (sel (object object) status)
	     ) -->

             (display-message '#.(istring "No unproved leaves."))
             (<- newcursor nil)

          || t -->

             (<- pf-cursor (sel rdescr$ proof-cursor))
             (<- subnbr (cadr maj-cursor))
             (<- proof (get-proof-of-theorem-object thm name))

             (Pif (and (eql 'SUBGOAL (car maj-cursor)) (> subnbr 0)) -->

                 (<- pf-cursor (append pf-cursor (list subnbr)))
                 (<- subproof (nthelem subnbr (children-of-proof-tree proof)))

                 (Pif (null (rule-of-proof-tree subproof)) -->
                    (<- newcursor pf-cursor)
                 || t -->
                    (<- newcursor (search-along-cursor$ proof pf-cursor))
                 fi)

              || t --> (<- newcursor (search-along-cursor$ proof pf-cursor))

              fi)

             (Pif (eql newcursor 'NONE) -->

                 (<- newcursor (search-along-cursor$ proof nil))

                 (Pif (eql newcursor 'NONE) --> (<- newcursor nil)
                  fi)
              fi)
          fi)

         (set-current-level$ newcursor)
         (layout-proof-level cur-region)
         (display-proof-level cur-region)
    )
)

;--
;-- red-select$
;--
;--     Brings up a subsidiary ted window to show/edit the view-part pointed
;--     to by the level-cursor.
;--

(defun red-select$ ()
  (declare (special cur-window$))
    (Pif (null free-regions) -->
        (display-message '#.(istring "Too many active views.  Please kill some."))

     || t -->
        (Plet (proof-region    0   ;-- the region holding the proof
	      proof-window    nil ;-- the window of the region holding the proof
              top             0   ;-- coordinates in view of top
              bot             0   ;-- coordinates in view of bottom
              left            0   ;-- coordinates in view of left
              right           0   ;-- coordinates in view of right
              level           nil ;-- the current-level of the proof
              level-cursor    nil ;-- the level-cursor for current-level
              view-kind       nil ;-- view-kind for new view, EDIT or SHOW
              view-part       nil ;-- sort of thing shown in new view
              view-descr      nil ;-- descriptor returned from createview
             )

            (<- proof-region cur-region)
            (<- proof-window (sel region (cur-region) window))
            (<- level (sel rdescr$ current-level))
            (<- level-cursor (sel rdescr$ level-cursor))

            ;-- grab a free region, insert it into used-regions list just
            ;-- after cur-region, and make it current

                (<- num-regions (1+ *-*))
                (<- cur-region (car free-regions))
                (<- free-regions (cdr free-regions))

                (Pif (onep num-regions) -->
                    (<- used-regions (list cur-region))
                    (<- cur-region-index 0)

                 || t -->
                    (<- (cdr (nthcdr cur-region-index used-regions))
                        (cons cur-region *-*)
                    )
                    (<- cur-region-index (1+ *-*))

                 fi)

            ;-- create a new view with nil name,
            ;-- indicating this region is associated with a proof
		;-- If this is a RULE or MAIN GOAL view than create a region
		;-- in a window within the current proof window (same width,
		;-- from the goal or BY-line to the bottom).  Otherwise, use
		;-- createview to pick an appropriate place for this window.
                (Pif (eql (car (major-of-level-cursor level-cursor))
                        'RULE
                    ) -->
		    (Plet (wtop       (getw-top proof-window)
			  wbot       (getw-bot proof-window)
			  wleft      (getw-left proof-window)
			  wright     (getw-right proof-window)
			  rule-entry nil ; level map entry of rule
			  rule-start nil
			  rule-end   nil
			  rule-size  0
			  first-line (start-of-level-map-entry
				        (sel rdescr$ first-displayed-entry)
				     )
			 )
			 (<- rule-entry (sel rdescr$ level-map))
			 (Ploop
			     (while (not (equal '(rule)
						(major-of-level-cursor
						  (level-cursor-of-level-map-entry
						    (car rule-entry)
						  )
						)
					 )
				    )
			     )
			     (do
			       (<- rule-entry (cdr rule-entry))
			     )
			 )
			 (<- rule-entry (car rule-entry))
			 (<- rule-start (start-of-level-map-entry rule-entry))
			 (<- rule-end (end-of-level-map-entry rule-entry))
			 (<- rule-size (- rule-end rule-start))
			 (<- rule-start (+ wtop (- rule-start first-line) 1))
			 (Pif (< rule-start wtop) -->
			     (<- rule-start wtop)
			  fi)
			 (Pif (> (- wbot rule-start) 2) -->
			     (<- wtop (+ rule-start 3))
			     (<- wbot (min wbot (+ wtop rule-size 3)))
			     (<- wleft (1+ wleft))
			     (<- wright (1- wright))
			     (createview-no-window nil cur-region 'small)
			     (<- cur-window$ (createw wtop wbot wleft wright))
			     (<- top 0)
			     (<- bot (- wbot wtop))
			     (<- left 0)
			     (<- right (- wright wleft))

			  || t -->
			     (<- view-descr (createview nil cur-region 'small))
			     (<- cur-window$ (car view-descr))
			     (<- top 0)
			     (<- bot (cadr view-descr))
			     (<- left 0)
			     (<- right (caddr view-descr))

			  fi)

		    )
		     
                 || (and (eql (car (major-of-level-cursor level-cursor))
			     'GOAL
			 )
                         (null (sel rdescr$ proof-cursor))
			 (not show-parens)
                    ) -->
		    (Plet (wtop   (getw-top proof-window)
			  wbot   (getw-bot proof-window)
			  wleft  (getw-left proof-window)
			  wright (getw-right proof-window)
			 )
			 (createview-no-window nil cur-region 'small)
			 (Pif (> (- wbot wtop) 6) -->
			     (<- wtop (+ wtop 4))
			  fi)
			 (<- wbot (min wbot (+ wtop 4)))
			 (<- wleft (1+ wleft))
			 (<- wright (1- wright))
			 (<- cur-window$ (createw wtop wbot wleft wright))
		         (<- top 0)
			 (<- bot (- wbot wtop))
			 (<- left 0)
			 (<- right (- wright wleft))
		    )

		|| t -->
                   (<- view-descr (createview nil cur-region 'small))

                   (<- cur-window$ (car view-descr))
                   (<- top 0)
                   (<- bot (cadr view-descr))
                   (<- left 0)
		   (<- right (caddr view-descr))

		 fi)

                (selectw cur-window$)

            ;-- fill in most fields of this new region
                (<- (sel region (cur-region) obj-name)
		    (sel region (proof-region) obj-name))
                (<- (sel region (cur-region) obj-kind)       'TTREE)
                (<- (sel region (cur-region) window)         cur-window$)
                (<- (sel region (cur-region) top)            top)
                (<- (sel region (cur-region) left)           left)
                (<- (sel region (cur-region) bot)            bot)
                (<- (sel region (cur-region) right)          right)
                (<- (sel region (cur-region) allowed-events) '(KILL SIZE))
                (<- (sel region (cur-region) modified)       nil)

            ;-- link together associated regions
                (<- (sel region (cur-region) assoc-region) proof-region)
                (<- (sel region (proof-region) assoc-region) cur-region)

            ;-- determine object to be viewed, view-kind (rules and
            ;-- main goal are EDITable, all else is for SHOW), 
            ;-- view-part (main goal, goal, subgoal, rule),
            ;-- record identity of part being edited (if any) in
            ;-- proof region's descriptor, and put object to be
            ;-- viewed into value field of new view
                (Pif (eql (car (major-of-level-cursor level-cursor))
                        'RULE
                    ) -->
                    (<- view-kind
                        (Pif show-parens --> 'SHOW
                         || t --> (sel region (proof-region) view-kind)
                         fi)
                    )                                                                
                    (<- view-part '#.(istring "rule"))
                    (<- (sel rdescr$ edited-part) 'RULE)
                    (new-ted-region cur-region
                                    (Pif (and show-parens
                                             (rule-of-proof-tree level) 
                                        )-->
                                        (rule-to-Ttree (rule-of-proof-tree level))
                                     || t -->
                                        (rule-body-of-proof-tree level)
				     fi)
                    )
 
                 || (eql (car (major-of-level-cursor level-cursor))
                        'GOAL
                    ) -->
                    (Pif (and (null (sel rdescr$ proof-cursor)) (not show-parens))  -->
                        (<- view-kind (sel region (proof-region) view-kind))
                        (<- view-part '#.(istring "main goal"))
                        (<- (sel rdescr$ edited-part) 'MAINGOAL)
                        (new-ted-region cur-region
                                        (sel rdescr$ thm goal-body)
                        )

                     || t -->
                        (<- view-kind 'SHOW)
                        (<- view-part '#.(istring "goal"))
                        (<- (sel rdescr$ edited-part) nil)
                        (new-ted-region cur-region (Pif level -->                                                                                     (pf-to-show-Ttree level)
						    || t -->
						       (sel rdescr$ thm goal-body)
                                                    fi)
			)
 
                     fi)

                 || t --> ;-- a SUBGOAL
                    (<- view-kind 'SHOW)
                    (<- view-part '#.(istring "subgoal"))
                    (<- (sel rdescr$ edited-part) nil)
                    (new-ted-region cur-region
                        (pf-to-show-Ttree
                             (nthelem (cadr (major-of-level-cursor
                                                level-cursor
                                             )
                                      )
                                      (children-of-proof-tree level)
                             )
                        )
                    )
         
                 fi)

            ;-- set view-kind field of new view and set view header        
                (<- (sel region (cur-region) view-kind) view-kind)
                (setheaderw
                    nil
                    (append
                        (Pif (eql view-kind 'SHOW) --> '#.(istring "SHOW ")
                         || t                    --> '#.(istring "EDIT ")
                         fi)
                        view-part
                        '#.(istring " of ")
                        (istring (sel region (proof-region) obj-name))
                    )
                )

        )
     fi)
)

(defun remove-active-region ()
    ;-- 
    ;-- Remove all traces of the current region, and set the current region
    ;-- to a sane value.
    ;--
        (Plet (
                 current-view
                 (car
                     (Psome
		      #'(lambda (view)
			  (equal cur-region (region-of-view view))
			  )
                         view-stack
                     )
                 )
             )
            (remove-view current-view)
        )
)


(defun number-of-views (name)
  (let ((n 0))
    (for (view in view-stack)
	 (do (when (eq (name-of-view view) name)
	       (incf n))))
    n))

(defun remove-view (view)
    ;-- 
    ;-- Remove all traces of the region corresponting to the given view, and
    ;-- set the current region to a sane value.
    ;--
        (Plet (reg (region-of-view view))
            (destroyw (sel region (reg) window))
            (destroyview view)
            (Pif (and
                    (eql (sel region (reg) view-kind) 'SHOW)
                    (eql (number-of-views (name-of-view view))
			 1)
                ) -->
                (restore-edit (name-of-view view))
            fi)
            (<- num-regions (1- num-regions))
            (Pif (member cur-region (cdr (member reg used-regions))) -->
                ;-- cur-region is after the region to be killed in the
                ;-- used-regions list, so decrement cur-region-index to keep
                ;-- the current region current.
                    (<- cur-region-index (1- *-*))
            fi)
            (<- used-regions (delete cur-region used-regions))
            (<- free-regions (cons cur-region free-regions))
            (Pif (not (zerop num-regions)) -->
                (<- cur-region-index (rem *-* num-regions))
                (<- cur-region
                    (nthelem (1+ cur-region-index) used-regions)
                )
             fi)
        )
)



(defun restore-edit (name)
    ;-- 
    ;-- A show view for object name has been destroyed.  If there is view
    ;-- for the object which used to be an edit view and it is the only view
    ;-- of the object left, then change it back to an edit view.

        (Plet (
                 edit-region      -1
                 num-active-views 0
             )
            (for
                (view in view-stack)
                (do
                    (Pif (eql (name-of-view view) name) -->
                        (<- num-active-views (1+ *-*))
                        (<- edit-region (region-of-view view))
                     fi)
                )
            )
            (Pif (and
                    (equal num-active-views 1)
                    (> edit-region -1)
                ) -->
                (<- (sel
                        region (edit-region)
                        view-kind
                    )
                    'EDIT
                )
                (selectw
                    (sel
                        region (edit-region)
                        window
                    )
                )
                (setheaderw 0 '#.(istring "EDIT"))
             fi)
        )
)



                    

;--
;-- red-subsidiary-killed (reg:region#)
;--
;--     The region, reg, associated with a PROOF region has been killed.
;--     If it was an EDIT view and was modified, take action to process
;--     the changes made to the proof tree.
;--

(defun red-subsidiary-killed (reg)

;;;;;;;;;;;;WHAT ABOUT MODIFIED FIELD?  WHEN SET?  when set-object-status?

    (Plet (proof-region (sel region (reg) assoc-region)
          redisplay-lib nil
          curr-obj nil
          curr-obj-name nil
          old-status nil
          new-status nil
	  main-tree  nil
         )
        
        (<- rdescr$ (sel region (proof-region) descriptor))

        (<- (sel region (proof-region) assoc-region) nil)

        (Pif (sel region (reg) modified) -->

	    (<- old-status
		(if (null (sel rdescr$ current-level))
		    (if (or (equal (sel rdescr$ thm goal-body) the-null-Ttree)
			    (equal (sel rdescr$ thm goal-body) raw-object-Ttree))
			'RAW
			'BAD)
		    (status-of-proof-tree (sel rdescr$ current-level))))

            ;-- Process the modification
                (Pif (eql (sel rdescr$ edited-part) 'MAINGOAL) -->

		    (<- main-tree (goal-body-to-proof-tree (sel rdescr$ thm goal-body)))
		    (set-proof-of-theorem-object
		        (sel rdescr$ thm)
			'PROOF-TREE
			main-tree
		    )
                    (set-current-level$ nil)
		    (Pif (or (equal (sel rdescr$ thm goal-body) raw-object-Ttree)
			     (equal (sel rdescr$ thm goal-body) the-null-Ttree))
			  --> (<- new-status 'RAW)
		     || (null main-tree) -->
		        (<- new-status 'BAD)
		     || t -->
			(<- new-status 'INCOMPLETE)
		     fi)
    
                 || (eql (sel rdescr$ edited-part) 'RULE) -->

                    (parse-rule-and-refine (sel rdescr$ current-level))
                    (set-current-level$ (sel rdescr$ proof-cursor))
		    (<- new-status (calculate-red-status (sel rdescr$ current-level)))

                 || (eql (sel rdescr$ edited-part) 'TRANSFORMATION) -->

                    (apply-transformation-tactic
                        (Ttree-of-ted-descriptor
                            (sel region (reg) descriptor)
                        )
                        (sel rdescr$ current-level)
                    )
                    (set-current-level$ (sel rdescr$ proof-cursor))
		    (<- new-status (calculate-red-status (sel rdescr$ current-level)))

                 fi)

            (<- curr-obj-name (sel region (proof-region) obj-name))
            (<- curr-obj (library-object curr-obj-name))

            ;-- will have to re-extract since proof has been editted.
                (invalidate-extraction curr-obj)

            ;-- Propagate status changes            
                (Pif (not (eql old-status new-status)) -->

                    (Pif (sel rdescr$ current-level) -->
                        (<- (status-of-proof-tree (sel rdescr$ current-level))
                            new-status
                        )
                     fi)

                    (Pif (propagate-red-status
                            (get-proof-of-theorem-object (sel rdescr$ thm) curr-obj-name)
                            (sel rdescr$ proof-cursor)
                        ) -->
                        (<- (sel (object curr-obj) status)
                            (red-status-to-obj-status
			      (or (status-of-proof-tree
				    (get-proof-of-theorem-object
				      (sel rdescr$ thm)
				      curr-obj-name))
				  new-status)))
                        (<- redisplay-lib t)
                     fi)
                 fi)

            ;-- Redisplay this level of the proof
                (layout-proof-level proof-region)
                (display-proof-level proof-region)

            ;-- If the root changed redisplay the library
                (Pif (or redisplay-lib (null (sel rdescr$ proof-cursor))) -->
                    (update-lib-display (list curr-obj-name))
                 fi)

         fi)

   )
)


;;; Minimally copy a proof tree.
(defun copy-proof (p)
    (let* ((copied-p (copy-list p)))
      (setf (rule-body-of-proof-tree copied-p)
	    (copy (rule-body-of-proof-tree p)))
      (setf (children-of-proof-tree copied-p)
	    (mapcar #'copy-proof (children-of-proof-tree p)))
      copied-p))




;-- 
;-- apply-transformation-tactic (tactic: Ttree, proof: proof-tree)
;--
;-- Apply the transformation tactic and splice the result back into the
;-- proof tree.

(defun apply-transformation-tactic (tactic proof)
    (Plet (
             result-proof
             (do-tactic
                 proof tactic #'transformation-error
             )
         )
        (Pif (not (null result-proof)) -->
	    (<- result-proof (copy-proof *-*))
            (<- (rule-of-proof-tree proof)
                (rule-of-proof-tree result-proof)
            )
            (<- (rule-body-of-proof-tree proof)
                (rule-body-of-proof-tree result-proof)
            )
            (<- (children-of-proof-tree proof)
                (children-of-proof-tree result-proof)
            )
         fi)
    )
)
(defun transformation-error (message)
    (display-message
        (append
            '#.(istring "Error in Transformation Tactic: ")
            message
        )
    )
)

;--
;-- red-kill-view (view:element-of-view-stack)
;--
;--     Remove the Proof region associated with the specified view.
;--     Leave cur-region set to the desired value.  The caller must
;--     set and select the appropriate current window.
;--

(defun red-kill-view (view)

    (Plet (reg (region-of-view view)
         )

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
;-- red-size-view (view:element-of-view-stack)
;--
;--     Redraw the current-level of the proof in the region
;--     associated with the specified view.
;--

(defun red-size-view (view)

    (layout-proof-level (region-of-view view))
    (display-proof-level (region-of-view view))

)


;--
;-- red-mouse-char (reg:region#, row, col, kind:{MOUSE-JUMP,MOUSE-SEL})
;--
;--     Map the given row and column into a level cursor for the region.
;--     If kind is MOUSE-SEL, then do a select on the view-kind specified
;--     by the level cursor.  If kind is MOUSE-JUMP, then if level-cursor
;--     is a SUBGOAL then zoom into it (like RIGHT) and if it is the GOAL
;--     then go to the parent (like DIAG).
;--
;--     We assume reg = cur-region.  (Set by process-mouse-char$ in prl.l)
;--

(defun red-mouse-char (reg row col kind)

    (Plet (mapped-level-cursor nil   ;-- mapped from real cursor.
          maj-cursor          nil   ;-- major of mapped-level-cursor.
          maj-kind            nil   ;-- kind of major stopping point.
          pf-cursor           nil   ;-- current proof-cursor.
         )

         (<- rdescr$             (sel region (reg) descriptor))
         (<- mapped-level-cursor (map-rc-to-level-cursor reg row col))
         (<- maj-cursor          (when mapped-level-cursor
				   (major-of-level-cursor mapped-level-cursor)))

         (Pif (and (not (null mapped-level-cursor))
                  (null (sel region (cur-region) assoc-region))
             ) -->

             (Pif (eql kind 'MOUSE-SEL) -->   ;-- do a select, if not one already

                 (<- (sel rdescr$ level-cursor) mapped-level-cursor)
                 (red-select$)

              || (eql kind 'MOUSE-JUMP) -->

                 (<- maj-kind (car maj-cursor))

                 (Pif (eql 'GOAL maj-kind) --> ;-- go to the parent level

                     (proof-cursor-diag$)

                  || (eql 'SUBGOAL maj-kind) -->   ;-- go into specified child.

                     (<- pf-cursor (sel rdescr$ proof-cursor))
                     (set-current-level$ (append pf-cursor (cdr maj-cursor)))
                  fi)

                 (layout-proof-level cur-region)
                 (display-proof-level cur-region)
              fi)
          fi)
    )
)



;-------------------------------------------------;
;                                                 ;
;       PROOF CURSOR MANIPULATION ROUTINES        ;
;                                                 ;
;-------------------------------------------------;


;--
;-- set-current-level$ (cursor:proof-cursor)
;--
;--     Set proof-cursor to cursor, level-cursor to the top of the level,
;--     and cur-level to the level selected by cursor.  This has the effect
;--     of going to the main goal in the level specified by cursor.
;--

(defun set-current-level$ (cursor)
    
    (<- (sel rdescr$ proof-cursor) cursor)
    (<- (sel rdescr$ current-level)
        (extract-level$
	    (get-proof-of-theorem-object
	      (sel rdescr$ thm)
	      (sel region (cur-region) obj-name))
	    cursor))
    (<- (sel rdescr$ level-cursor)
        (level-cursor '(GOAL)
                      (if (or (null (sel rdescr$ current-level))
			      (null (assumptions-of-proof-tree
				      (sel rdescr$ current-level))))

                          '(CONCL)

			  '(ASSUM 1)))))


;--
;-- extract-level$ (ptree:proof-tree, cursor:proof-cursor)
;--
;--     Return the level of ptree selected by cursor.
;--

(defun extract-level$ (ptree cursor)

    (Pif (null cursor) -->
        ptree

     || t -->
        (extract-level$ (nthelem (car cursor)
                                 (children-of-proof-tree ptree)
                        )
                        (cdr cursor)
        )

     fi)

)


;--
;-- proof-cursor-diag$ ()
;--
;--     Adjust level-cursor, proof-cursor to specify the
;--     parent goal of the currently specified stopping point.
;--

(defun proof-cursor-diag$ ()
 
    (Pif (eql 'GOAL (car (major-of-level-cursor (sel rdescr$ level-cursor)))) -->
        ;-- at this level's main goal already,
        ;-- retract to previous level (Pif any)
            (Pif (not (null (sel rdescr$ proof-cursor))) -->
                (set-current-level$
                     (reverse (cdr (reverse (sel rdescr$ proof-cursor))))
                )
             fi)
 
     fi)

    (<- (sel rdescr$ level-cursor)
        (level-cursor '(GOAL)
                      (Pif (or (null (sel rdescr$ current-level))
			       (null (assumptions-of-proof-tree
				       (sel rdescr$ current-level)))

                           ) --> '(CONCL)

                       || t --> '(ASSUM 1)
                       fi)
        )
    )

)

;--
;-- search-along-cursor (proof:proof-tree cursor:proof-cursor)
;--
;--     Returns a proof-cursor for the first bad or unrefined proof node
;--     occuring after the indicated node in a pre-order traversal of the
;--     proof tree.
;--
;-- Modified by jts: don't return the indicated node if it's unproved.
;-- Note that the indicated node is found by applying the cursor to the proof.
;--

(defun search-along-cursor$ (proof cursor)
    (Plet (newcursor 'NONE)

        (Pif (null cursor) -->

            (Pif (null (rule-of-proof-tree proof)) --> 'NONE
             || t --> (findleaf$ proof)
             fi)

         || t -->
            (<- newcursor
                (search-along-cursor$
                    (nthelem
                        (car cursor)
                        (children-of-proof-tree proof)
                    )
                    (cdr cursor)
                )
            )
            (Pif (not (eql newcursor 'NONE)) -->
                (cons (car cursor) newcursor)

             || t -->
                (Ploop
                    (local
                        children-to-search (nthcdr
                                               (car cursor)
                                               (children-of-proof-tree proof)
                                           )
                        current-child-index (car cursor)
                    )
                    (while (and
                               (eql newcursor 'NONE)
                               children-to-search
                           )
                    )
                    (do
                        (<- newcursor
                            (findleaf$ (car children-to-search))
                        )
                        (<- children-to-search (cdr *-*))
                        (<- current-child-index (1+ *-*))
                    )
                    (result
                        (Pif (eql newcursor 'NONE) -->
                            'NONE
                         || t -->
                            (cons current-child-index newcursor)
                         fi)
                    )
                )
             fi)

         fi)
    )
)

;--
;-- findleaf$ (p:proof-tree)
;--
;--     Return a proof-cursor for some bad or unrefined leaf of p.
;--     Return NONE if no such leaf exists.
;--

(defun findleaf$ (p)

    (Plet (children (children-of-proof-tree p)
          i        0
          cursor   'NONE
         )

        (Pif (null (rule-of-proof-tree p)) -->
            nil

         || t -->
            (Ploop
                (while (and children (eql cursor 'NONE)))
                (do
                    (<- i (1+ i))
                    (<- cursor (findleaf$ (car children)))
                    (<- children (cdr children))
                )
            )
            (Pif (eql cursor 'NONE) -->
                'NONE

             || t -->
                (cons i cursor)
    
             fi)

         fi)

    )
)


