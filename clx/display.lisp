;;; -*- Mode: LISP; Syntax: Common-lisp; Package: XLIB; Base: 10; Lowercase: Yes -*-

;;; This file contains definitions for the DISPLAY object for Common-Lisp X windows version 11

;;;
;;;			 TEXAS INSTRUMENTS INCORPORATED
;;;				  P.O. BOX 2909
;;;			       AUSTIN, TEXAS 78769
;;;
;;; Copyright (C) 1987 Texas Instruments Incorporated.
;;;
;;; Permission is granted to any individual or institution to use, copy, modify,
;;; and distribute this software, provided that this complete copyright and
;;; permission notice is maintained, intact, in all copies and supporting
;;; documentation.
;;;
;;; Texas Instruments Incorporated provides this software "as is" without
;;; express or implied warranty.
;;;

(in-package 'xlib :use '(lisp))

(export '(
	  with-display
	  with-event-queue
	  open-display
	  display-force-output
	  close-display
	  display-protocol-version
	  display-vendor
	  display-roots
	  display-motion-buffer-size
	  display-max-request-length
	  display-error-handler
	  display-after-function
	  display-invoke-after-function
	  display-finish-output))

;;
;; Resource id management
;;
(defun initialize-resource-allocator (display)
  ;; Find the resource-id-byte (appropriate for LDB & DPB) from the resource-id-mask
  (let ((id-mask (display-resource-id-mask display)))
    (unless (zerop id-mask) ;; zero mask is an error
      (do ((first 0 (index1+ first))
	   (mask id-mask (the mask32 (ash mask -1))))
	  ((oddp mask)
	   (setf (display-resource-id-byte display)
		 (byte (integer-length mask) first)))
	(declare (type array-index first)
		 (type mask32 mask))))))

(defun resourcealloc (display)
  ;; Allocate a resource-id for in DISPLAY
  (declare (type display display))
  (declare (values resource-id))
  (dpb (incf (display-resource-id-count display))
       (display-resource-id-byte display)
       (display-resource-id-base display)))

(defmacro allocate-resource-id (display object type)
  ;; Allocate a resource-id for OBJECT in DISPLAY
  (declare (type display display)
	   (type t object))
  (declare (values resource-id))
  (if (member (eval type) *clx-cached-types*)
      `(let ((id (funcall (display-xid ,display) ,display)))
	 (save-id ,display id ,object)
	 id)
    `(funcall (display-xid ,display) ,display)))

(defmacro deallocate-resource-id (display id type)
  ;; Deallocate a resource-id for OBJECT in DISPLAY
  (when (member (eval type) *clx-cached-types*)
    `(deallocate-resource-id-internal ,display ,id)))

(defun deallocate-resource-id-internal (display id)
  (remhash id (display-resource-id-map display)))

(defun lookup-resource-id (display id)
  ;; Find the object associated with resource ID
  (gethash id (display-resource-id-map display)))

(defun save-id (display id object)
  ;; Register a resource-id from another display.
  (declare (type display display)
	   (type integer id)
	   (type t object))
  (declare (values object))
  (setf (gethash id (display-resource-id-map display)) object))

(defun make-xatom (&key display id)
  (atom-name-internal display id))

;; Define functions to find the CLX data types given a display and resource-id
;; If the data type is being cached, look there first.
(macrolet ((generate-lookup-functions (useless-name &body types)
	    `(within-definition (,useless-name generate-lookup-functions)
	       ,@(mapcar
		   #'(lambda (type)
		       `(defun ,(xintern 'lookup- type)
			       (display id)
			  (declare (type display display)
				   (type resource-id id))
			  (declare (values ,type))
			  ,(if (member type *clx-cached-types*)
			       `(let ((,type (lookup-resource-id display id)))
				  (cond ((null ,type) ;; Not found, create and save it.
					 (setq ,type (,(xintern 'make- type)
						      :display display :id id))
					 (save-id display id ,type))
					;; Found.  Check the type
					,(cond ((null *type-check?*)
						`(t ,type))
					       ((member type '(window pixmap))
						`((type? ,type 'drawable) ,type))
					       (t `((type? ,type ',type) ,type)))
					,@(when *type-check?*
					    `((t (x-error 'lookup-error
							  :id id
							  :display display
							  :type ',type
							  :object ,type))))))
			       ;; Not being cached.  Create a new one each time.
			       `(,(xintern 'make- type)
				 :display display :id id))))
		   types))))
  (generate-lookup-functions ignore
    drawable
    window
    pixmap
    gcontext
    cursor
    colormap
    font
    xatom))

(defun atom-id (atom display)
  ;; Return the ID for an atom in DISPLAY
  (declare (type xatom atom)
	   (type display display))
  (declare (values (or null resource-id)))
  (gethash (if (keywordp atom)
	       atom
	       (kintern atom))
	   (display-atom-cache display)))

(defun set-atom-id (atom display id)
  ;; Set the ID for an atom in DISPLAY
  (declare (type xatom atom)
	   (type display display)
	   (type resource-id id))
  (declare (values resource-id))
  (setf (gethash (if (keywordp atom)
		     atom
		     (kintern atom))
		 (display-atom-cache display))
	id))

(defsetf atom-id set-atom-id)

(defun initialize-predefined-atoms (display)
  (do ((i 1 (1+ i))
       (end (length *predefined-atoms*))
       (save-p (member 'xatom *clx-cached-types*)))
      ((>= i end))
    (set-atom-id (svref *predefined-atoms* i) display i)
    (when save-p
      (save-id display i (svref *predefined-atoms* i)))))

(defun visual-info (display visual-id)
  (declare (type display display)
	   (type resource-id visual-id)
	   (values visual-info))
  (and (not (zerop visual-id))
       (or (lookup-resource-id display visual-id)
	   (error "Visual info not found for id #x~x in display ~s." visual-id display))))


;;
;; Display functions
;;
(defmacro with-display ((display &key timeout inline)
			&body body)
  ;; This macro is for use in a multi-process environment.  It provides exclusive
  ;; access to the local display object for multiple request generation.  It need not
  ;; provide immediate exclusive access for replies; that is, if another process is
  ;; waiting for a reply (while not in a with-display), then synchronization need not
  ;; (but can) occur immediately.  Except where noted, all routines effectively
  ;; contain an implicit with-display where needed, so that correct synchronization
  ;; is always provided at the interface level on a per-call basis.  Nested uses of
  ;; this macro will work correctly.  This macro does not prevent concurrent event
  ;; processing; see with-event-queue.
  `(with-buffer (,display
		 ,@(and timeout `(:timeout ,timeout))
		 ,@(and inline `(:inline ,inline)))
     ,@body))

(defmacro with-event-queue ((display &key timeout inline)
			    &body body &environment env)
  ;; exclusive access to event queue
  (if (and (null inline) (macroexpand '(use-closures) env))
      `(with-event-queue-function
	 ,display ,timeout
	 #'(lambda () 
	     (macrolet ((with-event-queue ((display &key timeout) &body body)
			  ;; Speedup hack for lexically nested with-event-queues
			  `(progn (progn ,display ,@(and timeout `(,timeout)) nil)
				  ,@body)))
	       ,@body)))
    (let ((disp (if (or (symbolp display) (constantp display)) display '.display.)))
      `(macrolet ((with-event-queue ((display &key timeout) &body body)
		    ;; Speedup hack for lexically nested with-event-queues
		    `(progn (progn ,display ,@(and timeout `(,timeout)) nil)
			    ,@body)))
	 (let (,@(unless (eq disp display) `((,disp ,display))))
	   (holding-lock ((display-event-lock ,disp) ,disp "CLX Event Lock"
			  ,@(and timeout `(:timeout ,timeout)))
	     ,@body))))))

(defun with-event-queue-function (display timeout function)
  (declare (type display display)
	   (type (or null number) timeout)
	   (type function function)
	   (downward-funarg function))
  (with-event-queue (display :timeout timeout :inline t)
    (funcall function)))

(defmacro with-event-queue-internal ((display &key timeout) &body body)
  ;; exclusive access to the internal event queues
  (let ((disp (if (or (symbolp display) (constantp display)) display '.display.)))
    `(let (,@(unless (eq disp display) `((,disp ,display))))
       (holding-lock ((display-event-queue-lock ,disp) ,disp "CLX Event Queue Lock"
		      ,@(and timeout `(:timeout ,timeout)))
	 ,@body))))

(defun open-display (host  &rest options &key (display 0) protocol
		     authorization-name authorization-data &allow-other-keys)
  ;; Implementation specific routine to setup the buffer for a specific host and display.
  ;; This must interface with the local network facilities, and will probably do special
  ;; things to circumvent the nework when displaying on the local host.
  ;;
  ;; A string must be acceptable as a host, but otherwise the possible types
  ;; for host and protocol are not constrained, and will likely be very
  ;; system dependent.  The default protocol is system specific.  Authorization,
  ;; if any, is assumed to come from the environment somehow.
  (declare (type integer display)
	   (dynamic-extent options))
  (declare (values display))
  ;; PROTOCOL is the network protocol (something like :TCP :DNA or :CHAOS). See OPEN-X-STREAM.
  (let* ((stream (open-x-stream host display protocol))
	 (disp (apply #'make-buffer
		      #x2000 'make-display-internal
		      :host host
		      :display display
		      :output-stream stream
		      :input-stream stream
		      :allow-other-keys t
		      options))
	 (ok-p nil))
    (unwind-protect
	(progn
	  (display-connect disp
			   :authorization-name authorization-name
			   :authorization-data authorization-data)
	  (initialize-resource-allocator disp)
	  (initialize-predefined-atoms disp)
	  (initialize-extensions disp)
	  (setq ok-p t))
      (unless ok-p (close-display disp :abort t)))
    disp))

(defun display-force-output (display)
  ; Output is normally buffered, this forces any buffered output to the server.
  (declare (type display display))
  (with-display (display)
    (buffer-force-output display)))

(defun close-display (display &key abort)
  ;; Close the host connection in DISPLAY
  (declare (type display display))
  (close-buffer display :abort abort))

(defun display-connect (display &key authorization-name authorization-data)
  (unless authorization-name (setq authorization-name ""))
  (unless authorization-data (setq authorization-data ""))
  (with-buffer-output (display :sizes (8 16))
    (card8-put
      0
      (ecase (display-byte-order display)
	(:lsbfirst #x6c)   ;; Ascii lowercase l - Least Significant Byte First
	(:msbfirst #x42))) ;; Ascii uppercase B -  Most Significant Byte First
    (card16-put 2 *protocol-major-version*)
    (card16-put 4 *protocol-minor-version*)
    (card16-put 6 (length authorization-name))
    (card16-put 8 (length authorization-data))
    (write-sequence-char display 12 authorization-name)
    (write-sequence-char display
			 (lround (+ 12 (length authorization-name))) authorization-data))
  (buffer-force-output display)
  (let ((reply-buffer nil))
    (declare (type (or null reply-buffer) reply-buffer))
    (unwind-protect
	(progn
	  (setq reply-buffer (allocate-reply-buffer #x1000))
	  (with-buffer-input (reply-buffer :sizes (8 16 32))
	    (buffer-input display buffer-bbuf 0 8)
	    (let ((success (boolean-get 0))
		  (reason-length (card8-get 1))
		  (major-version (card16-get 2))
		  (minor-version (card16-get 4))
		  (total-length (card16-get 6))
		  vendor-length
		  num-roots
		  num-formats)
	      (declare (ignore total-length))
	      (unless success
		(x-error 'connection-failure
			 :major-version major-version
			 :minor-version minor-version
			 :host (display-host display)
			 :display (display-display display)
			 :reason
			 (progn (buffer-input display buffer-bbuf 0 reason-length)
				(string-get reason-length 0 :reply-buffer reply-buffer))))
	      (buffer-input display buffer-bbuf 0 32)
	      (setf (display-protocol-major-version display) major-version)
	      (setf (display-protocol-minor-version display) minor-version)
	      (setf (display-release-number display) (card32-get 0))
	      (setf (display-resource-id-base display) (card32-get 4))
	      (setf (display-resource-id-mask display) (card32-get 8))
	      (setf (display-motion-buffer-size display) (card32-get 12))
	      (setq vendor-length (card16-get 16))
	      (setf (display-max-request-length display) (card16-get 18))
	      (setq num-roots (card8-get 20))
	      (setq num-formats (card8-get 21))
	      ;; Get the image-info
	      (setf (display-image-lsb-first-p display) (zerop (card8-get 22)))
	      (let ((format (display-bitmap-format display)))
		(declare (type bitmap-format format))
		(setf (bitmap-format-lsb-first-p format) (zerop (card8-get 23)))
		(setf (bitmap-format-unit format) (card8-get 24))
		(setf (bitmap-format-pad format) (card8-get 25)))
	      (setf (display-min-keycode display) (card8-get 26))
	      (setf (display-max-keycode display) (card8-get 27))
	      ;; 4 bytes unused
	      ;; Get the vendor string
	      (buffer-input display buffer-bbuf 0 (lround vendor-length))
	      (setf (display-vendor-name display)
		    (string-get vendor-length 0 :reply-buffer reply-buffer))
	      ;; Initialize the pixmap formats
	      (dotimes (i num-formats) ;; loop gathering pixmap formats
		(buffer-input display buffer-bbuf 0 8)
		(push (make-pixmap-format :depth (card8-get 0)
					  :bits-per-pixel (card8-get 1)
					  :scanline-pad (card8-get 2))
						; 5 unused bytes
		      (display-pixmap-formats display)))
	      (setf (display-pixmap-formats display)
		    (nreverse (display-pixmap-formats display)))
	      ;; Initialize the screens
	      (dotimes (i num-roots)
		(buffer-input display buffer-bbuf 0 40)
		(let* ((root (make-window :id (card32-get 0) :display display))
		       (root-visual (card32-get 32))
		       (default-colormap
			 (make-colormap :id (card32-get 4)
					:display display))
		       (screen
			 (make-screen
			   :root root
			   :default-colormap default-colormap
			   :white-pixel (card32-get 8)
			   :black-pixel (card32-get 12)
			   :event-mask-at-open (card32-get 16)
			   :width  (card16-get 20)
			   :height (card16-get 22)
			   :width-in-millimeters  (card16-get 24)
			   :height-in-millimeters (card16-get 26)
			   :min-installed-maps (card16-get 28)
			   :max-installed-maps (card16-get 30)
			   :backing-stores (member8-get 36 :never :when-mapped :always)
			   :save-unders-p (boolean-get 37)
			   :root-depth (card8-get 38)))
		       (num-depths (card8-get 39))
		       (depths nil))
		  ;; Save root window for event reporting
		  (save-id display (window-id root) root)
		  ;; Create the depth AList for a screen, (depth . visual-infos)
		  (dotimes (j num-depths)
		    (buffer-input display buffer-bbuf 0 8)
		    (let ((depth (card8-get 0))
			  (num-visuals (card16-get 2))
			  (visuals nil)) ;; 4 bytes unused
		      (dotimes (k num-visuals)
			(buffer-input display buffer-bbuf 0 24)
			(let ((visual (make-visual-info
					:id (card32-get 0)
					:display display
					:class (member8-get 4 :static-gray :gray-scale
							    :static-color :pseudo-color
							    :true-color :direct-color)
					:bits-per-rgb (card8-get 5)
					:colormap-entries (card16-get 6)
					:red-mask (card32-get 8)
					:green-mask (card32-get 12)
					:blue-mask (card32-get 16)
					;; 4 bytes unused
					)))
			  (save-id display (visual-info-id visual) visual)
			  (push visual visuals)))
		      (push (cons depth (nreverse visuals)) depths)))
		  (setf (screen-depths screen) (nreverse depths))
		  (setf (screen-root-visual-info screen)
			(setf (colormap-visual-info default-colormap)
			      (visual-info display root-visual)))
		  (push screen (display-roots display))))
	      (setf (display-roots display) (nreverse (display-roots display)))
	      (setf (display-default-screen display) (first (display-roots display))))))
      (when reply-buffer
	(deallocate-reply-buffer reply-buffer))))
  display)

(defun display-protocol-version (display)
  (declare (type display display))
  (declare (values major minor))
  (values (display-protocol-major-version display)
	  (display-protocol-minor-version display)))

(defun display-vendor (display)
  (declare (type display display))
  (declare (values name release))
  (values (display-vendor-name display)
	  (display-release-number display)))

(defun display-nscreens (display)
  (declare (type display display))
  (length (display-roots display)))

#+comment ;; defined by the DISPLAY defstruct
(defsetf display-error-handler (display) (handler)
  ;; All errors (synchronous and asynchronous) are processed by calling an error
  ;; handler in the display.  If handler is a sequence it is expected to contain
  ;; handler functions specific to each error; the error code is used to index the
  ;; sequence, fetching the appropriate handler.  Any results returned by the handler
  ;; are ignored; it is assumed the handler either takes care of the error
  ;; completely, or else signals. For all core errors, the keyword/value argument
  ;; pairs are:
  ;;    :display display
  ;;    :error-key error-key
  ;;    :major integer
  ;;    :minor integer
  ;;    :sequence integer
  ;;    :current-sequence integer
  ;; For :colormap, :cursor, :drawable, :font, :gcontext, :id-choice, :pixmap, and
  ;; :window errors another pair is:
  ;;    :resource-id integer
  ;; For :atom errors, another pair is:
  ;;    :atom-id integer
  ;; For :value errors, another pair is:
  ;;    :value integer
  )

  ;; setf'able
  ;; If defined, called after every protocol request is generated, even those inside
  ;; explicit with-display's, but never called from inside the after-function itself.
  ;; The function is called inside the effective with-display for the associated
  ;; request.  Default value is nil.  Can be set, for example, to
  ;; #'display-force-output or #'display-finish-output.

(defvar *inside-display-after-function* nil)

(defun display-invoke-after-function (display)
  ; Called after every protocal request is generated
  (declare (type display display))
  (when (and (display-after-function display)
	     (not *inside-display-after-function*))
    (let ((*inside-display-after-function* t)) ;; Ensure no recursive calls
      (funcall (display-after-function display) display))))

(defun display-finish-output (display)
  ;; Forces output, then causes a round-trip to ensure that all possible
  ;; errors and events have been received.
  (declare (type display display))
  (with-buffer-request-and-reply (display *x-getinputfocus* 16 :sizes (8 32))
       ()
    )
  ;; Report asynchronous errors here if the user wants us to.
  (report-asynchronous-errors display :after-finish-output))

(defparameter
  *request-names*
  '#("error" "CreateWindow" "ChangeWindowAttributes" "GetWindowAttributes"
     "DestroyWindow" "DestroySubwindows" "ChangeSaveSet" "ReparentWindow"
     "MapWindow" "MapSubwindows" "UnmapWindow" "UnmapSubwindows"
     "ConfigureWindow" "CirculateWindow" "GetGeometry" "QueryTree"
     "InternAtom" "GetAtomName" "ChangeProperty" "DeleteProperty"
     "GetProperty" "ListProperties" "SetSelectionOwner" "GetSelectionOwner"
     "ConvertSelection" "SendEvent" "GrabPointer" "UngrabPointer"
     "GrabButton" "UngrabButton" "ChangeActivePointerGrab" "GrabKeyboard"
     "UngrabKeyboard" "GrabKey" "UngrabKey" "AllowEvents"
     "GrabServer" "UngrabServer" "QueryPointer" "GetMotionEvents"
     "TranslateCoords" "WarpPointer" "SetInputFocus" "GetInputFocus"
     "QueryKeymap" "OpenFont" "CloseFont" "QueryFont"
     "QueryTextExtents" "ListFonts" "ListFontsWithInfo" "SetFontPath"
     "GetFontPath" "CreatePixmap" "FreePixmap" "CreateGC"
     "ChangeGC" "CopyGC" "SetDashes" "SetClipRectangles"
     "FreeGC" "ClearToBackground" "CopyArea" "CopyPlane"
     "PolyPoint" "PolyLine" "PolySegment" "PolyRectangle"
     "PolyArc" "FillPoly" "PolyFillRectangle" "PolyFillArc"
     "PutImage" "GetImage" "PolyText8" "PolyText16"
     "ImageText8" "ImageText16" "CreateColormap" "FreeColormap"
     "CopyColormapAndFree" "InstallColormap" "UninstallColormap" "ListInstalledColormaps"
     "AllocColor" "AllocNamedColor" "AllocColorCells" "AllocColorPlanes"
     "FreeColors" "StoreColors" "StoreNamedColor" "QueryColors"
     "LookupColor" "CreateCursor" "CreateGlyphCursor" "FreeCursor"
     "RecolorCursor" "QueryBestSize" "QueryExtension" "ListExtensions"
     "SetKeyboardMapping" "GetKeyboardMapping" "ChangeKeyboardControl" "GetKeyboardControl"
     "Bell" "ChangePointerControl" "GetPointerControl" "SetScreenSaver"
     "GetScreenSaver" "ChangeHosts" "ListHosts" "ChangeAccessControl"
     "ChangeCloseDownMode" "KillClient" "RotateProperties" "ForceScreenSaver"
     "SetPointerMapping" "GetPointerMapping" "SetModifierMapping" "GetModifierMapping"))
