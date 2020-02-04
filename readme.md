Nuprl: Proof Development System
--

from https://www.cs.cmu.edu/afs/cs/project/ai-repository/ai/areas/reasonng/atp/systems/nuprl/0.html

this is a slightly adapted ASDF-able version running on recent Common Lisp
implementation and new CLX.

To use it, you need a X11 server, an ANSI complaint CL with ASDF, and CLX from
Quicklisp.

`clx/` the CLX shipped within the original source, not recommended to use since
it isn't up to date.

`doc/` release notice and documentations

`ml/` ML tactics library

`sys/` The source for Nuprl

## start the system

```
CL-USER> (load "sys/nuprl.asd")
CL-USER> (asdf:load-system "nuprl")
;; now the base system has been loaded
CL-USER> (in-package "NUPRL")
;; do same setup
;; TODO: handle these to ASDF
NUPRL> (initialize)
NUPRL> (setf *nuprl-path-prefix* ...)
;; load tacits
NUPRL> (ml-load nil (complete-nuprl-path '(|ml|) '|load|))
NUPRL> (nuprl "")
;; have fun
```

## how to use
See `doc/refman/it.pdf`
