; Load everything (for interactive use)
; $Id$
(module kanren
  (include "lib/bigloo-specific.scm")
  (include "lib/kanren.ss")

  (include "examples/type-inference.scm")
  (include "examples/typeclasses.scm")
  (include "examples/zebra.scm")
  (include "examples/mirror.scm")
  (include "examples/mirror-equ.scm")
  (include "examples/deduction.scm")
)
;(load "benchmarks/alg-complexity.scm") ; must be last