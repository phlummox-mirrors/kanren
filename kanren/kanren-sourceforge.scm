; Evaluation of this file yields an HTML document
; $Id$

(define Content
'(html:begin
  (Header
   (title "A declarative logic programming system")
   (description "An applicative logic programming system with a
declarative set-theoretical semantics, and its applications")
   (Date-Revision-yyyymmdd "20040820")
   (Date-Creation-yyyymmdd "20040121")
   (keywords "Logic Programming, meta-logic programming, relations,
iterative deepening, proof assistant, Scheme")
   (AuthorAddress "oleg-at-okmij.org")
   (long-title "A declarative applicative logic programming system")
   )

  (body
   (navbar
     ("Home" "http://kanren.sourceforge.net")
     ("Docs" "#Documentation")
     ("Sample" "#Sample")
     ("Availability" "#Availability")
     ("CVS" "http://sourceforge.net/cvs/?group_id=99654")
     ("Summary" "http://sourceforge.net/projects/kanren/")
     ;("Discussion" "http://sourceforge.net/mail/?group_id=99654")
     ;("News" "http://sourceforge.net/news/?group_id=99654")
     ;("Related" "#KANREN-related")
     )


   (page-title)

   (a (@ (href "http://sourceforge.net")) " "
      (img (@ (src "http://sourceforge.net/sflogo.php?group_id=99654")
	      (width "88") (height "31") (border "0")
	      (alt "SourceForge Logo"))))

   (p (em "KANREN") " is a declarative logic programming system with
first-class relations, embedded in a pure functional subset of Scheme.
The system has a set-theoretical semantics, true unions, fair
scheduling, first-class relations, lexically-scoped logical variables,
depth-first and iterative deepening strategies.  The system achieves
high performance and expressivity without cuts.")
    (p
      "Applications of the system range from expert systems to
polymorphic type inference and overloading resolution, to model
checking and theorem proving. The system can be used as a meta-logic
system.")
    (p
      (em "KANREN") " works on any computer platform for which a
Scheme implementation exists (from PalmPilot and iPAQ to
Unix/Linux/Winxx/Mac workstations and servers to MindLego bricks). The
system can be compiled or interpreted. Being essentially a Scheme
library, KANREN can interact with the user through any graphical or
command-line interface provided by the host Scheme implementation.")

    (ul
      (li (local-ref "Sample"))
      (li (local-ref "mini"))
      (li (local-ref "Documentation"))
      (li (local-ref "Availability")
	(ul (li (local-ref "CVS"))
	    ;(li (local-ref "Distributions"))
	  ))
;       (li (local-ref "Related")
;       (li 
; 	(a (@ (href "http://lists.sourceforge.net/lists/listinfo/ssax-sxml"))
; 	  "KANREN Mailing list"))
      (li (a (@ (href "http://sourceforge.net/projects/kanren"))
	    "KANREN project summary page at SourceForge"))
      )

; Add the news section

   (Section 3 "Sample" " applications")

   (dl
     (dt (cvs-ref "examples/type-inference.scm"))
     (dd "Polymorphic type inference, including polymorphic let")

     (dt (cvs-ref "examples/zebra.scm"))
     (dd "The classic Zebra puzzle")

     (dt (cvs-ref "examples/typeclasses.scm"))
     (dd "Functional dependency satisfaction in Haskell typeclasses
and deriving counter-examples.  Overloading resolution for
Haskell typeclasses in open and closed worlds.  Our method can
typecheck more programs than it is currently possible in Haskell.")

     (dt (cvs-ref "examples/mirror.scm"))
     (dd "Structural induction proof.  We write an outline of an
inductive proof that mirroring a binary tree twice is the identity
transformation. The system fills out details and verifies that the
conclusion of the proof indeed follows from the given axioms. KANREN
is used as a meta-logic system to implement a backwards-chaining proof
verifier.")

     (dt (cvs-ref "examples/mirror-equ.scm"))
     (dd "Structural induction proof in equational theory. We can
truly write the equivalence axioms, including the symmetry axiom
" (code "(myeq a b) |- (myeq b a)") ". Try to do that in Prolog!")

     (dt (cvs-ref "examples/deduction.scm"))
     (dd "Proving the Deduction Theorem for Hilbert Propositional Calculus
 by induction. The example also demonstrates generating inductive hypotheses.")

     (dt (cvs-ref "examples/pure-bin-arithm.scm"))
     (dd "Pure, declarative, and constructive binary arithmetics:
Addition, multiplication, division with the remainder as sound and
complete, " (em "pure") ", declarative relations that can be used in
any mode and that recursively enumerate their domains. The relations
define arithmetics over base-2 non-negative numerals of " (em
"arbitrary") " size. If " (code "z") " is instantiated but " (code
"x") " and " (code "y") " are not, " (code "(++o x y z)") " delivers
all non-negative numbers that add to " (code "z") " and " (code "(**o
x y z)") " computes " (em "all") " factorizations of " (code "z") ".")

     (dt (cvs-ref "benchmarks/"))
     (dd "Standard Prolog benchmarks: nrev, query, qsort, queens, etc. --
re-written for KANREN.")
     )

   (Section 3 "mini" "KANREN")

   (p "miniKANREN is a simplified KANREN without many bells, whistles,
and optimizations of the full system. The goal of the simplifications was
to make miniKANREN easier to explain. Many tutorials below are specifically
miniKANREN tutorials. Incidentally, miniKANREN is not that inefficient.")


   (Section 3 "Documentation" " and tutorials")

   (dl
     (dt "Detailed description of the system")
     (dd 
       "<" (a (@ (href "http://www.cs.indiana.edu/l/www/classes/b521/qs.ps"))
	     "http://www.cs.indiana.edu/l/www/classes/b521/qs.ps") ">" (br)
       "<" (a (@ (href "http://www.cs.indiana.edu/l/www/classes/b521/qs.pdf"))
	     "http://www.cs.indiana.edu/l/www/classes/b521/qs.pdf") ">" (br)
       (n_)
    )

   (dt "C311 class notes (Indiana University)")
   (dd "<" (a (@ (href "http://www.cs.indiana.edu/l/www/classes/c311/"))
	     "http://www.cs.indiana.edu/l/www/classes/c311/") ">")

   (dt "miniKANREN tutorials (PDF), from the C311 class notes page")
   (dd 
     (a (@ (href "http://www.cs.indiana.edu/l/www/classes/c311/miniaop.pdf"))
	     "Outcome-Oriented Programming") (br)
     (a (@ (href "http://www.cs.indiana.edu/l/www/classes/c311/minirop.pdf"))
	     "Relation-Oriented Programming") (br)
     (a (@ (href "http://www.cs.indiana.edu/l/www/classes/c311/minilop.pdf"))
	     "Logic-Oriented Programming") (br)
     (a (@ (href "http://www.cs.indiana.edu/l/www/classes/c311/miniunify.pdf"))
	     "Understanding Unification") (br)
     (a (@ (href "http://www.cs.indiana.edu/l/www/classes/c311/minitypes.pdf"))
	     "Type Inference and Type Habitation") (br)
     (n_)
    )

   (dt (cvs-ref "docs/Substitution-Properties.txt"))
   (dd
     "Properties of Substitutions: "
     "Nine propositions about substitutions and the KANREN
unifier. The propositions justify several pieces of KANREN code, e.g.,
a " (code "head-let") " form of relation. The propositions were put
forth and proven " (em "before") " the code was written.")
     )


   (Section 3 "Availability")
   (p "The current version of KANREN is 4.11. KANREN is OpenSource,
distributed under the MIT license.")
   (p
     "KANREN has been tested on the following Scheme systems:"
     (br)
     "Petite Chez Scheme, Chez Scheme, SCM, Gauche.")

;    (Section 3 "Distributions")
;    (p "KANREN download site at SourceForge:"
;       (URL "http://sf.net/project/showfiles.php?group_id=99654"))

  (Section 3 "CVS" " Tree")
  (p (a (@ (href "http://sourceforge.net/cvs/?group_id=99654"))
	"The CVS Tree")
     " includes the complete KANREN code, extensive documentation, a tutorial,
validation tests, as well as several sample applications.")
  (p "You can "
     (a (@ (href "http://cvs.sourceforge.net/viewcvs.py/kanren"))
	"browse the files in the CVS tree")
     " from any web browser.")


;    (dl

;     (dt (a (@ (href  "http://sourceforge.net/tracker/?group_id=99654"))
; 	   "Trackers"))
;     (dd "You can use a tracker to make a suggestion, to request a
; feature, or to report a problem.")

;     (dt (a (@ (href "http://sourceforge.net/forum/?group_id=99654"))
; 	   "Forums"))
;     (dd "You can browse, search, and post messages related to KANREN and SXML"
; 	(br) (n_))

;     (dt (a (@ (href "http://sourceforge.net/docman/?group_id=99654"))
; 	   "Doc Manager"))
;     (dt (a (@ (href "http://sourceforge.net/pm/?group_id=99654"))
; 	   "Task Manager"))
;     (dt (a (@ (href "http://sourceforge.net/survey/?group_id=99654"))
; 	   "Surveys"))
;     )

   (footer)

)))

;(pp Content)

;========================================================================
;			HTML generation

; IMPORT
; SXML-to-HTML-ext.scm and all of its imports


; Generating HTML

(define (generate-HTML Content)
 (SRV:send-reply
  (pre-post-order Content
   (generic-web-rules Content 
     `((who *preorder*
	 . ,(lambda (tag . elems)
	      (pre-post-order `((br) . ,elems) universal-conversion-rules)))

		; A reference to an anchor in the present file
		; (local-ref target . title)
		; If title is given, generate a regular
		;	<a href="#target">title</a>
		; Otherwise, transform the content so that a
		; construct that may generate an anchor 'target' (such
		; as Section) is re-written to the
		; title SXML. All other constructs re-write to
		; nothing.
     (local-ref
      *preorder*
      . ,(lambda (tag target . title)
	   (let
	       ((title
		 (if (pair? title) title	; it is given explicitly
		     (pre-post-order Content
		       `((*text* . ,(lambda (trigger str) '()))
			 (*default*
			  . ,(lambda (tag . elems)
			       (let ((first-sign (signif-tail elems)))
				 (if first-sign
				     (let ((second-sign
					    (signif-tail (cdr first-sign))))
				       (assert (not second-sign))
				       (car first-sign))
				     '()))))
			 (Section
			  *preorder*
			  . ,(lambda (tag level key . elems)
			       (if (equal? key target)
				   (list key elems)
				   '()))))))))
	     (assert (pair? title) report: target)
	     (cerr "title: " title nl)
	     (post-order 
	      `(a (@ (href #\# ,target)) ,title)
	      universal-conversion-rules))))

       ; cvs-ref KANREN-relative path
       (cvs-ref
	 *macro*
	 . ,(lambda (tag path)
	      `(a (@ (href 
		       "http://cvs.sourceforge.net/viewcvs.py/kanren/kanren/"
		       ,path))
		 (code ,path))))

       ; (navbar (title url) ...)
       (navbar
	*preorder*
	. ,(lambda (tag . elems)
	     (post-order
	       `(p (hr (@ (size 1) (noshade)))
		  (div (@ (align "center"))
		    ,(map
		     (lambda (title-url)
		       `((a (@ (href ,(cadr title-url))) ,(car title-url))
			 (n_) "|" (n_)))
		     elems))
		  (hr (@ (size 1) (noshade))) (br))
	       universal-conversion-rules)))

       )))))

(generate-HTML Content)

; LocalWords:  href cvs dd typecheck dt OpenSource Chez
