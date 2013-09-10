<pre>
===============
   .+------+                                         +------+.
 .' |    .'|   (P)ROCESS                             |`.    | `.
+---+--+'  |             (A)LGEBRA                   |  `+--+---+
|   |  |   |                        (VE')RIFIER      |   |  |   |
|  ,+--+---+                                         +---+--+   |
|.'    | .'   (C) 2009-2013 F.Peschanski              `. |   `. |
+------+'                                               `+------+
              released under the GPL (cf. LICENSE)
===============
</pre>

This is a simple tool to describe models of concurrent systems and analyze
their behavioral properties.
Pave' is mostly a pedagogical tool to support the teaching of
concurrency theory, the calculus of communicating systems (CCS)
 and the undelying algorithmic aspects.
 
 It is a playground for the students so that they can see the
 analysis algorithms in action, and new features are added
 each year.
 
 The main current features implemented are the following ones:
 
 * relatively rudimentary parser for CCS definitions and expressions
 * efficient process normalization and structural congruence checking
 * naive strong bisimulation checking
 * generation of labelled transition systems from CCS terms
   (export to graphviz dot)
 * partition refinement algorithm for process minimization
   and faster strong bisimulation checking
 * support for CCS-by-value extensions
 * weak semantics (weak LTS, weak bisimulation checking).

The tool is developed in OCaml (and I really miss a good debugger !)

