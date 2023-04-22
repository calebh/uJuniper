# Micro-formalization of the Juniper programming language.

Evaluated with: Coq 8.16.1

To verify the correctness of the proofs and view the examples, ensure that PLF is compiled - specifically the Imp, Maps, Norm, and Smallstep modules. Then open one of the .v files in the proofs folder in your favorite Coq editor. Execute until the end to verify correctness.

The following files can be found in the proofs folder:

* uJuniperLang.v: Contains the language ASTs, small step evaluation rules and typing rules
* soundess.v: Contains all the lemmas and theorems related to language soundness
* examples.v: Holds the string concatenation example
* ListExtensions.v: Contains miscellaneous list manipulation functions used by other modules.