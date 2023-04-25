# Micro-formalization of the Juniper programming language.

## Project Contents

Evaluated with: Coq 8.16.1

To verify the correctness of the proofs and view the examples, ensure that PLF is compiled - specifically the Imp, Maps, Norm, and Smallstep modules. Then open one of the .v files in the proofs folder in your favorite Coq editor. Execute until the end to verify correctness.

The following files can be found in the proofs folder:

* uJuniperLang.v: Contains the language ASTs, small step evaluation rules and typing rules
* soundess.v: Contains all the lemmas and theorems related to language soundness
* examples.v: Holds the string concatenation example. Typechecking for string concatenation as well as an example of concatenating the string "Hello " and "world" to form "Hello world".
* ListExtensions.v: Contains miscellaneous list manipulation functions used by other modules.

The following files can be found in the docs folder:

* uJuniperTypingRules.tex: source code for the typing rules PDF
* uJuniperTypingRules.pdf: typing rules for uJuniper in PDF form
* uJuniper Presentation.pdf: slides from in-class presentation

## Project Summary

uJuniper faithfully implements the core Juniper features surrounding arrays, but does not implement some important features such as mutation and loops. In uJuniper the only loop-like construct implemented is the mapi function, which in the real Juniper language could be implemented using mutation/loops. Algebraic datatypes and pattern matching are another feature that has not been implemented. In the uJuniper language, types must be explicitly given when variables are defined, whereas the real Juniper language has full type inference.

One additional consideration regarding arrays is that type level arithmetic is performed in the Gallina language, not in the uJuniper language. In some sense Gallina acts as a "template" or "macro" language in our implementation. Therefore the strength of the soundness proof is slighly lowered since this technicality is pushed outside of the theory of our language. Due to my desire to use the lia tactic, I could not find an easy way to resolve this issue. I did consider compiling uJuniper arithmetic operations to equivalent Gallina expressions, however there were issues around getting our hands on a Gallina variable of nat type for every free variable in the Juniper expression.

Despite these drawbacks, uJuniper faithfully implements many aspects of the true Juniper language, especially those around array capacities.