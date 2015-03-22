Set Implicit Arguments.

Declare ML Module "coqFFIPlugin".

Extraction Language Ocaml.

Require Import reifiable.

Extract Inductive SExpr.t => "CoqFFIConstants.sexpr"
  [ "CoqFFIConstants.I" "CoqFFIConstants.B"].
