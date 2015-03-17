Set Implicit Arguments.

Declare ML Module "ocamlbindPlugin".

Extraction Language Ocaml.

Require Import reifiable.

Extract Inductive SExpr.t => "OcamlbindConstants.sexpr"
  [ "OcamlbindConstants.I" "OcamlbindConstants.B"].
