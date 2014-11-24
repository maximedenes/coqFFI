Declare ML Module "ocamlbindPlugin".

Extraction Language Ocaml.

Require Import reifiable.

Parameter save_input : SExpr.t -> unit.
Extract Constant save_input => "OcamlbindState.save_input".