Set Implicit Arguments.

Declare ML Module "ocamlbindPlugin".

Extraction Language Ocaml.

Require Import reifiable.

Parameter save_input : SExpr.t -> unit.
Parameter save_input_unsafe : forall T : Type, T -> unit.
Extract Constant save_input => "OcamlbindState.save_input".
Extract Constant save_input_unsafe => "OcamlbindState.save_input".
