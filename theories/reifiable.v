(** Reification is the mechanism used to transmit values from OCaml to Coq. *)
Require Import Setoid.
Require Import NArith PArith ZArith.
Require Import Ascii String.
Require Import List.

Set Implicit Arguments.

Import ListNotations.

(** A S-expression, basically a binary tree, can reify almost any data value. *)
(** We use binary integers until Coq gets proper support for primitive integers
and their extraction. *)
Module SExpr.
  Inductive t: Type :=
  | I : positive -> t
  | B : t -> t -> t.
End SExpr.

(** We provide the codec in an unbundled way, because it is simpler for building
terms using type class inference (e.g. nested inductive types), interacts better
with the guard condition and gives better performance (no projections). *)

Module Encodable.

  Class t (T : Type) := encode : T -> SExpr.t.

End Encodable.

Module Decodable.

  Class t (T : Type) := decode : SExpr.t -> option T.

End Decodable.

Global Hint Extern 1 (Encodable.t _) => assumption : typeclass_instances.
Global Hint Extern 1 (Decodable.t _) => assumption : typeclass_instances.