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

(** A reifiable type is a type equipped with reification functions. *)
Module Reifiable.
  Import SExpr.
  
  Class t (T: Type): Type := New {
    Export: T -> SExpr.t;
    Import: SExpr.t -> option T}.
  
  (** We expect to get the original value from a reified one. *)
  Definition IsSound (T: Type) (r: t T): Prop :=
    forall (v: T), Import (Export v) = Some v.
  
  (** If we can reify [A] to [B] and reify [B], then we can reify [A]. *)
  Definition Morphism (A B: Type) (r: t B)
    (export: A -> B) (import: B -> A): t A := New
    (fun a => Export (export a))
    (fun s => option_map import (Import s)).

End Reifiable.
