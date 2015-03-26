(** We define here instances of the reification mecanism. *)

Require Import Setoid.
Require Import NArith PArith ZArith.
Require Import Ascii String.
Require Import List.

From CoqFFI Require Import reifiable coqFFI.

Set Implicit Arguments.

Import ListNotations SExpr Reifiable.

Reification for unit.
Existing Instance unit_reify.

Reification for bool.
Existing Instance bool_reify.

Reification for positive.
Existing Instance positive_reify.

Reification for N.
Existing Instance N_reify.

Reification for Z.
Existing Instance Z_reify.

Reification for nat.
Existing Instance nat_reify.

(** A product type is reifiable. *)
(*
Instance Product (T1 T2: Type) `{r1: t T1} `{r2: t T2}
  : t (T1 * T2) := New
  (fun v =>
    B (Export (fst v)) (Export (snd v)))
  (fun s =>
    match s with
    | I => (Import I, Import I)
    | B s1 s2 => (Import s1, Import s2)
    end).

(** A sum type is reifiable. *)
Instance Sum (T1 T2: Type) `{r1: t T1} `{r2: t T2}
  : t (T1 + T2) := New
  (fun v =>
    match v with
    | inl v' => B I (Export v')
    | inr v' => B (B I I) (Export v')
    end)
  (fun v =>
    match v with
    | I => inl (Import I)
    | B I s' => inl (Import s')
    | B _ s' => inr (Import s')
    end).

(** A list is reifiable. *)
Instance List (T: Type) `{r: t T}
  : t (list T) := New
  (fix export v :=
    match v with
    | nil => I
    | cons x v' => B (Export x) (export v')
    end)
  (fix import s :=
    match s with
    | I => nil
    | B s1 s2 => cons (Import s1) (import s2)
    end).
*)

Reification for ascii.
Existing Instance ascii_reify.

Reification for string.
Existing Instance string_reify.

(*
Instance option (T : Type) `{t T} : t (option T) := New
  (fun o =>
     match o with
     | None => I
     | Some x => B I (Export x)
     end)
  (fun s =>
     match s with
     | B I v => Some (Import v)
     | _ => None
   end).
*)

(*
finition pack3 (x y z : SExpr.t) :=
B (B x y) z.

finition export2 T U `{Reifiable.t T, Reifiable.t U} (x : T) (y : U) :=
B (Export x) (Export y).

finition export3 T U V `{Reifiable.t T, Reifiable.t U, Reifiable.t V} (x : T) (y : U) (z : V) :=
pack3 (Export x) (Export y) (Export z).

finition export4 T U V W `{Reifiable.t T, Reifiable.t U, Reifiable.t V, Reifiable.t W}
                 (w : T) (x : U) (y : V) (z : W) :=
B (pack3 (Export w) (Export x) (Export y)) (Export z).

(** The above definitions are sound. *)
Module Facts.
  Lemma MorphismIsSound: forall (A B: Type) (r: t B)
    (export: A -> B) (import: B -> A),
    (forall (v: A), import (export v) = v) -> IsSound r ->
    IsSound (Morphism r export import).
    intros A B r export import Ha Hr v.
    simpl.
    now rewrite Hr.
  Qed.
  
  Lemma UnitIsSound: IsSound Unit.
    intro v.
    now destruct v.
  Qed.
  
  Lemma BoolIsSound: IsSound Bool.
    intro v.
    now destruct v.
  Qed.
  
  Lemma BinPosIsSound: IsSound BinPos.
    intro v.
    induction v; trivial;
    now rewrite <- IHv at 2.
  Qed.
  
  Lemma BinNatIsSound: IsSound BinNat.
    intro v.
    destruct v; trivial.
    simpl.
    now rewrite BinPosIsSound.
  Qed.
  
  Lemma NatIsSound: IsSound Nat.
    intro v.
    unfold Nat.
    rewrite MorphismIsSound; trivial.
      exact Nat2N.id.
      
      exact BinNatIsSound.
  Qed.
  
  Lemma ProductIsSound: forall (T1 T2: Type) (r1: t T1) (r2: t T2),
    IsSound r1 -> IsSound r2 -> IsSound (Product T1 T2).
    intros T1 T2 r1 r2 H1 H2 v.
    destruct v as [v1 v2].
    simpl.
    now rewrite H1; rewrite H2.
  Qed.
  
  Lemma SumIsSound: forall (T1 T2: Type) (r1: t T1) (r2: t T2),
    IsSound r1 -> IsSound r2 -> IsSound (Sum T1 T2).
    intros T1 T2 r1 r2 H1 H2 v.
    destruct v as [v1 | v2]; simpl.
      now rewrite H1.
      
      now rewrite H2.
  Qed.
  
  Lemma ListIsSound: forall (T: Type) (r: t T),
    IsSound r -> IsSound (List T).
    intros T r H v.
    induction v; trivial.
    rewrite <- IHv at 2.
    simpl.
    now rewrite H.
  Qed.
End Facts.

End Reifiable.
*)