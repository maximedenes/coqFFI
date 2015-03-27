(** We define here instances of the reification mecanism. *)

Require Import Setoid.
Require Import NArith PArith ZArith.
Require Import Ascii String.
Require Import List.

From CoqFFI Require Import reifiable coqFFI.

Set Implicit Arguments.

Import ListNotations SExpr Reifiable.

Set Printing All.

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

Reification for list.
Existing Instance list_reify.

Reification for prod.
Existing Instance prod_reify.

Reification for sum.
Existing Instance sum_reify.

Reification for ascii.
Existing Instance ascii_reify.

Reification for string.
Existing Instance string_reify.

Reification for option.
Existing Instance option_reify.