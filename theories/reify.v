(** We define here instances of the reification mecanism. *)

Require Import Setoid.
Require Import NArith PArith ZArith.
Require Import Ascii String.
Require Import List.

From CoqFFI Require Import reifiable coqFFI.

Set Implicit Arguments.
Set Printing All.

Import ListNotations.

Reification for unit.

Reification for bool.

Reification for positive.

Reification for N.

Reification for Z.

Reification for nat.

Reification for list.

Reification for prod.

Reification for sum.

Reification for ascii.

Reification for string.

Reification for option.