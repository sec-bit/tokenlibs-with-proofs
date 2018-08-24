(*
  This file is part of the verified smart contract project of SECBIT Labs.

  Copyright 2018 SECBIT Labs

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public License
  as published by the Free Software Foundation, either version 3 of
  the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public License
  along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

Require Import Nat.
Require Import ZArith.
Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.DecidableTypeEx.

(*
   Types. All integer types are modeled as nat.
*)
Definition label := nat.
Definition value := nat.
Definition uint256 := nat.
Definition uint8 := nat.
Definition time := nat.
Definition address := nat.

Module Label_as_DT <: UsualDecidableType := Nat_as_DT.
Module UINT8_as_DT <: UsualDecidableType := Nat_as_DT.
Module UINT256_as_DT <: UsualDecidableType := Nat_as_DT.
Module Time_as_DT <: UsualDecidableType := Nat_as_DT.
Module Address_as_DT <: UsualDecidableType := Nat_as_DT.

(*
   Over/underflow is modeled in map update functions.
*)
Parameter MAX_UINT256 : uint256.

Definition plus_with_overflow (lhs: value) (rhs: value) :=
  if (Nat.ltb (MAX_UINT256 - rhs) lhs)
  then (if (Nat.eqb rhs 0)
        then lhs
         else (lhs + rhs - MAX_UINT256 - 1))
  else (lhs + rhs).

Lemma plus_safe_lt : forall (x: value) (y: value),
    x <= MAX_UINT256 - y -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  rewrite Nat.ltb_antisym.
  rewrite (proj2 (Nat.leb_le _ _) H).
  reflexivity.
Qed.

Lemma plus_safe_lhs0 : forall (x: value) (y: value),
    x = 0 -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  subst.
  reflexivity.
Qed.

Lemma plus_safe_rhs0 : forall (x: value) (y: value),
    y = 0 -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  subst. simpl.
  rewrite Nat.add_0_r.
  destruct (MAX_UINT256 - 0 <? x); reflexivity.
Qed.

Definition minus_with_underflow (lhs: value) (rhs: value) :=
  if (Nat.ltb lhs rhs) then (lhs + MAX_UINT256 + 1 - rhs) else (lhs - rhs).

Lemma minus_safe : forall (x: value) (y: value),
    x >= y -> minus_with_underflow x y = x - y.
Proof.
  intros.
  unfold minus_with_underflow.
  rewrite Nat.ltb_antisym.
  rewrite (proj2 (Nat.leb_le _ _) H).
  reflexivity.
Qed.

Lemma minus_plus_safe: forall (x y : value),
    x <= MAX_UINT256 -> x >= y -> plus_with_overflow (minus_with_underflow x y) y = x.
Proof.
  intros x y Hhi Hlo.
  rewrite (minus_safe _ _ Hlo).
  assert (y <= x). auto with arith.
  assert (x - y <= MAX_UINT256 - y). omega.
  rewrite (plus_safe_lt _ _ H0).
  omega.
Qed.

Lemma neq_decidable: forall (m n : nat), Decidable.decidable (m <> n).
Proof.
  intros m n.
  case (Nat.eq_dec m n); intros H.
  - right; auto.
  - left; auto.
Qed.

Lemma beq_decidable: forall (x y: bool), Decidable.decidable (x = y).
Proof.
  intros x y.
  destruct x; destruct y;
    solve [ (left; reflexivity) |
            (right; apply Bool.diff_true_false) |
            (right; apply Bool.diff_false_true) ].
Qed.