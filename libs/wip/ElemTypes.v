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

Require Import Mapping.
Require Import Types.

Module ValElem <: ElemType.
  Definition elt := value.
  Definition elt_zero := 0.
  Definition elt_max := MAX_UINT256.
  Definition elt_add_raw := Nat.add.
  Definition elt_add := plus_with_overflow.
  Definition elt_sub := minus_with_underflow.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_add_raw_comm:
    forall x y, elt_add_raw x y = elt_add_raw y x.
  Proof.
    auto with arith.
  Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    unfold elt_eq; reflexivity.
  Qed.

  Lemma elt_zero_add:
    forall x, elt_add elt_zero x = x.
  Proof.
    auto.
  Qed.

  Lemma elt_zero_add':
    forall x, elt_add x elt_zero = x.
  Proof.
    intros.
    unfold elt_add, elt_zero.
    rewrite plus_safe_rhs0; auto.
  Qed.
End ValElem.

Module AddrElem <: ElemType.
  Definition elt := address.
  Definition elt_zero := 0.
  Definition elt_max := MAX_UINT256.
  Definition elt_add_raw := Nat.add.
  Definition elt_add := plus_with_overflow.
  Definition elt_sub := minus_with_underflow.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_add_raw_comm:
    forall x y, elt_add_raw x y = elt_add_raw y x.
  Proof.
    auto with arith.
  Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    unfold elt_eq; reflexivity.
  Qed.

  Lemma elt_zero_add:
    forall x, elt_add elt_zero x = x.
  Proof.
    auto.
  Qed.

  Lemma elt_zero_add':
    forall x, elt_add x elt_zero = x.
  Proof.
    intros.
    unfold elt_add, elt_zero.
    rewrite plus_safe_rhs0; auto.
  Qed.
End AddrElem.

Module BoolElem <: ElemType.
  Definition elt := bool.
  Definition elt_zero := false.
  Definition elt_max := true.
  Definition elt_add_raw := orb.
  Definition elt_add := orb.
  Definition elt_sub := andb.
  Definition elt_eq := fun (b b': elt) => b = b'.

  Lemma elt_add_raw_comm:
    forall x y, elt_add_raw x y = elt_add_raw y x.
  Proof.
    auto with bool.
  Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    unfold elt_eq; reflexivity.
  Qed.

  Lemma elt_zero_add:
    forall x, elt_add elt_zero x = x.
  Proof.
    auto.
  Qed.

  Lemma elt_zero_add':
    forall x, elt_add x elt_zero = x.
  Proof.
    auto with bool.
  Qed.
End BoolElem.