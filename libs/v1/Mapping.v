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

Require Export Types.
Require Export BNat.
Require Export TMap.
Require Export Nat.

(* Modelling of Solidity mapping based on total map library. *)

(*
   address-to-value, models the Solidity type:
    "mapping (address => uint256)"
 *)
Definition a2v := @tmap address value.

(*
   address-to-address-to-value, models the Solidity type:
    "mapping (address => mapping (address => uint256))"
 *)
Definition aa2v := @tmap (prod address address) value.



Instance address_Domain : BEq address :=
{
  beq := BNat.beq_nat;
  beq_true_eq := BNat.beq_true_eq;
  beq_false_neq := BNat.beq_false_neq;
  eq_beq_true := BNat.eq_beq_true;
  neq_beq_false := BNat.neq_beq_false;
}.

Instance value_Range : BZero :=
{
  zero := (0: value);
}.

Definition beq_addrx2 (a1 a2: (prod address address)): bool :=
    match a1, a2 with
    | (x1, y1), (x2, y2) => andb (beq_nat x1 x2) (beq_nat y1 y2)
    end.

Instance addressx2_Domain : BEq (prod address address) :=
{
  beq a a' := beq_addrx2 a a';
}.
Proof.
  unfold beq_addrx2.
  intros [a1 a2] [a3 a4].
  intros.
  unfold andb in H.
  decbeqnat a1 a3.
  rewbnat H.
  rewbnat Hb.
  trivial.
  intros [a1 a2] [a3 a4].
  intros.
  unfold beq_addrx2 in H.
  unfold andb in H.
  decbeqnat a1 a3.
  rewbnat Hb.
  intro Hf.
  inversion Hf;subst.
  simplbnat.
  intro Hf.
  inversion Hf; subst.
  simplbnat.
  intros [a1 a2] [a3 a4].
  intros.
  unfold beq_addrx2.
  inversion H;subst.
  unfold andb.
  simplbnat.
  trivial.
  intros [a1 a2] [a3 a4].
  intros.
  unfold beq_addrx2.
  unfold andb.
  decbeqnat a1 a3.
  rewbnat Hb in H.
  decbeqnat a2 a4.
  rewbnat Hb0 in H.
  destruct (H (eq_refl _)).
  trivial.
  trivial.
Defined.

Opaque beq.

(* Section Test. *)
(*   Variable a a' a1 a2 a3: address. *)
(*   Variable v v' v1 v2 v3: value. *)

(*   Let m1 := tmap_upd tmap_emp 1 9. *)

(*   Eval compute in (m1 1). *)
(*   Eval compute in (m1 4). *)

(*   Let m2 := tmap_upd tmap_emp (1,5) 9. *)

(*   Eval compute in (m2 (1, 5)). *)
(*   Eval compute in (m2 (2, 4)). *)

(*   Let m3 := $0 $+ { 9 <- a}. *)

(*   Eval compute in (m3 9). *)

(*   Eval compute in (m3 4). *)

(*   Let m4 := $0 $+ {(1,5) <- v'}. *)

(*   Eval compute in (m4 (1, 5)). *)

(*   Eval compute in (m4 (4, 4)). *)

(* End Test. *)

Require Import Omega.

(* Modeling of over/underflow *)
Definition plus_with_overflow (lhs: value) (rhs: value) :=
  if (blt_nat (MAX_UINT256 - rhs) lhs)
  then (if (beq_nat rhs 0)
        then lhs
         else (lhs + rhs - MAX_UINT256 - 1))
  else (lhs + rhs).

Lemma plus_safe_lt : forall (x: value) (y: value),
    x <= MAX_UINT256 - y -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  assert (H1 : blt_nat (MAX_UINT256 - y) x = false).
  apply le_blt_false; trivial.
  rewrite H1; trivial.
Qed.

Lemma plus_safe_lhs0 : forall (x: value) (y: value),
    x = 0 -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  rewrite H; simpl.
  assert(Ht: blt_nat (MAX_UINT256 - y) 0 = false).
  simplbnat; trivial.
  rewrite Ht; trivial.
Qed.

Lemma plus_safe_rhs0 : forall (x: value) (y: value),
    y = 0 -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  rewrite H; simpl.
  destruct (blt_nat_dec (MAX_UINT256 - 0) x); rewrite e; trivial.
Qed.

Definition minus_with_underflow (lhs: value) (rhs: value) :=
  if (blt_nat lhs rhs) then (lhs + MAX_UINT256 + 1 - rhs) else (lhs - rhs).

Lemma minus_safe : forall (x: value) (y: value),
    x >= y -> minus_with_underflow x y = x - y.
Proof.
  intros.
  unfold minus_with_underflow.
  assert (H1 : blt_nat x y = false).
  apply le_blt_false; trivial.
  rewrite H1; trivial.
Qed.

Lemma minus_plus_safe: forall (x y : value),
    x <= MAX_UINT256 -> x >= y -> plus_with_overflow (minus_with_underflow x y) y = x.
Proof.
  intros x y Hhi Hlo.
  rewrite (minus_safe _ _ Hlo).
  assert (y <= x). auto with arith.
  assert (x - y <= MAX_UINT256 - y). apply ble_minus; auto.
  rewrite (plus_safe_lt _ _ H0).
  omega.
Qed.

(* Mapping update *)
Definition a2v_upd_inc (m: a2v) (a: address) (v:value) :=
  @tmap_upd address value address_Domain m a (plus_with_overflow (m a) v).

Definition a2v_upd_dec (m: a2v) (a: address) (v:value) :=
  @tmap_upd address value address_Domain m a (minus_with_underflow (m a) v).

Definition aa2v_upd_2 (m: aa2v) (a1: address) (a2: address) (v:value) :=
  @tmap_upd (prod address address) value addressx2_Domain m (a1, a2) v.

Definition aa2v_upd_inc (m: aa2v) (a1: address) (a2: address) (v:value) :=
  @tmap_upd (prod address address) value addressx2_Domain m (a1, a2) (plus_with_overflow (m (a1, a2)) v).

Definition aa2v_upd_dec (m: aa2v) (a1: address) (a2: address) (v:value) :=
  @tmap_upd (prod address address) value addressx2_Domain m (a1, a2) (minus_with_underflow (m (a1, a2)) v).

Notation "m $+ { k , k' <- v }" := (aa2v_upd_2 m k k' v) (at level 50, left associativity).

Notation "m $+ { k <- += v }" := (a2v_upd_inc m k v) (at level 50, left associativity).

Notation "m $+ { k <- -= v }" := (a2v_upd_dec m k v) (at level 50, left associativity).

Notation "m $+ { k , k' <- += v }" := (aa2v_upd_inc m k k' v) (at level 50, left associativity).

Notation "m $+ { k , k' <- -= v }" := (aa2v_upd_dec m k k' v) (at level 50, left associativity).

Lemma a2v_dec_inc_id:
  forall (m: a2v) (a: address) (v: value),
    m a <= MAX_UINT256 ->
    m a >= v ->
    m = m $+ { a <- -= v } $+ { a <- += v }.
Proof.
  intros m a v Hhi Hlo.
  unfold a2v_upd_inc, a2v_upd_dec, tmap_upd.
  apply tmap_extensionality.
  intros a'. destruct (beq_dec a a').
  - (* a = a' *)
    rewrite Nat.eqb_eq in H. subst a.
    rewrite (beq_refl _).
    rewrite (minus_plus_safe _ _ Hhi Hlo).
    reflexivity.
  - (* a <> a' *)
    rewrite H.
    reflexivity.
Qed.