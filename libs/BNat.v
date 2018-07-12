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

Require Export Bool.
Require Import Arith.

Definition A := nat.

Definition B := nat.

Definition zero := 0.

(* *********************************************************** *)

Theorem nat_eq_dec : forall a b : nat, {a = b} + {a <> b}.
Proof.
  intros; compare a b; auto.
Qed.

(* *********************************************************** *)

Fixpoint blt_nat (n m : nat) {struct n} : bool :=
  match n, m with
  | O, O => false
  | O, S _ => true
  | S _, O => false
  | S n', S m' => blt_nat n' m'
  end.

Lemma blt_irrefl :
  forall a : nat, blt_nat a a = false.
Proof.
  induction a; simpl; auto.
Qed.

Lemma blt_irrefl_Prop :
  forall a : nat, ~ (blt_nat a a = true).
Proof.
  induction a; simpl; auto.
Qed.

Lemma blt_asym :
  forall a b : nat, blt_nat a b = true
    -> blt_nat b a = false.
Proof.
  double induction a b; simpl; intros; auto.
Qed.

Lemma blt_O_Sn :
  forall n : nat, blt_nat O (S n) = true.
Proof.
  induction n; simpl; auto.
Qed.

Lemma blt_n_O : forall n,
  blt_nat n O = false.
Proof.
  induction n; simpl; auto.
Qed.

Lemma not_blt_n_O :
  forall n : nat, ~ (blt_nat n 0 = true).
Proof.
  induction n; simpl; auto.
Qed.

Lemma blt_true_lt :
  forall a b : nat, blt_nat a b = true -> a < b.
Proof.
  double induction a b; simpl; intros;
    auto with arith; try discriminate.
Qed.

Lemma blt_false_le :
  forall n m, blt_nat n m = false -> m <= n.
Proof.
  double induction n m; simpl; intros;
    auto with arith; discriminate.
Qed.

Lemma le_blt_false :
  forall n m, n <= m -> blt_nat m n = false.
Proof.
  double induction n m; simpl; intros;
    auto with arith.
  destruct (lt_n_O _ H0).
Qed.

Lemma lt_blt_true :
  forall a b : nat, a < b -> blt_nat a b = true.
Proof.
  double induction a b; simpl; intros;
    auto with arith.
  destruct (lt_irrefl 0 H).
  destruct (lt_n_O (S n) H0).
Qed.

Lemma blt_n_Sn :
  forall n : nat, blt_nat n (S n) = true.
Proof.
  induction n; simpl; intros; auto with arith.
Qed.

Lemma blt_S_eq :
  forall a b, blt_nat a b = blt_nat (S a) (S b).
Proof.
  trivial.
Qed.

Lemma blt_n_Sm :
  forall n m, blt_nat n m = true
    -> blt_nat n (S m) = true.
Proof.
  double induction n m; simpl; intros; auto with arith.
  discriminate.
Qed.

Lemma blt_n_mk :
  forall n m k, blt_nat n m = true
    -> blt_nat n (m + k) = true.
Proof.
  double induction n m; simpl; intros;
    auto with arith;  discriminate.
Qed.

Lemma blt_n_km :
  forall n m k, blt_nat n m = true
    -> blt_nat n (k + m) = true.
Proof.
  double induction n m; simpl; intros;
    auto with arith; try discriminate.
  replace (k + (S n0)) with ((S n0) + k);
    [idtac | auto with arith].
  simpl. trivial.
  replace (k + (S n0)) with ((S n0) + k);
    [idtac | auto with arith].
  simpl.
  replace (n0 + k) with (k + n0);
    [idtac | auto with arith].
  apply H0; trivial.
Qed.

Lemma blt_nat_dec : forall a b,
  {blt_nat a b = true} + {blt_nat a b = false}.
Proof.
  double induction a b; simpl; intros; try tauto || auto.
Qed.


(* *********************************************************** *)

Definition ble_nat (n m : nat) : bool :=
  match blt_nat m n with
    | true => false
    | false => true
  end.

(* *********************************************************** *)

Fixpoint beq_nat (n m : nat)  {struct n} : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n1, S m1 => beq_nat n1 m1
  end.

Lemma beq_refl : forall m, beq_nat m m = true.
Proof.
  induction m; simpl; intros; auto.
Qed.

Lemma beq_trans : forall m n k, beq_nat m n = true
  -> beq_nat n k = true
  -> beq_nat m k = true.
Proof.
  induction m; induction n; destruct k;
    simpl; intros; discriminate || auto.
  eapply IHm; eauto.
Qed.

Lemma beq_sym : forall m n b,
  beq_nat m n = b -> beq_nat n m = b.
Proof.
  double induction n m; simpl; intros;
    auto with arith; discriminate.
Qed.

Lemma beq_sym2 : forall m n,
  beq_nat m n = beq_nat n m.
Proof.
  double induction n m; simpl; intros;
    auto with arith; discriminate.
Qed.

Lemma beq_true_eq :
  forall n m, beq_nat n m = true
    -> n = m.
Proof.
  double induction n m; simpl; intros;
    auto with arith; discriminate.
Qed.

Lemma beq_false_neq :
  forall n m, beq_nat n m = false
    -> ~ (n = m).
Proof.
  double induction n m; simpl; intros;
    auto with arith; discriminate.
Qed.

Lemma eq_beq_true :
  forall n m, n = m
    -> beq_nat n m = true.
Proof.
  double induction n m; simpl; intros;
    auto with arith; discriminate.
Qed.

Lemma neq_beq_false :
  forall n m, ~ (n = m)
    -> beq_nat n m = false.
Proof.
  double induction n m; simpl; intros;
    auto with arith.
  destruct (H (refl_equal _)).
Qed.

Lemma beq_nat_dec : forall a b,
  {beq_nat a b = true} + {beq_nat a b = false}.
Proof.
  double induction a b; simpl; intros; try tauto || auto.
Qed.

(* *********************************************************** *)

Lemma blt_t_beq_f :
  forall m n, blt_nat m n = true
    -> beq_nat m n = false.
Proof.
  double induction n m; simpl; intros; auto with arith.
Qed.

Lemma bgt_t_beq_f :
  forall m n, blt_nat n m = true
    -> beq_nat m n = false.
Proof.
  double induction m n; simpl; intros; auto with arith.
Qed.

Lemma beq_t_blt_f :
  forall m n, beq_nat m n = true
    -> blt_nat m n = false.
Proof.
  double induction m n; simpl; intros; auto with arith.
Qed.

Lemma beq_t_bgt_f :
  forall m n, beq_nat m n = true
    -> blt_nat n m = false.
Proof.
  double induction n m; simpl; intros; auto with arith.
Qed.

Lemma blt_S_dec :
  forall n m,
    blt_nat n (S m) = true
    -> blt_nat n m = true \/ beq_nat n m = true.
Proof.
  intros n m H.
  assert (Hx:=blt_true_lt _ _ H).
  apply lt_n_Sm_le in Hx.
  apply le_lt_or_eq_iff in Hx.
  destruct Hx.
    left.
    apply lt_blt_true; trivial.
  right.
  apply eq_beq_true; trivial.
Qed.

(* *********************************************************** *)

Definition max_nat (m n : nat) : nat :=
  if blt_nat m n then n else m.

Lemma max_nat_elim_l : forall m n : nat,
  m <= max_nat m n.
Proof.
  unfold max_nat; intros m n.
  destruct (blt_nat_dec m n) as [Hb | Hb]; rewrite Hb.
  assert (Hb' := blt_true_lt m n Hb).
  auto with arith.
  auto with arith.
Qed.

Lemma max_nat_elim_r : forall m n : nat,
  n <= max_nat m n.
Proof.
  unfold max_nat; intros m n.
  destruct (blt_nat_dec m n) as [Hb | Hb]; rewrite Hb.
  auto with arith.
  assert (Hb' := blt_false_le m n Hb).
  auto with arith.
Qed.

Lemma ble_minus:
  forall (x y : nat),
    x <= y ->
    forall (z: nat),
      y <= z ->
      y - x <= z - x.
Proof.
  induction x; induction y; induction z; try auto with arith; intros.
  - inversion H0.
  - simpl. apply IHx; auto with arith.
Qed.

(* *********************************************************** *)

Ltac rewrite_bnat t :=
  match type of t with
    | blt_nat ?a ?b = ?c => rewrite t
    | beq_nat ?a ?b = ?c => rewrite t
  end.

Ltac rewrite_bnat_H t H :=
  match type of t with
    | blt_nat ?a ?b = ?c => rewrite t in H
    | beq_nat ?a ?b = ?c => rewrite t in H
  end.

Ltac rewrite_bnat_all t :=
  match goal with
    | |- context[(blt_nat ?a ?b)] => rewrite_bnat t; rewrite_bnat_all t
    | H : context[(blt_nat ?a ?b)] |- _ => rewrite_bnat_H t H; rewrite_bnat_all t
    | |- context[(beq_nat ?a ?b)] => rewrite_bnat t; rewrite_bnat_all t
    | H : context[(beq_nat ?a ?b)] |- _ => rewrite_bnat_H t H; rewrite_bnat_all t
    | _ => idtac
  end.

Ltac simplbnat :=
  match goal with
    (* blt rewrite directly *)
    | [H : blt_nat ?x ?y = ?f
      |- context [(blt_nat ?x ?y)]] =>
       rewrite H; simplbnat
    | [H : blt_nat ?x ?y = ?f,
       H0 : context [(blt_nat ?x ?y)]
      |- _ ] =>
       rewrite H in H0; simplbnat

    (* beq rewrite directly *)
    | [H : beq_nat ?x ?y = ?f
      |- context [(beq_nat ?x ?y)]] =>
       rewrite H; simplbnat
    | [H : beq_nat ?x ?y = ?f,
       H0 : context [(beq_nat ?x ?y)] |- _ ] =>
       rewrite H in H0; simplbnat

    (* blt -> beq *)
    | [H : blt_nat ?x ?y = true
      |- context[(beq_nat ?x ?y)]] =>
      rewrite (blt_t_beq_f x y H); simplbnat
    | [H : blt_nat ?x ?y = true,
       H0 : context[(beq_nat ?x ?y)] |- _ ] =>
      rewrite (blt_t_beq_f x y H) in H0; simplbnat

    (* bgt -> beq *)
    | [H : blt_nat ?y ?x = true
      |- context[(beq_nat ?x ?y)]] =>
      rewrite (bgt_t_beq_f x y H); simplbnat
    | [H : blt_nat ?y ?x = true,
       H0 : context[(beq_nat ?x ?y)] |- _ ] =>
      rewrite (bgt_t_beq_f x y H) in H0; simplbnat

    (* beq -> blt *)
    | [H : beq_nat ?y ?x = true
      |- context[(blt_nat ?x ?y)]] =>
      rewrite (beq_t_blt_f x y H); simplbnat
    | [H : beq_nat ?y ?x = true,
       H0 : context[(blt_nat ?x ?y)] |- _ ] =>
      rewrite (beq_t_blt_f x y H) in H0; simplbnat

    (* beq -> bgt *)
    | [H : beq_nat ?y ?x = true
      |- context[(blt_nat ?y ?x)]] =>
      rewrite (beq_t_bgt_f x y H); simplbnat
    | [H : beq_nat ?y ?x = true,
       H0 : context[(blt_nat ?y ?x)] |- _ ] =>
      rewrite (beq_t_bgt_f x y H) in H0; simplbnat

    (* blt_irrefl *)
    | [ |- context [blt_nat ?x ?x]] =>
      rewrite (blt_irrefl x); simplbnat
    | [H : context [blt_nat ?x ?x] |- _ ] =>
      rewrite (blt_irrefl x) in H; simplbnat

    (* blt_asym *)
    | [H : blt_nat ?x ?y = true
      |- context [blt_nat ?y ?x]] =>
      rewrite (blt_asym x y H); simplbnat
    | [H : blt_nat ?x ?y = true,
       H0 : context [blt_nat ?y ?x] |- _ ] =>
      rewrite (blt_asym x y H) in H0; simplbnat

    (* blt_O_Sn *)
    | [ |- context [(blt_nat O (S ?x))]] =>
      rewrite (blt_O_Sn x); simplbnat
    | [H : context [(blt_nat O (S ?x))] |- _ ] =>
      rewrite (blt_O_Sn x) in H; simplbnat

    (* blt_n_O *)
    | [ |- context [(blt_nat ?x O)]] =>
      rewrite (blt_n_O x); simplbnat
    | [H : context [(blt_nat ?x O)] |- _ ] =>
      rewrite (blt_n_O x) in H; simplbnat

    (* blt_n_Sn *)
    | [ |- context [(blt_nat ?x (S ?x))]] =>
      rewrite (blt_n_Sn x); simplbnat
    | [H : context [(blt_nat ?x (S ?x))] |- _ ] =>
      rewrite (blt_n_Sn x) in H; simplbnat

    (* blt_S_eq *)
    | [ |- context [(blt_nat (S ?x) (S ?y))]] =>
      rewrite <- (blt_S_eq x y); simplbnat
    | [H : context [(blt_nat (S ?x) (S ?y))] |- _ ] =>
      rewrite <- (blt_S_eq x y) in H; simplbnat

    (* blt_n_Sm *)
    | [H : blt_nat ?x ?y = true
      |- context [(blt_nat ?x (S ?y))]] =>
      rewrite (blt_n_Sm x y H); simplbnat
    | [H : blt_nat ?x ?y = true,
       H0 : context [(blt_nat ?x (S ?y))] |- _ ] =>
      rewrite <- (blt_n_Sm x y H) in H0; simplbnat

    (* blt_n_mk *)
    | [H : blt_nat ?x ?y = true
      |- context [(blt_nat ?x (?y + ?k))]] =>
      rewrite (blt_n_mk x y k H); simplbnat
    | [H : blt_nat ?x ?y = true,
       H0 : context [(blt_nat ?x (?y + ?k))] |- _ ] =>
      rewrite <- (blt_n_mk x y k H) in H0; simplbnat

    (* blt_n_km *)
    | [H : blt_nat ?x ?y = true
      |- context [(blt_nat ?x (?k + ?y))]] =>
      rewrite (blt_n_km x y k H); simplbnat
    | [H : blt_nat ?x ?y = true,
       H0 : context [(blt_nat ?x (?k + ?y))] |- _ ] =>
      rewrite <- (blt_n_km x y k H) in H0; simplbnat

    (* beq_refl *)
    | [ |- context [(beq_nat ?x ?x)] ] =>
      rewrite (beq_refl x); simplbnat
    | [H : context [(beq_nat ?x ?x)] |- _ ] =>
      rewrite (beq_refl x) in H; simplbnat

    (* beq_sym *)
    | [ H : beq_nat ?x ?y = ?b
        |- context [(beq_nat ?y ?x)] ] =>
      rewrite (beq_sym x y b H); simplbnat
    | [H : beq_nat ?x ?y = ?b,
       H0 : context [(beq_nat ?y ?x)] |- _ ] =>
      rewrite (beq_sym x y b H) in H0; simplbnat

    | [ H : ?x <> ?y |- context [(beq_nat ?x ?y)] ] =>
      rewrite (neq_beq_false x y H); simplbnat
    | [ H : ?x <> ?y,
        H0 : context [(beq_nat ?x ?y)] |- _ ] =>
      rewrite (neq_beq_false x y H) in H0; simplbnat

    | [ H : ?y <> ?x |- context [(beq_nat ?x ?y)] ] =>
      rewrite (neq_beq_false x y (sym_not_eq H)); simplbnat
    | [ H : ?y <> ?x,
        H0 : context [(beq_nat ?x ?y)] |- _ ] =>
      rewrite (neq_beq_false x y (sym_not_eq H)) in H0; simplbnat

    | [H : ?x = ?x |- _ ] => clear H; simplbnat
    | [H : true = false |- _ ] => discriminate H
    | [H : false = true |- _ ] => discriminate H
    | _ => idtac
  end.

Tactic Notation "bnat simpl" := simplbnat.

Ltac desbnatH H :=
  match goal with
    | H : blt_nat ?a ?b = true |- _ =>
        generalize (blt_true_lt a b H); clear H; intro H

    | H : blt_nat ?a ?b = false |- _ =>
        generalize (blt_false_le a b H); clear H; intro H

    | H : beq_nat ?a ?b = true |- _ =>
        generalize (beq_true_eq a b H); clear H; intro H

    | H : beq_nat ?a ?b = false |- _ =>
        generalize (beq_false_neq a b H); clear H; intro H

    | _ => fail 1 "not bnat found"
  end.

Ltac desbnat :=
  match goal with
    | H : blt_nat ?a ?b = true |- _ =>
        generalize (blt_true_lt a b H); clear H; intro H; desbnat

    | H : blt_nat ?a ?b = false |- _ =>
        generalize (blt_false_le a b H); clear H; intro H; desbnat

    | H : beq_nat ?a ?b = true |- _ =>
        generalize (beq_true_eq a b H); clear H; intro H; desbnat

    | H : beq_nat ?a ?b = false |- _ =>
        generalize (beq_false_neq a b H); clear H; intro H; desbnat

    | _ => idtac
  end.

Ltac conbnat :=
  match goal with
    | |- blt_nat ?a ?b = true =>
        apply (lt_blt_true a b)

    | |- blt_nat ?a ?b = false =>
        apply (le_blt_false b a)

    | |- beq_nat ?a ?b = true =>
        apply (eq_beq_true a b)

    | |- beq_nat ?a ?b = false =>
        apply (neq_beq_false a b)

    | _ => fail 1 "the goal is not bnat"
  end.

Ltac solvebnat :=
  desbnat; conbnat; auto with arith.


(* *********************************************************** *)

Tactic Notation "rewbnat" constr (t) :=
  match t with
    | beq_nat ?x ?y = ?f =>
      let Hb := fresh "Hb" in
        (assert (Hb : t);
          [solvebnat | rewrite Hb; clear Hb])
    | blt_nat ?x ?y = ?f =>
      let Hb := fresh "Hb" in
        (assert (Hb : t);
          [solvebnat | rewrite Hb; clear Hb])
    | _ =>
      match type of t with
        | beq_nat ?x ?y = true => rewrite (beq_true_eq x y t)
        | _ => rewrite t
      end
  end.

Tactic Notation "rewbnat" constr (t) "in" hyp (H) :=
  match t with
    | beq_nat ?x ?y = ?f =>
      let Hb := fresh "Hb" in
        (assert (Hb : t);
          [solvebnat | rewrite Hb in H; clear Hb])
    | blt_nat ?x ?y = ?f =>
      let Hb := fresh "Hb" in
        (assert (Hb : t);
          [solvebnat | rewrite Hb in H; clear Hb])
    | _ =>
      match type of t with
        | beq_nat ?x ?y = true => rewrite (beq_true_eq x y t) in H
        | _ => rewrite t in H
      end
  end.

Tactic Notation "assertbnat" constr (t) :=
  let Hb := fresh "Hb" in (
    match t with
      | beq_nat ?x ?y = ?f =>
        (assert (Hb : t);
            [solvebnat | idtac])
      | blt_nat ?x ?y = ?f =>
        (assert (Hb : t);
            [solvebnat | idtac])
      | _ => fail 1 "t must be a blt_nat or beq_nat equation"
    end).

Ltac discribnat :=
  desbnat; subst;
  match goal with
    | H : ?x <> ?x |- _ => destruct (H (refl_equal x))
    | H : ?x = ?y |- _ => discriminate
    | H : ?x < ?x |- _ => destruct (lt_irrefl x H)
    | H : ?x < O |- _ => destruct (lt_n_O x H)
    | H : beq_nat ?x ?x = false |- _ =>
      desbnatH H; destruct (H (refl_equal x))
    | _ => elimtype False;
        auto with arith || fail 1 "no discriminatable hypothesis"
  end.

Ltac substbnat_all := desbnat; subst.

Ltac substbnat_one f := desbnat; subst f.

Tactic Notation "substbnat" := substbnat_all.

Tactic Notation "substbnat" constr (f) := substbnat_one f.

(*
Section test.

Variables (a b c d e f g : nat).
Hypotheses
  (H0 : beq_nat a b = true)
  (H1 : blt_nat c b = true)
  (H2 : blt_nat b a = true)
  (H3 : beq_nat a b = true)
  (H4 : beq_nat a b = true)
  (H5 : if beq_nat a b then True else False)
.

Goal if beq_nat a b then True else False.
simplbnat.
rewrite_bnat_all H0.
substbnat.
rewbnat H0 in H3.
invbnat.
bnat2nat.
omega.
simplbnat.

End test. *)

(* *********************************************************** *)

Ltac decbeqnat x y :=
  let Hb := fresh "Hb" in
    (destruct (beq_nat_dec x y) as [Hb | Hb]; simplbnat).

Ltac decbltnat x y :=
  let Hb := fresh "Hb" in
    (destruct (blt_nat_dec x y) as [Hb | Hb]; simplbnat).

Lemma neq_decidable: forall (m n : nat), Decidable.decidable (m <> n).
Proof.
  intros m n.
  case (Nat.eq_dec m n); intros H.
  - right; auto.
  - left; auto.
Qed.