(*
  This file is part of the verified smart contract project of SECBIT Labs.

  Copyright 2015 Yu Guo
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

Require Import LibEx.
(* Require Import IntBool. *)
Require Import List.
Require Import Coq.Logic.Classical_Prop.
Require Export Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.

Section TMapLib.

  Variable A : Set.

  Variable beq : A -> A -> bool.

  Hypothesis beq_true_eq : forall a a' : A,
    beq a a' = true -> a = a'.

  Hypothesis beq_false_neq : forall a a' : A,
    beq a a' = false -> a <> a'.

  Hypothesis eq_beq_true : forall a a' : A,
    a = a' -> beq a a' = true.

  Hypothesis neq_beq_false : forall a a' : A,
    a <> a' -> beq a a' = false.

  Variable B : Type.

  Variable zero : B.

Lemma beq_dec : forall a a' : A, {beq a a' = true} + {beq a a' = false}.
Proof.
  intros; destruct (beq a a'); [left | right]; trivial.
Qed.

Lemma eq_dec : forall a a' : A, {a = a'} + {a <> a'}.
Proof.
  intros; destruct (beq_dec a a'); [left | right].
  apply beq_true_eq; trivial.
  apply beq_false_neq; trivial.
Qed.

Ltac beq_case_tac x y :=
  let Hb := fresh "Hb" in
    (destruct (beq_dec x y) as [Hb | Hb]; trivial).

Lemma beq_sym : forall a a' b,
  beq a a' = b -> beq a' a = b.
Proof.
  intros m n b H.
  destruct b.
    apply eq_beq_true.
    apply sym_eq.
    apply beq_true_eq; trivial.
  apply neq_beq_false.
  apply sym_not_eq.
  apply beq_false_neq; trivial.
Qed.

Lemma beq_refl : forall a, beq a a = true.
Proof.
  intro m.
  apply eq_beq_true; trivial.
Qed.

Lemma beq_trans : forall a a' a'' b, beq a a' = true
  -> beq a' a'' = b
  -> beq a a'' = b.
Proof.
  intros m n k b H1 H2.
  assert (m = n).
    apply beq_true_eq; trivial.
  subst m.
  destruct b.
    apply eq_beq_true.
    apply beq_true_eq; trivial.
  apply neq_beq_false.
  apply beq_false_neq; trivial.
Qed.

Ltac beq_simpl_tac :=
  match goal with

    (* beq rewrite directly *)
    | [H : beq ?x ?y = ?f
      |- context [(beq ?x ?y)]] =>
       rewrite H; beq_simpl_tac
    | [H : beq ?x ?y = ?f,
       H0 : context [(beq ?x ?y)] |- _ ] =>
       rewrite H in H0; beq_simpl_tac

    (* beq_refl *)
    | [ |- context [(beq ?x ?x)] ] =>
      rewrite (@beq_refl x); beq_simpl_tac
    | [H : context [(beq ?x ?x)] |- _ ] =>
      rewrite (@beq_refl x) in H; beq_simpl_tac

    (* beq_sym *)
    | [ H : beq ?x ?y = ?b
        |- context [(beq ?y ?x)] ] =>
      rewrite (@beq_sym x y b H); beq_simpl_tac
    | [H : beq ?x ?y = ?b,
       H0 : context [(beq ?y ?x)] |- _ ] =>
      rewrite (@beq_sym x y b H) in H0; beq_simpl_tac

    (* neq -> beq *)
    | [ H : ?x <> ?y |- context [(beq ?x ?y)] ] =>
      rewrite (neq_beq_false H); beq_simpl_tac
    | [ H : ?x <> ?y,
        H0 : context [(beq ?x ?y)] |- _ ] =>
      rewrite (neq_beq_false H) in H0; beq_simpl_tac
    | [ H : ?x <> ?y |- context [(beq ?y ?x)] ] =>
      rewrite (beq_sym (neq_beq_false H)); beq_simpl_tac
    | [ H : ?x <> ?y,
        H0 : context [(beq ?y ?x)] |- _ ] =>
      rewrite (beq_sym (neq_beq_false H)) in H0; beq_simpl_tac

    (* beq -> neq *)
    | [ H : (beq ?x ?y = false) |- ?x <> ?y ] =>
      apply (beq_false_neq H); beq_simpl_tac
    | [ H : (beq ?x ?y = false) |- ?y <> ?x ] =>
      apply (beq_false_neq (beq_sym H)); beq_simpl_tac

    | [H : ?x = ?x |- _ ] => clear H; beq_simpl_tac
    | [H : true = false |- _ ] => discriminate H
    | [H : false = true |- _ ] => discriminate H

    | [|- true = true ] => trivial
    | [|- false = false ] => trivial

    | [|- context [beq ?x ?y] ] => simpl; trivial
    | [ H: context [beq ?x ?y] |- _ ] => simpl in H

    | _ => idtac
  end.

(* Section Test. *)
(*   Variables a b : A. *)
(*   Goal beq a b = false -> b <> a. *)
(*     intro H. *)
(*     beq_simpl_tac. *)
(*   Abort. *)
(* End Test. *)

Tactic Notation "beq" "simpl" := beq_simpl_tac.

Ltac beq_rewrite_tac H :=
  match type of H with
    | beq ?a ?b = true =>
      match goal with
        | [ |- context [(?a)]] =>
          rewrite (@beq_true_eq a b H)
        | [ |- context [(?b)]] =>
          rewrite <- (@beq_true_eq a b H)
      end
    | _ => fail
  end.

Tactic Notation "beq" "rewrite" constr(t) := beq_rewrite_tac t.

Ltac beq_rewriteH_tac H H' :=
  match type of H with
    | beq ?a ?b = true =>
      match type of H' with
        | context [(?a)] =>
          rewrite (@beq_true_eq a b H) in H'
        | context [(?b)] =>
          rewrite <- (@beq_true_eq a b H) in H'
      end
    | _ => fail
  end.

Tactic Notation "beq" "rewrite" constr(t) "in" hyp(H) := beq_rewriteH_tac t H.

Section Test.
  Variables a b a' : A.
  Goal beq a b = true -> beq a a' = true -> False.
    intros.
    beq_rewriteH_tac H0 H.
  Abort.
End Test.

(*****************************************************************************)
(** Definition of map                                                        *)
(*****************************************************************************)

(***********************)
(** map                *)
(***********************)

Definition tmap := A -> B.

Definition get (m : tmap) (a : A) := m a.

Lemma get_dec :
  forall (m : tmap) (a : A),
    {exists b, get m a = b} + {get m a = zero}.
Proof.
  intros m a.
  unfold get.
  left.
  exists (m a). trivial.
Qed.

Definition emp : tmap := fun _ => zero.

Lemma emp_sem :
  forall a : A, get emp a = zero.
Proof.
  intros; unfold get, emp; trivial.
Qed.

Definition sig (a : A) (b : B) :=
  fun a' => if beq a a' then b else zero.

Lemma sig_sem : forall (a a' : A) (b : B),
  get (sig a b) a' =
  match (beq a a') with
    | true => b
    | false => zero
  end.
Proof.
  unfold get, sig. intros a a' b.
  destruct (eq_dec a a').
  rewrite e; trivial.
  rewrite (@neq_beq_false a a'); auto.
Qed.

Definition upd (m : tmap) (a : A) (b : B) : tmap :=
  fun a' => if (beq a a') then b else get m a'.

Lemma upd_sem : forall m a a' b,
  get (upd m a b) a' =
  match (beq a a') with
    | true => b
    | false => get m a'
  end.
  intros.
  unfold get.
  unfold upd.
  unfold get.
  trivial.
Qed.

(***********************)
(** extensionality     *)
(***********************)

Lemma extensionality: forall (m1 m2 : tmap),
  (forall a, get m1 a = get m2 a) -> m1 = m2.
Proof.
  unfold get.
  apply functional_extensionality.
Qed.

(***********************)
(** lookup             *)
(***********************)

Definition lookup (m : tmap) (a : A) (b : B) :=
  get m a = b.

(************************)
(** merge               *)
(************************)

(***********************************************************)
(**                                                        *)
(**    Lemmas                                              *)
(**                                                        *)
(**    Tactics                                             *)
(**                                                        *)
(***********************************************************)

Lemma emp_zero : forall a,
    emp a = zero.
Proof.
  intros.
  unfold emp.
  trivial.
Qed.

Lemma get_upd_eq : forall (m : tmap) a v,
    (upd m a v) a = v.
Proof.
  intros.
  unfold upd.
  assert (beq a a= true).
  apply eq_beq_true. trivial.
  rewrite H. trivial.
Qed.

Lemma get_upd_eq2 : forall (m : tmap) a1 a2 v,
    a1 = a2
    -> (upd m a1 v) a2 = v.
Proof.
  intros.
  rewrite H.
  apply get_upd_eq.
Qed.

Lemma get_upd_ne : forall (m : tmap) a a' v,
    a' <> a
    ->  (upd m a v) a' = m a'.
Proof.
  intros.
  unfold upd.
  assert (beq a a' = false). apply neq_beq_false. auto.
  rewrite H0. unfold get. trivial.
Qed.

Hint Extern 1 => match goal with
                 | [ H : emp _ = _ |- _ ] =>
                   rewrite emp_zero in H; discriminate
                 end.

Hint Rewrite get_upd_eq get_upd_ne using congruence.

(***********************)
(** get set            *)
(***********************)

Ltac destruct_get :=
  match goal with

    | H: context [ get ?m ?a ] |- _ =>
        destruct (get m a);
          destruct_get

    | |- context [ get ?m ?a ] =>
        destruct (get m a);
          destruct_get

    | _ => idtac

end.

End TMapLib.

Notation "$0" := (emp 0).

Unset Implicit Arguments.
