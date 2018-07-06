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

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Axiom FFF : False.
Ltac skip := destruct FFF.

Ltac inv H := inversion H; clear H; subst.

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Tactic Notation "substH" hyp (H) :=
  match goal with
    | |- ?a -> ?b => clear H; intro H
    | |- _ => fail 1 "goal must be 'A -> B'."
  end.

Tactic Notation "substH" hyp (H) "with" constr (t) :=
  generalize t; clear H; intro H.

Tactic Notation "substH" hyp (H) "with" constr (t) "into" ident (Hn) :=
  generalize t; clear H; intro Hn.

Lemma eq_sym : forall {A: Type} (n m : A), n = m -> m = n.
Proof.
  intros.
  subst; trivial.
Qed.
Arguments eq_sym [A n m].

Lemma neq_sym : forall {A: Type} (n m : A), n <> m -> m <> n.
Proof.
  intros.
  intro HF; subst; auto.
Qed.
Arguments neq_sym {A} {n} {m} _ _.


Tactic Notation "gen_clear" hyp (H) :=
  generalize H; clear H.

Tactic Notation "gen_clear" hyp (H1) hyp (H2) :=
  generalize H1 H2; clear H1 H2.

Tactic Notation "gen_clear"
  hyp (H1) hyp (H2) hyp (H3) :=
  generalize H1 H2 H3; clear H1 H2 H3.

Tactic Notation "gen_clear"
  hyp (H1) hyp (H2) hyp (H3) hyp (H4) :=
  generalize H1 H2 H3 H4;
    clear H1 H2 H3 H4.

Tactic Notation "gen_clear"
  hyp (H1) hyp (H2) hyp (H3)
  hyp (H4) hyp (H5):=
  generalize H1 H2 H3 H4 H5;
    clear H1 H2 H3 H4 H5.

Tactic Notation "gen_clear"
  hyp (H1) hyp (H2) hyp (H3)
  hyp (H4) hyp (H5) hyp (H6):=
  generalize H1 H2 H3 H4 H5 H6;
    clear H1 H2 H3 H4 H5 H6.

Tactic Notation "split_l" :=
  split; [trivial | idtac].

Tactic Notation "split_r" :=
  split; [idtac | trivial ].

Tactic Notation "split_lr" :=
  split; [trivial | trivial ].

Tactic Notation "split_l" "with" constr (t) :=
  split; [apply t | idtac].

Tactic Notation "split_r" "with" constr (t) :=
  split; [idtac | apply t ].

Tactic Notation "split_l" "by" tactic (tac) :=
  split; [tac | idtac ].

Tactic Notation "split_r" "by" tactic (tac) :=
  split; [idtac | tac ].

Tactic Notation "split_l_clear" "with" hyp (H) :=
  split; [apply H | clear H].

Tactic Notation "split_r_clear" "with" hyp (H) :=
  split; [clear H | apply H ].

Tactic Notation "inj_hyp" hyp (H) :=
  injection H; clear H; intro H.

Tactic Notation "rew_clear" hyp (H) :=
  rewrite H; clear H.

Tactic Notation "injection" hyp (H) :=
  injection H.

Tactic Notation "injection" hyp (H) "as"
  simple_intropattern (pat) :=
  injection H; intros pat.
