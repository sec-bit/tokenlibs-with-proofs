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

Require Import Arith.
Require Import Lists.List.
Require Import Nat.
Require Import Omega.

Require Import Maps.
Require Import Model.
Require Import Spec.

Definition assert_genesis_event (e: Event) (E: EventList) : Prop :=
  match E with
    | nil => False
    | cons e' E => e = e'
  end.

Lemma assert_genesis_event_app :
  forall e E E',
    assert_genesis_event e E
    -> assert_genesis_event e (E ++ E').
Proof.
  intros.
  destruct E.
  + simpl in H.  inversion H.
  + simpl in H. auto.
Qed.

Definition PropINV (env: Env) (S: State) (E: EventList) : Prop :=
  (exists creator,
      assert_genesis_event (ev_constructor creator) E) /\
  (forall owner,
      owner <> 0 ->
      length (V2A.map_filter (st_tokenOwner S) (fun e => Nat.eqb (snd e) owner)) =
      (st_ownedTokensCount S $ owner)%a2v).

Lemma create_INV :
  forall env0 env msg C E,
    create env0 msg C E
    -> env_step env0 env
    -> PropINV env (w_st C) E.
Proof.
  intros env0 env msg C evts Hcreate Henv_step.
  destruct Hcreate; subst; simpl in *; subst.
  split.

  - exists sender.
    constructor; auto.

  - destruct H3 as [HtokenOwner [HtokenApprovals [HownedTokensCount HoperatorApprovals]]].
    intros.
    rewrite HownedTokensCount; A2V.msimpl.
    rewrite (V2A.filter_length_equal _ HtokenOwner).
    auto.
Qed.

Lemma step_INV:
  forall this env msg S E env' S' E',
    step env (mk_contract this S) msg (mk_contract this S') E'
    -> env_step env env'
    -> PropINV env S E
    -> PropINV env' S' (E ++ E').
Proof.
  intros this env msg st evts env' st' evts' Hstep _ HPinv.

  unfold PropINV in *.
  destruct HPinv as [[creator Hcreator] HPinv].
  split.

  - exists creator. apply assert_genesis_event_app; auto.

  - clear creator Hcreator.
    intros owner Howner_nonzero.

    inversion Hstep;
      unfold func_step in H1;
      destruct H1 as [Haddr [Hinv [Hinv' [Hreq [Hevts Htrans]]]]];
      unfold INV in Hinv, Hinv';
      subst;
      simpl in *;
      subst;
      (* Htrans in some cases are simply 'C' = C' *)
      try destruct Htrans as [HtokenOwner [HtokenApprovals [HownedTokensCount HoperatorApprovals]]];
      auto.
Qed.

Lemma step_contract_address_preserve:
  forall env C msg C' E',
    step env C msg C' E'
    -> w_a C = w_a C'.
Proof.
  intros.
  destruct C as [a S].
  destruct C' as [a' S'].
  induction H; unfold func_step in H1; intuition.
Qed.

Lemma steps_INV:
  forall ml env env' C C' E E',
    PropINV env (w_st C) E ->
    steps env C ml env' C' E' ->
    PropINV env' (w_st C') (E ++ E').
Proof.
  induction ml; simpl.

  - intros env env' C C' E E' HPinv [Hcontract [Hevts' Henv]].
    subst. rewrite app_nil_r; auto.

  - intros env env' C C' E E' HPinv Hsteps.
    destruct Hsteps as [env'' [C'' [E'' [E''' [Hstep [Hsteps [HE' Henv_step]]]]]]].
    destruct C. destruct C''.
    simpl in *.

    generalize (step_contract_address_preserve _ _ _ _ _ Hstep);
      simpl; intros HC_eq.

    rewrite HC_eq in Hstep.
    generalize (step_INV _ _ _ _ _ _ _ _ Hstep Henv_step HPinv);
      intros HPinv''.
    substH IHml with
        (IHml env'' env' {| w_a := w_a0; w_st := w_st0 |} C' (E ++ E'') E'''
              HPinv'' Hsteps).
    simpl in IHml.
    subst E'.
    rewrite (app_assoc _ _ _).
    auto.
Qed.

(* Prop #1: owned token count consistency *)
Theorem Property_owned_token_count_consistency:
  forall env0 msg0 env ml C E C' E',
    create env0 msg0 C E
    -> env_step env0 env
    -> run env C ml C' E'
    -> forall owner,
        owner <> 0 ->
        length (V2A.map_filter (st_tokenOwner (w_st C')) (fun e => Nat.eqb (snd e) owner)) =
        (st_ownedTokensCount (w_st C') $ owner)%a2v.
Proof.
  intros env0 msg0 env ml C evts C' evts'
         Hcreate Henv_step Hrun owner Howner_nonzero.
  inversion Hrun; subst.
  generalize (create_INV env0 env msg0 C evts Hcreate Henv_step);
    intros HPinv.
  generalize (steps_INV _ _ _ _ _ _ _ HPinv H);
    intros HPinv'.

  unfold PropINV in HPinv'.
  destruct HPinv' as [_ HPinv'].
  apply HPinv'; auto.
Qed.

(* Prop #2: every newly minted token is unique *)
Theorem Property_unique_minted_token:
  forall msg to token,
    m_func msg = mc_mint to token ->
    forall env C C' evts,
      step env C msg C' evts ->
      st_tokenOwner (w_st C) $ token = 0.
Proof.
  intros msg to token Hfunc env C C' evts Hstep.

  inversion Hstep; subst;
    try inversion Hfunc;
    subst.

  unfold func_step in H1.
  destruct H1 as [Hst [_ [_ [Hreq _]]]].
  unfold funcspec_mint in Hreq; simpl in Hreq.
  intuition.
Qed.
