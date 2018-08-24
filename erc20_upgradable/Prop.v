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

Require Export Arith.
Require Export Lists.List.

Require Import Maps.
Require Import Model.
Require Import Spec.

(* The correctness of update contract relies on the assumption that
   the storage state of the old contract does not change. *)
Definition env_req
           (env: Model.env) (C: contract) (env': Model.env) (C': contract): Prop :=
  env_contract env (st_oldToken (w_st C)) = env_contract env' (st_oldToken (w_st C')).

Definition assert_genesis_event (e: event) (E: eventlist) : Prop :=
  match E with
    | nil => False
    | cons e' E => e = e'
  end.

Lemma assert_genesis_event_app : forall e E E',
        assert_genesis_event e E
        -> assert_genesis_event e (E ++ E').
Proof.
  intros.
  destruct E.
  + simpl in H.  inversion H.
  + simpl in H. auto.
Qed.

Definition PropINV (env: env) (S: state) (E: eventlist) : Prop :=
  (* contract must have been constructed *)
  (exists creator,
      assert_genesis_event (ev_constructor creator (st_oldToken S)) E)
  /\ (forall OS,
         env_contract env (st_oldToken S) = Some OS ->
         A2V.sum (ost_balances OS) = ost_totalSupply OS /\
         A2V.sum (st_balances S) +
         A2V.sum_filter (ost_balances OS)
                        (fun e => negb (st_migratedBalances S $ (fst e))%a2b) =
         st_totalSupply S).

(* step evaluation maintains invariant *)
Lemma step_INV:
  forall this env msg S E env' S' E',
    step env (mk_contract this S) msg (mk_contract this S') E'
    -> env_step env env'
    -> env_req env (mk_contract this S) env' (mk_contract this S')
    -> PropINV env S E
    -> PropINV env' S' (E ++ E').
Proof.
  intros this env msg st evts env' st' evts'
         Hstep Henv_step Henv HPinv.

  unfold env_req in Henv; simpl in Henv.

  unfold env_step in Henv_step.
  destruct Henv_step as [Henv_time Henv_bhash].

  unfold PropINV in *.
  destruct HPinv as [[creator Hcreator] HPinv].

  inversion_clear Hstep;
    subst;
    unfold func_step in H1;
    destruct H1 as [_ [Hinv [Hinv' [Hreq [Hevts Htrans]]]]];
    unfold spec_require in Hreq;
    unfold spec_events in Hevts;
    unfold spec_trans in Htrans;
    simpl in *;
    destruct Htrans as
        [_ [_ [_ [Htotal [Hblncs [_ [_ [Hmig Hold]]]]]]]];
    (split;
     [ exists creator; try (rewrite Hold); apply assert_genesis_event_app; auto
     | intros ost' Hcontract'; clear Hevts;
       unfold INV in Hinv;
       destruct Hinv as [[Htotal_lo Htotal_hi] [Hallwd [ost [Hcontract [_ Hinv]]]]];
       rewrite Hcontract, Hcontract' in Henv; inversion Henv; subst ost';
       clear Henv Hcontract';
       unfold INV_sum_blncs in Hinv;
       substH HPinv with (HPinv ost Hcontract);
       destruct HPinv as [Host_total HPinv]
    ]).

  - (* transfer, msg.sender not migrated *)
    destruct Hreq as [Hmig_sender [ost' [Hcontract' Hblncs_sender]]].
    rewrite Hcontract in Hcontract';
      inversion Hcontract'; subst ost'; clear Hcontract'.
    destruct Hblncs as [ost' [Hcontract' Hblncs']].
    rewrite Hcontract in Hcontract';
      inversion Hcontract'; subst ost'; clear Hcontract'.

    rewrite Hblncs', Hmig.

    (* sum_filter(ost_balances[], f) = sum_filter(ost_balances[], g) + ost_balances[sender] *)
    pose (f := fun e : nat * value => negb (A2B.get (st_migratedBalances st) (fst e))).
    pose (g := fun e : nat * value => negb (A2B.get (A2B.upd (st_migratedBalances st) sender true) (fst e))).
    assert (Hf_true: forall v, f (sender, v) = true).
    {
      unfold f; simpl.
      rewrite Hmig_sender. auto.
    }
    assert (Hg_false: forall v, g (sender, v) = false).
    {
      unfold g; simpl.
      A2B.msimpl; rewrite Hmig_sender.
    }
    assert (Hfg: forall k v, sender <> k -> f (k, v) = g (k, v)).
    {
      intros k _v Hneq.
      unfold f, g; simpl.
      rewrite A2B.get_upd_neq; auto.
    }
    generalize (A2V.sum_filter_one_bit sender f g Hf_true Hg_false Hfg (ost_balances ost));
      unfold f, g; intros Hsum_filter.
    (* balances[sender] <= sum(balances[]) *)
    generalize (A2V.sum_upper (st_balances st) sender);
      intros.
    (* old_balances[sender] <= sum_filter(old_balances[], f) *)
    generalize (A2V.sum_filter_true_upper f sender (ost_balances ost) (Hf_true _));
      unfold f; intros.

    erewrite A2V.sum_upd_inc; eauto.
    + erewrite A2V.sum_upd_dec; eauto.
      * erewrite A2V.sum_upd_inc; eauto; omega.
      * A2V.msimpl.
          rewrite (plus_safe_lt _ _); omega.
    + destruct (Nat.eq_dec to sender); A2V.msimpl.
      * rewrite (plus_safe_lt _ _); [> | omega].
        rewrite (minus_safe _ _); omega.
      * generalize (A2V.sum_sum_filter_true_le
                      f sender Hf_true
                      (st_balances st) (ost_balances ost) to n);
          unfold f; intros.
        omega.

  - (* transfer, msg.sender migrated *)
    destruct Hreq as [Hmig_sender Hblncs_sender].

    rewrite Hblncs, Hmig.

    (* balances[sender] <= sum(balances[]) *)
    generalize (A2V.sum_upper (st_balances st) sender); intros.

    erewrite A2V.sum_upd_inc; eauto.
    + erewrite A2V.sum_upd_dec; eauto.
      omega.
    + destruct (Nat.eq_dec to sender); A2V.msimpl.
      * rewrite (minus_safe _ _); omega.
      * generalize (A2V.sum_descend to sender n (st_balances st)); intros.
        omega.

  - (* balanceOf, not migrated *)
    destruct Hblncs as [ost' [Hcontract' Hblncs']].
    rewrite Hcontract in Hcontract';
      inversion Hcontract'; subst ost'; clear Hcontract'.

    rewrite Hblncs', Hmig.

    (* sum_filter(ost_balances[], f) = sum_filter(ost_balances[], g) + ost_balances[owner] *)
    pose (f := fun e : nat * value => negb (A2B.get (st_migratedBalances st) (fst e))).
    pose (g := fun e : nat * value => negb (A2B.get (A2B.upd (st_migratedBalances st) owner true) (fst e))).
    assert (Hf_true: forall v, f (owner, v) = true).
    {
      unfold f; simpl.
      rewrite Hreq. auto.
    }
    assert (Hg_false: forall v, g (owner, v) = false).
    {
      unfold g; simpl.
      A2B.msimpl; rewrite Hreq.
    }
    assert (Hfg: forall k v, owner <> k -> f (k, v) = g (k, v)).
    {
      intros k _v Hneq.
      unfold f, g; simpl.
      rewrite A2B.get_upd_neq; auto.
    }
    generalize (A2V.sum_filter_one_bit owner f g Hf_true Hg_false Hfg (ost_balances ost));
      unfold f, g; intros Hsum_filter.
    (* balances[owner] <= sum(balances[]) *)
    generalize (A2V.sum_upper (st_balances st) owner);
      intros.
    (* old_balances[owner] <= sum_filter(old_balances[], f) *)
    generalize (A2V.sum_filter_true_upper f owner (ost_balances ost) (Hf_true _));
      unfold f; intros.

    erewrite A2V.sum_upd_inc; eauto; omega.

  - (* balanceOf, migrated *)
    split; auto.

  - (* transferFrom, limited, not migrated *)
    destruct Hreq as [Hmig_from [Hallwd_from_sender [ost' [Hcontract' Hsum_blncs]]]].
    rewrite Hcontract in Hcontract';
      inversion Hcontract'; subst ost'; clear Hcontract'.

    destruct Hblncs as [ost' [Hcontract' Hblncs']].
    rewrite Hcontract in Hcontract';
      inversion Hcontract'; subst ost'; clear Hcontract'.

    (* sum_filter(ost_balances[], f) = sum_filter(ost_balances[], g) + ost_balances[from] *)
    pose (f := fun e : nat * value => negb (A2B.get (st_migratedBalances st) (fst e))).
    pose (g := fun e : nat * value => negb (A2B.get (A2B.upd (st_migratedBalances st) from true) (fst e))).
    assert (Hf_true: forall v, f (from, v) = true).
    {
      unfold f; simpl.
      rewrite Hmig_from. auto.
    }
    assert (Hg_false: forall v, g (from, v) = false).
    {
      unfold g; simpl.
      A2B.msimpl; rewrite Hmig_from.
    }
    assert (Hfg: forall k v, from <> k -> f (k, v) = g (k, v)).
    {
      intros k _v Hneq.
      unfold f, g; simpl.
      rewrite A2B.get_upd_neq; auto.
    }
    generalize (A2V.sum_filter_one_bit from f g Hf_true Hg_false Hfg (ost_balances ost));
      unfold f, g; intros Hsum_filter.
    (* balances[from] <= sum(balances[]) *)
    generalize (A2V.sum_upper (st_balances st) from);
      intros.
    (* old_balances[from] <= sum_filter(old_balances[], f) *)
    generalize (A2V.sum_filter_true_upper f from (ost_balances ost) (Hf_true _));
      unfold f; intros.

    pose (g' := fun e : nat * value => negb (A2B.get (st_migratedBalances st') (fst e))).
    assert (Hgg': forall k, g k = g' k).
    {
      intros.
      unfold g, g'; simpl.
      rewrite Hmig; auto.
    }
    generalize (A2V.sum_filter_f_eq Hgg' (ost_balances ost));
      unfold g, g';
      intros Hsum_filter_eq;
      rewrite <- Hsum_filter_eq;
      clear Hsum_filter_eq.

    rewrite (A2V.sum_equal Hblncs').

    erewrite A2V.sum_upd_inc; eauto.
    + erewrite A2V.sum_upd_dec; eauto.
      * erewrite A2V.sum_upd_inc; eauto; omega.
      * A2V.msimpl.
        rewrite (plus_safe_lt _ _); omega.
    + destruct (Nat.eq_dec to from); A2V.msimpl.
      * rewrite (plus_safe_lt _ _); [> | omega].
        rewrite (minus_safe _ _); omega.
      * generalize (A2V.sum_sum_filter_true_le
                      f from Hf_true (st_balances st) (ost_balances ost) to n);
          unfold f; intros.
        omega.

  - (* transferFrom, limited, migrated *)
    destruct Hreq as [Hmig_from [Hallwd_from_sender Hblncs_from]].

    pose (f := fun e: nat * value => negb (A2B.get (st_migratedBalances st) (fst e))).
    pose (g := fun e: nat * value => negb (A2B.get (st_migratedBalances st') (fst e))).
    assert (Hfg: forall k, f k = g k).
    {
      intros; unfold f, g.
      rewrite Hmig; auto.
    }
    generalize (A2V.sum_filter_f_eq Hfg (ost_balances ost));
      unfold f, g;
      intros Hsum_filter_eq; rewrite <- Hsum_filter_eq; clear Hsum_filter_eq.

    rewrite (A2V.sum_equal Hblncs).
    destruct (Nat.eq_dec to from).
    + subst to.
      generalize (A2V.sum_upper (st_balances st) from); intros.
      erewrite A2V.sum_upd_inc; eauto.
      * erewrite A2V.sum_upd_dec; eauto.
        omega.
      * A2V.msimpl.
        rewrite (minus_safe _ _); omega.
    + rewrite A2V.sum_transfer; try omega.
      generalize (A2V.sum_descend to from n (st_balances st)); intros.
      omega.

  - (* transferFrom, unlimited, not migrated *)
    destruct Hreq as [Hmig_from [Hallwd_from_sender [ost' [Hcontract' Hsum_blncs]]]].
    rewrite Hcontract in Hcontract';
      inversion Hcontract'; subst ost'; clear Hcontract'.

    destruct Hblncs as [ost' [Hcontract' Hblncs']].
    rewrite Hcontract in Hcontract';
      inversion Hcontract'; subst ost'; clear Hcontract'.

    (* sum(old_blncs, f) = sum(old_blncs, g) + old_blncs[from] *)
    pose (f := fun e : nat * value => negb (A2B.get (st_migratedBalances st) (fst e))).
    pose (g := fun e : nat * value => negb (A2B.get (st_migratedBalances st') (fst e))).
    assert (Hf_true: forall v, f (from, v) = true).
    {
      unfold f; simpl.
      rewrite Hmig_from; auto.
    }
    assert (Hg_false: forall v, g (from, v) = false).
    {
      intros.
      unfold g; simpl.
      rewrite Hmig. A2B.msimpl.
    }
    assert (Hfg: forall k v, from <> k -> f (k, v) = g (k, v)).
    {
      intros k _v Hneq.
      unfold f, g. rewrite Hmig; simpl.
      rewrite A2B.get_upd_neq; auto.
    }
    generalize (A2V.sum_filter_one_bit
                  from f g Hf_true Hg_false Hfg (ost_balances ost));
      unfold f, g; intros Hsum_filter_eq.
    (* balances[from] <= sum(balances[]) *)
    generalize (A2V.sum_upper (st_balances st) from);
      intros.
    (* old_balances[from] <= sum_filter(old_balances[], f) *)
    generalize (A2V.sum_filter_true_upper f from (ost_balances ost) (Hf_true _));
      unfold f; intros.

    rewrite (A2V.sum_equal Hblncs').
    erewrite A2V.sum_upd_inc; eauto.
    + erewrite A2V.sum_upd_dec; eauto.
      * erewrite A2V.sum_upd_inc; eauto; omega.
      * A2V.msimpl.
        rewrite (plus_safe_lt _ _); omega.
    + destruct (Nat.eq_dec to from); A2V.msimpl.
      * subst to.
        rewrite (plus_safe_lt _ _); [> | omega].
        rewrite (minus_safe _ _); omega.
      * generalize (A2V.sum_sum_filter_true_le
                      f from Hf_true (st_balances st) (ost_balances ost) to n);
          unfold f; intros.
        omega.

  - (* transferFrom, unlimited, migrated *)
    destruct Hreq as [Hmig_from [Hallwd_from_sender Hblncs_from]].
    rewrite (A2V.sum_equal Hblncs).

    pose (f := fun e : nat * value => negb (A2B.get (st_migratedBalances st) (fst e))).
    pose (g := fun e : nat * value => negb (A2B.get (st_migratedBalances st') (fst e))).
    assert (Hfg: forall k, f k = g k).
    {
      intros.
      unfold f, g; simpl.
      rewrite Hmig; auto.
    }
    unfold f, g in Hfg.
    rewrite <- (A2V.sum_filter_f_eq Hfg).

    generalize (A2V.sum_upper (st_balances st) from); intros.

    erewrite A2V.sum_upd_inc; eauto.
    + erewrite A2V.sum_upd_dec; eauto.
      omega.
    + destruct (Nat.eq_dec to from); A2V.msimpl.
      * rewrite (minus_safe _ _); omega.
      * generalize (A2V.sum_descend to from n (st_balances st)); intros.
        omega.

  - (* approve *)
    rewrite Hblncs; rewrite Hmig; rewrite Htotal; auto.

  - (* allowance *)
    auto.

  - (* increaseApproval *)
    rewrite Hblncs; rewrite Hmig; rewrite Htotal; auto.

  - (* decreaseApproval *)
    rewrite Hblncs; rewrite Hmig; rewrite Htotal; auto.

  - (* decreaseApproval *)
    rewrite Hblncs; rewrite Hmig; rewrite Htotal; auto.

  - (* transferOwnership *)
    rewrite Hblncs; rewrite Hmig; rewrite Htotal; auto.
Qed.

(* create evaluation maintains invariant *)
Lemma create_INV : forall env0 env msg C E,
    create env0 msg C E ->
    env_step env0 env ->
    env_req env0 C env C ->
    PropINV env (w_st C) E.
Proof.
  intros env0 env msg C E Hcreate Henv_step Henv_req.

  destruct Hcreate; subst.
  unfold funcspec_constructor in *; simpl in *.
  destruct H3 as [Hold [[ost [Hcontract [Htotal' _]]] [Hblncs' [Hmig' [Hallwd' Howner']]]]].
  destruct H1 as [Hblncs [Hallwd [Hmig [ost0 [Hcontract0 [Host_stopped [Host_sum Host_total]]]]]]].
  rewrite Hcontract in Hcontract0; inversion Hcontract0; subst ost0; clear Hcontract0.

  unfold env_req in Henv_req.

  unfold PropINV.
  subst evts' oldAddr.
  simpl.

  split.

  - exists sender. reflexivity.

  - intros ost' Hcontract'.

    rewrite <- Henv_req in Hcontract'.
    rewrite Hcontract in Hcontract'; inversion Hcontract'; subst ost'; clear Hcontract'.
    rewrite (A2V.sum_equal Hblncs').

    pose (f := fun e : nat * value => negb (A2B.get (st_migratedBalances (w_st C')) (fst e))).
    pose (g := fun e : nat * value => negb (A2B.get A2B.empty (fst e))).
    assert (Hfg: forall k, f k = g k).
    {
      intros.
      unfold f, g; simpl.
      rewrite Hmig'; simpl; auto.
    }
    generalize (A2V.sum_filter_f_eq Hfg (ost_balances ost));
      unfold f,g; intros Hsum_filter_eq; rewrite Hsum_filter_eq.
    simpl.
    rewrite A2V.sum_filter_true.
    split; intuition.
Qed.

Lemma step_contract_address_preserve : forall env C msg C' E',
      step env C msg C' E'
      -> w_a C = w_a C'.
Proof.
  intros.
  destruct C as [a S].
  destruct C' as [a' S'].
  induction H; unfold func_step in H1; intuition.
Qed.

Lemma step_oldToken_preserve : forall msg env C C' E',
    step env C msg C' E'
    -> st_oldToken (w_st C') = st_oldToken (w_st C).
Proof.
  intros env C msg C' E' Hstep;
    inversion_clear Hstep;
    subst;
    destruct H1;
    destruct H0 as [_ [_ [_ [_ Htrans]]]];
    simpl in Htrans;
    destruct Htrans as [_ [_ [_ [_ [_ [_ [_ [_ Hold]]]]]]]];
    auto.
Qed.

Lemma steps_oldToken_preserve: forall ml env env' C C' E',
    steps env C ml env' C' E' env_req
    -> st_oldToken (w_st C') = st_oldToken (w_st C).
Proof.
  induction ml; simpl.

  - intros env env' C C' E' [Hcontract [Hevts Henv]].
    subst; reflexivity.

  - intros env env' C C' evts Hsteps.
    destruct Hsteps as [env'' [C'' [E'' [E' [Hstep [Hsteps [Hevts Henv_step]]]]]]].
    generalize (step_oldToken_preserve _ _ _ _ _ Hstep); intros Hold.
    substH IHml with (IHml env'' env' C'' C' E' Hsteps).
    omega.
Qed.

Lemma step_totalSupply_preserve: forall msg env C C' E',
    step env C msg C' E'
    -> st_totalSupply (w_st C') = st_totalSupply (w_st C).
Proof.
  intros env C msg C' E' Hstep;
    inversion_clear Hstep;
    subst;
    destruct H1;
    destruct H0 as [_ [_ [_ [_ Htrans]]]];
    simpl in Htrans;
    destruct Htrans as [_ [_ [_ [Htotal _]]]];
    auto.
Qed.

Lemma steps_totalSupply_preserve: forall ml env env' C C' E',
    steps env C ml env' C' E' env_req
    -> st_totalSupply (w_st C') = st_totalSupply (w_st C).
Proof.
  induction ml; simpl.

  - intros env env' C C' E' [Hcontract [Hevts Henv]].
    subst; reflexivity.

  - intros env env' C C' evts Hsteps.
    destruct Hsteps as [env'' [C'' [E'' [E' [Hstep [Hsteps [Hevts Henv_step]]]]]]].
    generalize (step_totalSupply_preserve _ _ _ _ _ Hstep); intros Hold.
    substH IHml with (IHml env'' env' C'' C' E' Hsteps).
    omega.
Qed.

Lemma steps_env_req: forall ml env env' C C' E',
    steps env C ml env' C' E' env_req
    -> env_req env C env' C'.
Proof.
  induction ml.

  - intros env env' C C' evts Hsteps.
    simpl in Hsteps.
    intuition.

  - intros env env' C C' evts Hsteps.
    simpl in Hsteps.
    destruct Hsteps as [env'' [C'' [E'' [E' [Hstep [Hsteps [Hevts [Henv_step Henv_step']]]]]]]].
    substH IHml with (IHml env'' env'  C'' C' E' Hsteps).
    unfold env_req in *.
    congruence.
Qed.

Lemma steps_INV:
  forall ml env env' C C' E E',
    PropINV env (w_st C) E ->
    steps env C ml env' C' E' env_req ->
    PropINV env' (w_st C') (E ++ E').
Proof.
  induction ml; simpl.

  - intros env env' C C' E E' HPinv [Hcontract [HE' [Henv Henv_req]]].
    subst. rewrite app_nil_r; auto.

  - intros env env' C C' E E' HPinv Hsteps.
    destruct Hsteps as [env'' [C'' [E'' [E''' [Hstep [Hsteps [HE' [Henv_step Henv_req]]]]]]]].
    unfold env_req in Henv_req.
    destruct C. destruct C''.
    simpl in *.

    generalize (step_contract_address_preserve _ _ _ _ _ Hstep);
      simpl; intros HC_eq.

    generalize (step_oldToken_preserve _ _ _ _ _ Hstep);
      simpl; intros Hold_eq.

    rewrite HC_eq in Hstep.
    generalize (step_INV _ _ _ _ _ _ _ _ Hstep Henv_step Henv_req HPinv);
      intros HPinv''.
    substH IHml with
        (IHml env'' env' {| w_a := w_a0; w_st := w_st0 |} C' (E ++ E'') E'''
              HPinv'' Hsteps).
    simpl in IHml.
    subst E'.
    rewrite (app_assoc _ _ _).
    auto.
Qed.

(* The total supply always equals the sum of balances in the current contract
   and balances of balances of non-migrated accounts in the old contract. *)
Lemma INV_implies_sum_equal_totalSupply :
  forall env S E,
    PropINV env S E ->
    forall OS,
      env_contract env (st_oldToken S) = Some OS ->
      A2V.sum (st_balances S) +
      A2V.sum_filter (ost_balances OS)
                     (fun e => negb (st_migratedBalances S $ (fst e))%a2b) =
      st_totalSupply S.
Proof.
  intros env S E HI ost Hcontract.
  unfold PropINV in HI.
  destruct HI as [_ Hinv].
  substH Hinv with (Hinv ost Hcontract).
  destruct Hinv.
  auto.
Qed.

(* Prop #1: total supply is equal to sum of balances *)
Theorem Property_totalSupply_equal_to_sum_balances :
  forall env0 env msg ml C E C' E',
    create env0 msg C E
    -> env_step env0 env
    -> env_req env0 C env C
    -> run env env_req C ml C' E'
    -> forall OS,
        env_contract env (st_oldToken (w_st C)) = Some OS ->
        A2V.sum (st_balances (w_st C')) +
        A2V.sum_filter (ost_balances OS)
                       (fun e => negb (st_migratedBalances (w_st C') $ (fst e))%a2b) =
        st_totalSupply (w_st C').
Proof.
  intros env0 env msg ml C E C' E' Hcreate Henv_step Henv_req Hrun ost Hcontract.

  unfold run in Hrun.
  destruct Hrun as [env' Hsteps].

  apply INV_implies_sum_equal_totalSupply
    with (env := env') (E := E ++ E') (S := w_st C');
    auto.

  - generalize (create_INV _ _ _ _ _ Hcreate Henv_step Henv_req);
      intros Hcreate_inv.
    eapply steps_INV; eauto.

  - generalize (steps_env_req _ _ _ _ _ _ Hsteps);
      intros Henv_req'; unfold env_req in Henv_req'.
    apply steps_oldToken_preserve in Hsteps.
    congruence.
Qed.

(* Prop #2: total supply does not change *)
Theorem Property_totalSupply_preserve:
    forall env0 env msg ml C E C' E',
    create env0 msg C E
    -> env_step env0 env
    -> env_req env0 C env C
    -> run env env_req C ml C' E'
    -> st_totalSupply (w_st C') = st_totalSupply (w_st C).
Proof.
  intros env0 env msg ml C E C' E' Hcreate Henv_step Henv_req Hrun.

  unfold run in Hrun.
  destruct Hrun as [env' Hsteps].
  eapply steps_totalSupply_preserve; eauto.
Qed.
