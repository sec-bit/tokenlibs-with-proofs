(*
  This file is part of the verified smart contract project of SECBIT Labs.

  Copyright 2018 SECBIT Labs

  Author: Even Lu

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

Require Export Lists.List.
(* Require Export TMapLib.*)
Require Import Model.
Require Import Spec.

Ltac arith_rewrite t := 
  let H := fresh "Harith" in
  match t with 
  | ?x = ?y => assert (H: t); [auto with arith; try omega | rewrite H; clear H]
  end.

(* Inductive TotalValue : (@tmap address value) -> value -> Prop := *)
(*  | sum_emp : TotalValue tmap_emp 0 *)
(*  | sum_add : forall m v a' v',  *)
(*      TotalValue m v *)
(*      -> m a' = 0 *)
(*      -> TotalValue (m $+ {a' <- v'}) (v + v') *)
(*  | sum_upd : forall m v a' v',  *)
(*      TotalValue m v *)
(*      -> m a' <> 0 *)
(*      -> TotalValue (m $+ {a' <- v'}) (v - (m a') + v'). *)

Inductive Sum : (@tmap address value) -> value -> Prop :=
 | Sum_emp : Sum tmap_emp 0
 | Sum_add : forall m v a' v', 
     Sum m v
     -> m a' = 0
     -> Sum (m $+ {a' <- v'}) (v + v')
 | Sum_del : forall m v a', 
     Sum m v
     -> Sum (m $+ {a' <- 0}) (v - (m a')).

Lemma address_dec : forall (a1 a2: address),
      {a1 = a2} + {a1 <> a2}.
Proof.
  intros.
  remember (beq a1 a2) as Ha.
  assert (beq a1 a2 = Ha). auto.
  destruct Ha.
  beq_elimH H. left. apply H.
  right.
  simplbeq.
  trivial.
Qed.

Lemma Sum_dec2 : forall m t a,
        Sum m t
        -> Sum  (m $+ {a <- -= m a}) (t - m a).
Proof.
  unfold a2v_upd_dec.
  intros.
  assert (Ht :minus_with_underflow (m a) (m a) = 0).
  unfold minus_with_underflow.
  rewrite blt_irrefl. 
    auto with arith.
    rewrite Ht.
  apply Sum_del; trivial.
Qed.

Fixpoint sum (m: @tmap address value) (al: list address) : value :=
  match al with
  | nil => 0
  | cons a al' => (m a) + sum m al'
  end.

Open Scope list_scope.


Section List.
  
  Context  `{A: Type}.

  Context `{BEq A}.

  Fixpoint list_in (a: A) (al: list A) : bool := 
    match al with
    | nil => false 
    | cons a' al' => if beq a a' then true 
                     else list_in a al'
  end.

Fixpoint no_repeat (al: list A) : bool := 
  match al with 
  | nil => true 
  | cons a' al' => andb (negb (list_in a' al')) (no_repeat al')
  end.

End List.
Opaque beq.

Lemma sum_emp : forall al,
    sum $0 al  = 0.
Proof.
  intros.
  induction al.
  simpl. trivial.
  simpl. apply IHal.
Qed.

Lemma sum_add_cons : forall (al : list address) m (a: address),
    list_in a al = false 
    -> no_repeat al = true
    -> m a + sum m al  = sum m (a :: al).
Proof.
  induction al. 
    intros m a Hin Hnr.
    simpl.
    trivial.
  intros m a' Hin' Hnr'.
  assert (Hnin : list_in a' al = false).
    simpl in Hin'.
    decbeq a' a.
    trivial.
  substH IHal with (IHal m a' Hnin). 
  simpl.
  simpl in IHal.
  omega.
Qed.

Lemma sum_del_none : forall al m a,
    list_in a al = false
    -> no_repeat al = true
    -> sum (m $+ {a <- 0}) al  = sum m al.
Proof.
  induction al. 
    intros m a Hin Hnr.
    simpl.
    trivial.
  intros m a' Hin' Hnr.
  simpl in Hin'.
  simpl.
  decbeq a a'; tmap_simpl.
  simpl in Hnr.
  desb Hnr as [Hnr1 Hnr2].
  rewrite (IHal m a' Hin' Hnr2).
  trivial.
Qed.

Lemma sum_del_any : forall al m a,
    list_in a al = true
    -> no_repeat al = true
    -> m a + sum (m $+ {a <- 0}) al  = sum m al.
Proof.
  induction al. 
    intros m a Hin Hnr.
    simpl in Hin.
    discriminate.
  intros m a' Hin' Hnr.
  simpl in Hin'.
  destruct (beq_dec a a').
    simplbeq.
    simpl.
    simpl in Hnr.
    desb Hnr as [Hnr1 Hnr2].
    simpltm.
    assert (a = a').
      beq_elimH H.
      trivial.
    subst a'.
    simplb.
    rewrite sum_del_none; trivial.
  simpl.
  simplbeq.
  tmap_simpl.
  simpl in Hnr.
  desb Hnr as [Hnr1 Hnr2].
  rewrite <- (IHal m a' Hin' Hnr2).
  omega.
Qed.

Lemma minus_minus: forall t a b,
      t - a - b = t - (a + b).
Proof.
  intros.
  omega.
Qed.

Lemma sum_add_not_in : forall al m a v,
    list_in a al = false
    -> no_repeat al = true
    -> sum (m $+ {a <- v}) al  = sum m al.
Proof.
  induction al.
    intros m a v Hin Hnr.
    simpl.
    trivial.
  intros m a' v' Hin' Hnr.
  simpl in Hin'.
  simpl in Hnr.
  desb Hnr as [Hnr1 Hnr2].
  simplb.
  decbeq a a'; tmap_simpl.
  simpl.
  simpltm.
Qed.

Lemma sum_add_in : forall al m a v,
    list_in a al = true
    -> no_repeat al = true
    -> m a = 0
    -> sum (m $+ {a <- v}) al  = sum m al + v.
Proof.
  induction al.
    intros m a v Hin Hnr Hma.
    simpl in Hin.
    discriminate.
  intros m a' v' Hin' Hnr Hma.
  simpl in Hin'.
  simpl in Hnr.
  desb Hnr as [Hnr1 Hnr2].
  decbeq a a'; simpl; simpltm.
    simplb.
    beq_elimH Hb.
    subst a'.
    rewrite sum_add_not_in; auto.
    rewrite Hma; simpl; trivial.
    auto with arith.
  simplb.
  rewrite (IHal m a' v' Hin' Hnr2 Hma).
  auto with arith.
Qed.

Lemma Sum_ge_strong : forall m t,
    Sum m t
    -> forall a al, 
      list_in a al = false
      -> no_repeat al = true
      -> t >= m a + sum m al.
Proof.
  intros m t H.
  induction H.
  - intros a al Hal Hnr.
    simpltm.
    rewrite sum_emp.
    auto with arith.
  - intros a al Hal Hnr.
    decbeq a a'.
      simpltm.
      substH IHSum with (IHSum a al Hal Hnr).
      beq_elimH Hb.
      subst a'.
      rewrite H0 in IHSum.
      rewrite (sum_add_not_in _ _ _ _ Hal Hnr).
      omega.
    simpltm.
    substH IHSum with (IHSum a al Hal Hnr).
    assert (Hx: list_in a' al = true \/ list_in a' al = false).
      destruct (list_in a' al); [left | right]; trivial.
    destruct Hx as [Hx | Hx].
      rewrite (sum_add_in _ _ _ _ Hx Hnr H0).
      omega.
    rewrite (sum_add_not_in _ _ _ _ Hx Hnr).
    omega.
  - intros a al' Hnin Hnr.
    decbeq a a'.
      tmap_simpl.
      beq_elimH Hb.
      subst a'.
      rewrite (sum_add_not_in _ _ _ _ Hnin Hnr).
      substH IHSum with (IHSum a al' Hnin Hnr).
      omega.
    assert (Hx: list_in a' al' = true \/ list_in a' al' = false).
      destruct (list_in a' al'); [left | right]; trivial.
    destruct Hx as [Hx | Hx].
      tmap_simpl.
      assert (Hy:=sum_del_any al' m a' Hx Hnr).
      substH IHSum with (IHSum a al' Hnin Hnr).
      rewrite <- Hy in IHSum.
      assert (Hxx: forall a b c d, 
          a >= b + (c + d)
          -> a - c >=  b + d).
        clear.  
        intros.
        omega.
      apply Hxx; trivial.
    tmap_simpl.
    rewrite sum_del_none; auto.
    assert (Hy: v >= m a + sum m (a' :: al')).
      apply IHSum; trivial.
        simpl.
        simplbeq.
        trivial.
      simpl.
      rewrite Hx.
      simpl.
      trivial.
    simpl in Hy.
    omega.
Qed.

Lemma Sum_ge : forall m a t,
        Sum m t
        -> t >= m a.
Proof.
  intros.
  assert (Hx:= Sum_ge_strong _ _ H a nil).
  simpl in Hx.
  substH Hx with (Hx (eq_refl _) (eq_refl _)).
  omega.
Qed.

Lemma Sum_ge_2 : forall m a a' t,
        Sum m t
        -> beq a a' = false
        -> t >= m a + m a'.
Proof.
  intros.
  assert (Hx:= Sum_ge_strong _ _ H a (a'::nil)).
  simpl in Hx.
  rewrite H0 in Hx.
  assert (m a + m a' =m a + (m a' + 0)). omega.
  rewrite <- H1 in Hx.
  apply Hx.
  trivial. trivial.
Qed.

Lemma Sum_sig : 
  forall m a t,
    m = $0 $+ { a <- t }
    -> Sum m t.
Proof.
  intros m a t Hm.
  rewrite Hm.
  assert (t = 0 + t).
    auto with arith.
  rewrite H at 2.
  constructor 2.
    constructor 1.
  simpltm.
  trivial.
Qed.

Lemma Sum_dec : forall m t a (v: value),
        Sum m t
        -> m a >= v
        -> Sum  (m $+ {a <- -= v}) (t - v).
Proof.
 unfold a2v_upd_dec.
  intros m t a v H.
  generalize dependent v.
  generalize dependent a.
  induction H.
  + intros.
    simpl in H.
    assert (v = 0).
      unfold value in * .
      omega.
    simpl.
    assert ($0 $+ {a <- (0:value)} = $0).
      simpl.
      apply tmap_extensionality.
      intro a'.
      decbeq a a'.
      rewrite (tmap_get_upd_eq2 $0 a a' (0:value)); auto.
      tmap_simpl.
      assert(Ht: minus_with_underflow 0 v = 0 - v).
      apply minus_safe; trivial.
      rewrite Ht.
      rewrite H0.
      assert(Hm: 0 - 0 = 0);auto.
      rewrite Hm.
    rewrite H1.
    constructor 1.
  + intros a v2 H1.
    decbeq a a'.
      tmap_simpl.
      beq_elimH Hb.
      subst a'.
      assert(Ht: minus_with_underflow v' v2 = v' - v2).
      apply minus_safe; trivial.
      rewrite Ht.
      arith_rewrite (v + v' - v2 = v + (v' - v2)).
      constructor 2; trivial.
    simpltm.
    rewrite (tmap_upd_upd_ne); simplbeq; auto.
    assert (Hx : v + v' - v2 = v - v2 + v').
       assert (v >= m a). apply Sum_ge. apply H.
       assert (v >= v2). omega.
       unfold value in *. omega.
    rewrite Hx.
    constructor; trivial.
      apply IHSum; trivial.
    simpltm.
  + intros a v0 H1.
    decbeq a a'.
      simpltm.
      assert (v0 = 0).
        unfold value in *. omega.
      subst v0.
      simpl.
      simpltm.
      beq_elimH Hb.
      subst a'.
      assert (Hx: v - m a - 0 = v - m a).
        unfold value in *. omega.
      rewrite Hx.
      constructor; trivial.
    simpltm.
    rewrite (tmap_upd_upd_ne); simplbeq; auto.
    assert (Hx: v - m a' - v0 = v - v0 - m a').
       unfold value in *. omega.
    rewrite Hx.
    assert (Hm: m a' = (m $+ {a <- minus_with_underflow (m a) v0}) a').
    simpltm.
    rewrite Hm.
    constructor 3.
    apply IHSum; trivial.
Qed.

Lemma Sum_inc : forall m t a (v: value),
        Sum m t
        -> m a <= MAX_UINT256 - v
        -> Sum  (m $+ {a <- += v}) (t + v).
Proof.
  unfold a2v_upd_inc.
  intros m t a v H Hlt.
  generalize dependent v.
  generalize dependent a.
  induction H.
  +  intros.
     simpltm.
     assert (plus_with_overflow TMap.zero v = v).
     apply plus_safe_lhs0; auto.
     rewrite H.
     constructor 2; auto; try constructor.
  + intros a v2 Hlt.
    decbeq a a'.
      tmap_simpl.
      beq_elimH Hb.
      subst a'.
      arith_rewrite (v + v' + v2 = v + (v' + v2)).
      rewrite (plus_safe_lt v' v2); trivial.
      constructor 2; trivial.
    simpltm.
    substH IHSum with (IHSum a v2).
    rewrite (tmap_upd_upd_ne); simplbeq; auto.
    arith_rewrite (v + v' + v2 = v + v2 + v').
    constructor 2; auto.
    simpltm.
  + intros a v0.
    decbeq a a'.
      beq_elimH Hb.
      subst a'.
      assert (plus_with_overflow ((m $+ {a <- 0}) a)  v0 = v0).
        rewrite tmap_get_upd_eq.
        rewrite plus_safe_lhs0; trivial.
      rewrite H0.
      constructor 2.
      constructor 3.
      trivial.
      simpltm.
  simpltm.
  rewrite (tmap_upd_upd_ne); simplbeq; auto.
  assert (Hx: v - m a' + v0 = v + v0 - m a').
    assert (Hy: v >= m a').
      apply (Sum_ge m a' v); trivial.
    omega.
  rewrite Hx.
  assert (m a' = m $+ {a <- plus_with_overflow (m a) v0} a').
    simpltm.
  rewrite H0.
  constructor 3.
  apply IHSum; trivial.
Qed.

Lemma a2v_upd_inc_zero : forall m a,
        m $+ {a <- += 0} = m.
Proof.
  unfold a2v_upd_inc.
  intros.
  rewrite(plus_safe_rhs0 (m a) 0); trivial.
  assert (Hx : m a + 0 = m a).
    unfold value in *. omega.
  rewrite Hx.
  tmap_simpl.
Qed.

Lemma a2v_upd_dec_zero : forall m a,
        m $+ {a <- -= 0} = m.
Proof.
  unfold a2v_upd_dec.
  intros.
  rewrite(minus_safe (m a) 0).
  assert (Hx : m a - 0 = m a).
    unfold value in *. omega.
  rewrite Hx.
  tmap_simpl.
  omega.
Qed.

Lemma test : forall a b,
    a >= b -> a = a - b + b.
Proof.
  intros.
  omega.
Qed.

Lemma Sum_transfer : forall m t a1 a2 v m',
        Sum m t
        -> m a1 >= v
        -> m a2 <= MAX_UINT256 - v
        -> m' = m $+{a1 <- -= v} $+{a2 <- += v}
        -> Sum m' t.
Proof.
  intros.
  decbeq a1 a2.
  + beq_elimH Hb.
    subst a2.
    rewrite H2.
    assert (Ht: t = t - v + v).
      assert (Ht1 : t >= m a1).
        apply Sum_ge; trivial.
      assert (Ht2 : t >= v).
        omega.
      clear - Ht2.
      unfold value in t.
      eapply test; eauto.
    rewrite Ht.
    eapply Sum_inc; eauto.
    eapply Sum_dec; eauto.
    unfold a2v_upd_dec.
    rewrite (tmap_get_upd_eq m a1 _).
    rewrite(minus_safe (m a1) v); auto.
    omega.
  + remember (m a1) as Ha1.
    remember (m a2) as Ha2.
    rewrite HeqHa1 in H0.
    destruct Ha1.
      assert (Hv : v = 0).
        rewrite <- HeqHa1 in H0.
        auto with arith.
      subst v.
      rewrite a2v_upd_dec_zero in H2.
      rewrite a2v_upd_inc_zero in H2.
      rewrite H2; trivial.
    assert (Hx := Sum_ge _ a1 _ H).
    assert (Ht : t = t - v - (m $+ {a1 <- -= v} a2) + (m $+ {a1 <- -= v} a2) + v).
      unfold a2v_upd_dec.
      simpltm.
      assert (Ht2 : t >= v).
        omega.
      assert (Ht3: t >= m a1 + m a2).
        apply Sum_ge_2; trivial.
      rewrite minus_minus.
      arith_rewrite (t - (v + m a2) + m a2 + v = t - (v + m a2) + (v + m a2)).
      rewrite <- test; trivial.
      omega.
    rewrite Ht.
    rewrite H2.
    unfold a2v_upd_dec in * .
    unfold a2v_upd_inc in * .
    apply Sum_inc.
    simpltm.
    assert (Ht3: t >= m a1 + m a2).
      apply Sum_ge_2; trivial.
    arith_rewrite (t - v - m a2 + m a2 = t - v).
    apply Sum_dec; trivial.
    simpltm.
    omega.
Qed.

Lemma Sum_Burn : forall m t a1 v m',
        Sum m t
        -> m a1 >= v
        -> m' = m $+{a1 <- -= v}
        -> Sum m' (t-v).
Proof.
  intros.
  rewrite H1. apply Sum_dec. apply H. apply H0.
Qed.

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

Definition INV (env: env) (S: state) (E: eventlist) : Prop :=
  let blncs := st_balances S in
  (* balances not overflow *)
  (forall a, blncs a <= MAX_UINT256) /\
  (* totalSupply preserves *)
  exists total,
    total = st_totalSupply S
    /\ Sum blncs total
    /\ exists creator, exists name, exists decimals, exists sym, exists burnValue,
       assert_genesis_event (ev_BurnableToken creator (total+burnValue) name decimals sym) E.

Lemma sub_add_add: forall (total v x:nat),
    total >= v ->
     total - v + (v + x) = total + x.
Proof.
  intros.
  rewrite <- Nat.add_sub_swap.
  omega.
  auto.
Qed.

 Lemma abc : forall a b c, a >= b -> b >= c -> a >= c.
   intros.
   omega.
 Qed.

(* step evaluation maintains invariant *)
Theorem step_INV: forall this env msg S E env' S' E',
    step env (mk_contract this S) msg (mk_contract this S') E'
    -> env_step env env'
    -> INV env S E
    -> INV env' S' (E ++ E').
Proof.
  intros this env msg S E env' S' E'.
  intros Hstep Henv' HI.
  destruct HI as [Hblncs [total [Htotal [Htv [creator [name [decimals [sym Hassert]]]]]]]].
  inversion_clear Hstep.
  (* case: transfer *)
  - unfold funcspec_transfer in H1.
    subst spec preP evP postP.
    simpl in *.
    subst msg.
    simpl in H5.
    destruct H5 as [[Hx1a Hx1b] [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 [Hx7 Hx8]]]]]]].
    destruct Hx1b.

    + (* msg.sender == to *)
      subst sender.
      rewrite <- (a2v_dec_inc_id _ _ _ (Hblncs to) Hx1a) in Hx8.
      rewrite <- Hx8 in *.
      split; auto.

      exists total.
      repeat split; subst; auto.
      exists creator. exists name. exists decimals. exists sym.
      inversion Hassert.  exists x.
      apply assert_genesis_event_app; auto.

    + (* msg.sender != to *)
      destruct H0 as [Hsender Hof].
      split.
      * (* no overflow *)
        rewrite Hx8.
        intros.
        destruct (beq_dec a to).
        {
          (* a == to *)
          rewrite Nat.eqb_eq in H0.
          subst a.
          apply neq_beq_false in Hsender.
          unfold a2v_upd_inc, a2v_upd_dec.
          rewrite (tmap_upd_upd_ne _ _ _ _ _ Hsender).
          rewrite (tmap_get_upd_ne _ _ _ _ Hsender).
          rewrite (tmap_get_upd_eq _ _ _).
          rewrite (tmap_get_upd_ne _ _ _ _ Hsender).
          rewrite (plus_safe_lt _ _ Hof).
          generalize(Hblncs sender). intros. omega.
        }
        {
          (* a <> to *)
          apply beq_sym in H0.
          unfold a2v_upd_inc, a2v_upd_dec.
          rewrite (tmap_get_upd_ne _ _ _ _ H0).
          destruct (beq_dec a sender).
          - (* a == sender *)
            rewrite Nat.eqb_eq in H1.
            subst a.
            rewrite (tmap_get_upd_eq _ _ _).
            rewrite (minus_safe _ _ Hx1a).
            generalize (Hblncs sender). intros. omega.
          - (* a <> sender *)
            apply beq_sym in H1.
            rewrite (tmap_get_upd_ne _ _ _ _ H1).
            generalize (Hblncs a). intros. omega.
        }
      * (* totalSupply preserves *)
        exists total.
        rewrite <- Htotal in *.
        repeat split; auto.
        {
          apply (Sum_transfer (st_balances S) total
                              sender to v (st_balances S'));
            auto with arith.
        }
        {
          exists creator. exists name. exists decimals. exists sym.
          inversion Hassert.  exists x.
          apply assert_genesis_event_app; auto.
        }

  (* case: transferFrom-1 *)
  - unfold funcspec_transferFrom_1 in H1.
    subst spec.
    simpl in *.
    destruct H2 as [[Hx1a [Hx1b [Hx1c Hx1d]]] [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 [Hx7 Hx8]]]]]]].
    destruct Hx1b.

    + (* from = to *)
      subst from.
      rewrite <- (a2v_dec_inc_id _ _ _ (Hblncs to) Hx1a) in Hx7.
      rewrite <- Hx7 in *.
      split; auto.

      exists total.
      repeat split; subst; auto.
      exists creator. exists name. exists decimals. exists sym.
      inversion Hassert.  exists x.
      apply assert_genesis_event_app; auto.

    + (* from <> to *)
      destruct H1 as [Hfrom Hof].
      split.
      * (* no overflow *)
        rewrite Hx7.
        intros.
        destruct (beq_dec a to).
        {
          (* a == to *)
          rewrite Nat.eqb_eq in H1.
          subst a.
          apply neq_beq_false in Hfrom.
          unfold a2v_upd_inc, a2v_upd_dec.
          rewrite (tmap_upd_upd_ne _ _ _ _ _ Hfrom).
          rewrite (tmap_get_upd_ne _ _ _ _ Hfrom).
          rewrite (tmap_get_upd_eq _ _ _).
          rewrite (tmap_get_upd_ne _ _ _ _ Hfrom).
          rewrite (plus_safe_lt _ _ Hof).
          generalize(Hblncs from). intros. omega.
        }
        {
          (* a <> to *)
          apply beq_sym in H1.
          unfold a2v_upd_inc, a2v_upd_dec.
          rewrite (tmap_get_upd_ne _ _ _ _ H1).
          destruct (beq_dec a from).
          - (* a == from *)
            rewrite Nat.eqb_eq in H2.
            subst a.
            rewrite (tmap_get_upd_eq _ _ _).
            rewrite (minus_safe _ _ Hx1a).
            generalize (Hblncs from). intros. omega.
          - (* a <> sender *)
            apply beq_sym in H2.
            rewrite (tmap_get_upd_ne _ _ _ _ H2).
            generalize (Hblncs a). intros. omega.
        }
      * (* totalSupply preserves *)
        exists total.
        rewrite <- Htotal in *.
        repeat split; auto.
        {
          apply (Sum_transfer (st_balances S) total
                              from to v (st_balances S'));
            auto with arith.
        }
        {
          exists creator. exists name. exists decimals. exists sym.
          inversion Hassert.  exists x.
          apply assert_genesis_event_app; auto.
        }

  (* case: transferFrom-2 *)
  - unfold funcspec_transferFrom_2 in H1.
    subst spec.
    simpl in *.
    destruct H2 as [[Hx1a [Hx1b [Hx1c Hx1d]]] [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 [Hx7 Hx8]]]]]]].
    destruct Hx1b.

    + (* from = to *)
      subst from.
      rewrite <- (a2v_dec_inc_id _ _ _ (Hblncs to) Hx1a) in Hx7.
      rewrite <- Hx7 in *.
      split; auto.

      exists total.
      repeat split; subst; auto.
      exists creator. exists name. exists decimals. exists sym.
      inversion Hassert.  exists x.
      apply assert_genesis_event_app; auto.

    + (* from <> to *)
      destruct H1 as [Hfrom Hof].
      split.
      * (* no overflow *)
        rewrite Hx7.
        intros.
        destruct (beq_dec a to).
        {
          (* a == to *)
          rewrite Nat.eqb_eq in H1.
          subst a.
          apply neq_beq_false in Hfrom.
          unfold a2v_upd_inc, a2v_upd_dec.
          rewrite (tmap_upd_upd_ne _ _ _ _ _ Hfrom).
          rewrite (tmap_get_upd_ne _ _ _ _ Hfrom).
          rewrite (tmap_get_upd_eq _ _ _).
          rewrite (tmap_get_upd_ne _ _ _ _ Hfrom).
          rewrite (plus_safe_lt _ _ Hof).
          generalize(Hblncs from). intros. omega.
        }
        {
          (* a <> to *)
          apply beq_sym in H1.
          unfold a2v_upd_inc, a2v_upd_dec.
          rewrite (tmap_get_upd_ne _ _ _ _ H1).
          destruct (beq_dec a from).
          - (* a == from *)
            rewrite Nat.eqb_eq in H2.
            subst a.
            rewrite (tmap_get_upd_eq _ _ _).
            rewrite (minus_safe _ _ Hx1a).
            generalize (Hblncs from). intros. omega.
          - (* a <> sender *)
            apply beq_sym in H2.
            rewrite (tmap_get_upd_ne _ _ _ _ H2).
            generalize (Hblncs a). intros. omega.
        }
      * (* totalSupply preserves *)
        exists total.
        rewrite <- Htotal in *.
        repeat split; auto.
        {
          apply (Sum_transfer (st_balances S) total
                              from to v (st_balances S'));
            auto with arith.
        }
        {
          exists creator. exists name. exists decimals. exists sym.
          inversion Hassert.  exists x.
          apply assert_genesis_event_app; auto.
        }

  (* case: balanceOf *)
  - unfold funcspec_balanceOf in H2.
    subst spec.
    simpl in *.
    destruct H5 as [Hx1 [Hx2 Hx3]].
    rewrite H4 in Hx3. rewrite <- Hx3.
    split; auto.
    exists total.
    repeat split; auto.
    exists creator. exists name. exists decimals. exists sym.
    inversion Hassert.  exists x.
    apply assert_genesis_event_app; auto.

  (* case: approve *)
  - unfold funcspec_approve in H1.
    subst spec.
    simpl in *.
    destruct H2 as [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 [Hx7 Hx8]]]]]]].
    rewrite <- Hx7 in *.
    split; auto.
    exists total.
    rewrite Hx3 in *.
    rewrite Hx7 in *.
    repeat split; auto.
    exists creator. exists name. exists decimals. exists sym.
    inversion Hassert.  exists x.
    apply assert_genesis_event_app; auto.

  (* case: allowance *)
  - unfold funcspec_allowance in H1.
    subst spec.
    simpl in *.
    destruct H2 as [Hx1 [Hx2 Hx3]].
    subst S'.
    split; auto.
    exists total.
    simpl.
    repeat split; auto.
    exists creator. exists name. exists decimals. exists sym.
    inversion Hassert.  exists x.
    apply assert_genesis_event_app; auto.

  (* case: totalSupply *)
  - unfold funcspec_totalSupply in H1.
    subst spec.
    simpl in *.
    destruct H5 as [Hx1 [Hx2 Hx3]].
    rewrite H4 in Hx3. rewrite <- Hx3.
    split.
    + auto.
    + exists total.
      repeat split; auto.
      exists creator. exists name. exists decimals. exists sym.
      inversion Hassert.  exists x.
      apply assert_genesis_event_app; auto.

   (* case: funcspec_Burn *)
  - unfold funcspec_Burn in H1.
    subst spec.
    simpl in *.
    destruct H5 as [Hx1 [Hx2 Hx3]].
    rewrite H4 in Hx3.
    destruct Hx3 as [Hx31 [Hx32 [Hx33 [Hx34 [Hx35 Hx36]]]]].
    split.
    + rewrite Hx32. intros a.
      unfold a2v_upd_dec.
      destruct (beq_dec a (m_sender msg)).
      {
        (* a == m_sender msg *)
        rewrite Nat.eqb_eq in H1.
        subst a.
        
        rewrite (tmap_get_upd_eq _ _ _).
        generalize (Hblncs (m_sender msg)).
        intros Hs.
        rewrite H2 in Hx1.
        destruct Hx1.
        rewrite (minus_safe _ _ H1).
        omega. 
      }
      {
        (* a <> m_sender msg *)
         apply beq_sym in H1.
         rewrite (tmap_get_upd_ne _ _ _ _ H1).
         generalize (Hblncs a). intros. omega.
      }
   + exists (total-v).
     repeat split; auto.
     rewrite Hx31. auto.
     rewrite Hx32.
     rewrite H2 in Hx1.
     destruct Hx1.
     generalize H1.
     generalize Htv.
     apply Sum_dec.     
     exists creator. exists name. exists decimals. exists sym.
     inversion Hassert.  exists (v+x).
     assert (total - v + (v+x) = total+x). 
     apply sub_add_add.
     rewrite H2 in Hx1.
     assert (total >= st_balances S (m_sender msg)).
     rewrite Htotal.
     apply Sum_ge.
     rewrite Htotal in Htv. auto.
     destruct Hx1.
     
     generalize H6. generalize H5.
     apply abc.
     rewrite H5.
     apply assert_genesis_event_app; auto.
Qed.

(* create evaluation maintains invariant *)
Theorem create_INV : forall env0 env C E,
    create env0 C E
    -> env_step env0 env
    -> INV env (w_st C) E.
Proof.
  intros.
  inversion_clear H.
  unfold funcspec_BurnableToken in H2.
  subst spec. simpl in *.
  destruct H6 as [Hx1 [Hx2 Hx3]].
  unfold INV.
  rewrite H3 in Hx1.
  rewrite H4 in Hx2.
  rewrite H5 in Hx3.
  destruct Hx3 as [Hto [Hb Hxx]].
  split.
  - (* no overflow initially *)
  
    rewrite Hb.
    intros a.
    destruct (beq_dec a (m_sender msg)).
    + rewrite Nat.eqb_eq in H.
      subst a.
      rewrite (tmap_get_upd_eq _ _ _). auto.
    + rewrite Nat.eqb_neq in H.
      rewrite tmap_get_upd_ne.
      simpl.
      omega.
      apply neq_beq_false in H.
      apply beq_sym in H.
      auto.

  - (* totalSupply preserves *)
    exists ia.
    repeat split; auto.
    + rewrite Hb.
      apply Sum_sig with (m_sender msg).
      auto.
    + exists (w_a C). exists name. exists dec. exists sym.
      exists 0.
      unfold assert_genesis_event.
      subst E.
      assert (ia+0 = ia). omega.
      rewrite H.
      trivial.
Qed.

Lemma step_contract_address_constant : forall env C I C' E',
      step env C I C' E'
      -> w_a C = w_a C'.
Proof.
  intros.
  destruct C as [a S].
  destruct C' as [a' S'].
  induction H; simpl; auto; intuition.
Qed.


Lemma steps_INV: forall ml env C E,
    INV env (w_st C) E
    -> forall env' C' E', steps env C ml env' C' E'
    -> INV env' (w_st C') (E ++ E').
Proof.
  induction ml.

  - (* nil *)
    intros.
    inversion_clear H0.
    destruct H2.
    subst.
    rewrite app_nil_r.
    trivial.

  - (* a :: ml *)
    intros.
    inversion_clear H0.
    rename x into envx.
    rename a into msg.
    destruct H1 as [Cx [Ex [Ey [H1 [H2 [H3 H4]]]]]].
    subst E'.
    assert (Hx : INV envx (w_st Cx) (E ++ Ex)).
    {
      assert (w_a C = w_a Cx).
      {
        apply step_contract_address_constant with env msg Ex. apply H1.
      }
      destruct C as [C_a C_st].
      destruct Cx as [Cx_a Cx_st].
      simpl. simpl in H. simpl in H0. generalize H. generalize H4.
      apply step_INV with C_a msg.
      subst Cx_a. apply H1.
    }
    substH IHml with (IHml envx Cx (E ++ Ex) Hx).
    rewrite app_assoc.
    apply IHml; trivial.
Qed.

Lemma INV_implies_totalSupply_fixed :
  forall env S E,
    INV env S E
    -> Sum (st_balances S) (st_totalSupply S).
Proof.
  intros env S E HI.
  unfold INV in HI.
  destruct HI as [_ [total [Ht [HT HI]]]].
  rewrite Ht in HT.
  trivial.
Qed.

(* Prop #1: total supply is fixed *)
Theorem Property_totalSupply_fixed : 
  forall env0 env ml C E C' E',
    create env0 C E
    -> env_step env0 env
    -> run env C ml C' E'
    -> Sum (st_balances (w_st C')) (st_totalSupply (w_st C')).
Proof.
  intros env0 env ml C E C' E' Hc Hs Hr.
  unfold run in Hr.
  destruct Hr as [env' Hsteps].
  apply INV_implies_totalSupply_fixed with env' (E++E').
  substH Hc with (create_INV _ _ C E Hc Hs).
  eapply steps_INV; eauto.
Qed.
