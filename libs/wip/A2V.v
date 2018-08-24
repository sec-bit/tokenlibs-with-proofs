Require Import ZArith.
Require Import Lists.List.

Require Import Mapping.
Require Import ElemTypes.
Require Import Types.
Require Import LibEx.

Module Import A2V := Mapping (Address_as_DT) (ValElem).
Definition a2v: Type := A2V.t.

Notation "$0" := (A2V.empty) (only parsing) : a2v_scope.

Notation "m '$' k" :=
  (A2V.get m k)
    (at level 50, left associativity, only parsing) : a2v_scope.

Notation "m '$' '{' k '<~' v '}'" :=
  (A2V.upd m k v)
    (at level 50, left associativity, only parsing) : a2v_scope.

Notation "m '$' '{' k '<+~' v '}'" :=
  (A2V.upd_inc m k v)
    (at level 50, left associativity, only parsing) : a2v_scope.

Notation "m '$' '{' k '<-~' v '}'" :=
  (A2V.upd_dec m k v)
    (at level 50, left associativity, only parsing) : a2v_scope.

Notation "m '~' m'" :=
  (A2V.equal m m')
    (at level 70, no associativity, only parsing) : a2v_scope.

Open Scope a2v_scope.

Section Compare.
  Lemma upd_dec_le:
    forall m k k' v upper,
      v <= m $ k <= upper ->
      m $ k' + v <= upper ->
      m $ { k <-~ v } $ k' + v <= upper.
  Proof.
    intros m k k' v upper [Hk_lo Hk_hi] Hk'.
    destruct (Nat.eq_dec k' k).

    - (* k = k' *)
      subst k'.
      msimpl.
      rewrite (minus_safe _ _); omega.

    - (* k <> k' *)
      msimpl; omega.
  Qed.
End Compare.

Section Sum.

  Lemma sum_empty:
    A2V.sum $0 = 0.
  Proof.
    auto.
  Qed.

  Lemma sum_raw_upper:
    forall m k v nodup ,
      A2V.map.find (elt:=value) k {| A2V.map.this := m; A2V.map.NoDup := nodup |} = Some v ->
      v <= A2V.sum_raw m.
  Proof.
    unfold A2V.map.find.
    unfold A2V.map.Raw.find.
    induction m; simpl.

    - intros. inversion H.

    - intros. destruct a.
      destruct (Address_as_DT.eq_dec k n).

      + inversion H. omega.

      + inversion nodup.
        generalize (IHm _ _ H3 H). omega.
  Qed.

  Lemma sum_upper:
    forall m k, m $ k <= A2V.sum m.
  Proof.
    unfold A2V.get, A2V.sum.
    unfold A2V.map.elements.
    unfold A2V.map.Raw.elements.
    destruct m.
    simpl; intros.
    case_eq (A2V.map.find (elt:=value) k {| A2V.map.this := this; A2V.map.NoDup := NoDup |});
      intros.
    - eapply sum_raw_upper; eauto.
    - auto with arith.
  Qed.

  Lemma sum_upd:
    forall m t,
      A2V.sum m = t ->
      forall k v oldv,
        m $ k = oldv ->
        A2V.sum (m $ { k <~ v }) = t - oldv + v.
  Proof.
    destruct m.
    induction this.

    - (* nil *)
      unfold A2V.sum.
      unfold A2V.get.
      simpl.
      intros.
      subst.
      auto.

    - (* a :: this *)
      unfold A2V.sum in *.
      unfold A2V.get in *.
      simpl in *.
      destruct a.

      intros.
      destruct (Address_as_DT.eq_dec k n).

      + subst; simpl.
        unfold A2V.map.find. simpl.
        unfold Address_as_DT.eq_dec.
        destruct (Nat.eq_dec n n).
        * omega.
        * destruct n0; auto.

      + simpl.
        assert (Hsum: A2V.sum_raw this = t - v).
        { omega. }
        inversion NoDup.
        rewrite (find_hd_neq_tl NoDup H4 n0) in H0.
        generalize (IHthis _ _ Hsum _ v0 _ H0). intros Hsum'.
        rewrite Hsum'.

        assert (oldv <= t - v).
        {
          case_eq (A2V.map.find (elt:=value) k {| A2V.map.this := this; A2V.map.NoDup := H4 |});
            intros.
          - rewrite H5 in H0.
            rewrite H0 in H5.
            rewrite <- Hsum.
            eapply sum_raw_upper; eauto.
          - rewrite H5 in H0.
            rewrite <- H0.
            auto with arith.
        }

        omega.
  Qed.

  Lemma sum_upd_inc:
    forall m t,
      A2V.sum m = t ->
      forall k v,
        m $ k <= MAX_UINT256 - v ->
        A2V.sum (m $ { k <+~ v }) = t + v.
  Proof.
    intros m t Hsum k v Hle.
    unfold A2V.upd_inc.
    rewrite (plus_safe_lt _ _); auto.
    erewrite sum_upd; eauto.
    generalize (sum_upper m k); intros.
    omega.
  Qed.

  Lemma sum_upd_dec:
    forall m t,
      A2V.sum m = t ->
      forall k v,
        m $ k >= v ->
        A2V.sum (m $ { k <-~ v}) = t - v.
  Proof.
    intros m t Hsum k v Hge.
    unfold A2V.upd_dec.
    rewrite (minus_safe _ _); auto.
    erewrite sum_upd; eauto.
    generalize (sum_upper m k); intros.
    omega.
  Qed.

  Lemma sum_transfer:
    forall m k k' v,
      m $ k >= v ->
      m $ k' <= MAX_UINT256 - v ->
      A2V.sum (m $ { k <-~ v } $ { k' <+~ v } ) = A2V.sum m.
  Proof.
    intros m k k' v Hlo Hhi.
    erewrite sum_upd_inc; eauto.
    erewrite sum_upd_dec; eauto.
    - generalize (sum_upper m k); intros; omega.
    - destruct (Nat.eq_dec k' k).
      + subst k'. msimpl.
        rewrite (minus_safe _ _); auto.
        omega.
      + msimpl.
  Qed.

  Lemma sum_descend:
    forall k k',
      k <> k' ->
      forall m,
        m $ k <= sum m - (m $ k').
  Proof.
    destruct m. induction this; simpl.

    - unfold get. auto.

    - inversion NoDup; subst.
      destruct a.
      generalize (A2V.sum_cons NoDup H3).
      intros Heq; rewrite Heq; clear Heq.

      destruct (Nat.eq_dec k n).
      + subst. msimpl.
        assert (Hneq: k' <> n). auto.
        rewrite (A2V.get_hd_neq NoDup H3 Hneq).
        generalize (sum_upper ({| map.this := this; map.NoDup := H3 |}) k');
          intros Hget.
        omega.

      + rewrite (A2V.get_hd_neq NoDup H3 n0).
        destruct (Nat.eq_dec k' n).
        * subst.
          rewrite (A2V.get_hd_eq' NoDup).
          generalize (sum_upper ({| map.this := this; map.NoDup := H3 |}) k);
            intros Hget.
          omega.
        * rewrite (A2V.get_hd_neq NoDup H3 n1).
          substH IHthis with (IHthis H3).
          omega.
  Qed.

  Lemma sum_filter_descend:
    forall m k v nodup nodup' f,
      sum_filter {| map.this := m; map.NoDup := nodup |} f <=
      sum_filter {| map.this := (k, v) :: m; map.NoDup := nodup' |} f.
  Proof.
    induction m; intros; simpl.

    - unfold sum_filter.
      unfold map.elements.
      simpl.
      omega.

    - case_eq (f (k, v)); intros Hf.
      + rewrite (sum_filter_hd_true nodup' nodup Hf).
        destruct a as [k' v'].
        inversion nodup; subst.
        substH IHm with (IHm k' v' H2 nodup f).
        omega.

      + rewrite (sum_filter_hd_false nodup' nodup Hf).
        omega.
  Qed.

  Lemma sum_filter_true_upper:
    forall f k m,
      f (k, m $ k) = true -> m $ k <= sum_filter m f.
  Proof.
    destruct m. induction this; simpl; intros Hf.

    - unfold get, sum_filter.
      simpl. auto.

    - destruct a as [k' v'].
      inversion NoDup; subst.
      destruct (Nat.eq_dec k k').

      + subst k'.
        msimpl.
        msimpl_in Hf.
        rewrite (A2V.sum_filter_hd_true NoDup H2 Hf).
        omega.

      + rewrite (get_hd_neq NoDup H2 n) in *.
        substH IHthis with (IHthis H2 Hf).
        generalize (sum_filter_descend this k' v' H2 NoDup f); intros.
        omega.
  Qed.

  Lemma sum_filter_descend_true:
    forall f k k',
      k <> k' ->
      (forall v, f (k, v) = true) ->
      (forall v, f (k', v) = true) ->
      forall m,
        m $ k <= sum_filter m f - (m $ k').
  Proof.
    destruct m.
    induction this; simpl; auto.

    destruct a as [k'' v''].
    inversion NoDup; subst.

    destruct (Nat.eq_dec k k'').

    - (* k = k'' *)
      subst k''.
      msimpl.
      rewrite (get_hd_neq NoDup H5); auto.
      rewrite (sum_filter_hd_true NoDup H5); auto.
      substH H1 with (H1 (get {| map.this := this; map.NoDup := H5 |} k')).
      generalize (sum_filter_true_upper
                    f
                    k'
                    {| map.this := this; map.NoDup := H5 |}
                    H1);
        intros Hle.
      omega.

    - (* k <> k'' *)
      rewrite (get_hd_neq NoDup H5 n).
      case_eq (f (k'', v'')); intros Hf.
      + rewrite (sum_filter_hd_true NoDup H5 Hf).
        substH H0 with (H0 (get {| map.this := this; map.NoDup := H5 |} k)).
        generalize (sum_filter_true_upper
                      f
                      k
                      {| map.this := this; map.NoDup := H5 |}
                      H0);
          intros Hle.
        destruct (Nat.eq_dec k' k'').
        * subst k''. msimpl.
          omega.
        * substH IHthis with (IHthis H5).
          rewrite (get_hd_neq NoDup H5 n0).
          omega.
      + destruct (Nat.eq_dec k' k'').
        * subst k''.
          substH H1 with (H1 v'').
          rewrite Hf in H1; inversion H1.
        * rewrite (sum_filter_hd_false NoDup H5 Hf).
          rewrite (get_hd_neq NoDup H5 n0).
          apply IHthis.
  Qed.

  Lemma sum_filter_one_bit:
    forall k f g,
      (forall v, f (k, v) = true) ->
      (forall v, g (k, v) = false) ->
      (forall k' v', k <> k' -> f (k', v') = g (k', v')) ->
      forall m,
        sum_filter m f = (sum_filter m g) + (m $ k).
  Proof.
    intros k f g Hf Hg Hfg.
    destruct m.
    induction this; unfold sum_filter, get; simpl; auto.

    destruct a as [k'' v''].
    destruct (Nat.eq_dec k k'').

    - (* k'' = k *)
      subst k''.

      rewrite (Hf v'').
      rewrite (Hg v'').

      generalize (A2V.find_hd_eq NoDup); intros Hfind.
      rewrite A2V.find_hd_eq.
      simpl.

      inversion NoDup; subst.
      substH IHthis with (IHthis H2).

      generalize (find_hd_neq_none NoDup H2); clear Hfind; intros Hfind.
      rewrite (not_find_get Hfind) in IHthis; clear Hfind.

      unfold sum_filter in IHthis; simpl in IHthis.
      omega.

    - (* k'' <> k *)
      inversion NoDup; subst.
      generalize (find_hd_neq_tl NoDup H2 n); intros Hnot_find.
      substH Hfg with (Hfg k'' v'' n).
      substH IHthis with (IHthis H2).
      unfold sum_filter, get in IHthis; simpl in IHthis.

      case_eq (f (k'', v''));
        intros Hf';
        rewrite Hf' in Hfg;
        rewrite <- Hfg;
        simpl;
        rewrite Hnot_find; omega.
  Qed.

  Lemma sum_sum_filter_true_le:
    forall f k,
      (forall v, f (k, v) = true) ->
      forall m m' k',
        k' <> k ->
        m $ k' <= sum m + sum_filter m' f - ((m $ k) + (m' $ k)).
  Proof.
    intros f k Hf m m' k' Hneq.

    generalize (sum_upper m k); intros.
    generalize (sum_descend k' k Hneq m); intros.
    generalize (sum_filter_true_upper f k m' (Hf _)); intros.

    omega.
  Qed.
End Sum.

Hint Resolve sum_empty
     sum_raw_upper sum_upper
     sum_upd sum_upd_inc sum_upd_dec
     sum_transfer.

Ltac sum_simpl :=
  match goal with
  (* sum_empty *)
  | [ |- context [ A2V.sum $0 ] ]
    => rewrite sum_empty;
       auto; sum_simpl

  (* sum_upd *)
  | [ |- context [ A2V.sum (?m $ { ?k <~ ?v }) ] ]
    => rewrite (sum_upd _ _ (Nat.eq_refl (A2V.sum m)) _ _ _ (Nat.eq_refl (m $ k)));
       auto; sum_simpl

  (* sum_upd_inc *)
  | [ H: ?m $ ?k <= MAX_UINT256 - ?v
      |- context [ A2V.sum (?m $ { ?k <+~ ?v }) ]
    ]
    => rewrite (sum_upd_inc _ _ (Nat.eq_refl (A2V.sum m)) _ _ H);
       auto; sum_simpl

  (* sum_upd_dec *)
  | [ H: ?m $ ?k >= ?v
      |- context [ A2V.sum (?m $ { ?k <-~ ?v }) ]
    ]
    => rewrite (sum_upd_dec _ _ (Nat.eq_refl (A2V.sum m)) _ _ H);
       auto; sum_simpl

  (* sum_transfer *)
  | [ H0: ?m $ ?k >= ?v, H1: ?m $ ?k' <= MAX_UINT256 - ?v
      |- context [ A2V.sum (?m $ { ?k <-~ ?v } $ { ?k' <+~ ?v } ) ]
    ]
    => rewrite (sum_transfer _ _ _ _ H0 H1);
       auto; sum_simpl

  | _ => auto; idtac
  end.