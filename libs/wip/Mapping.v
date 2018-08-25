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

Require Import
        Nat
        ZArith
        List
        Coq.FSets.FMapWeakList
        Coq.Structures.DecidableType
        Coq.Structures.DecidableTypeEx.

Require Import
        Types.

Set Implicit Arguments.
Unset Strict Implicit.

Module Type ElemType.
  Parameter Inline elt: Type.
  Parameter Inline elt_zero: elt.
  Parameter Inline elt_add: elt -> elt -> elt.
  Parameter Inline elt_add_raw: elt -> elt -> elt.
  Parameter Inline elt_sub: elt -> elt -> elt.
  Parameter Inline elt_eq: elt -> elt -> Prop.

  Axiom elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.

  Axiom elt_add_raw_comm:
    forall x y, elt_eq (elt_add_raw x y) (elt_add_raw y x).

  Axiom elt_eq_refl:
    forall x, elt_eq x x.

  Axiom elt_zero_add:
    forall x, elt_add elt_zero x = x.

  Axiom elt_zero_add':
    forall x, elt_add x elt_zero = x.
End ElemType.

Module Mapping (K: DecidableType) (Elt: ElemType).
  Module Import map := FMapWeakList.Make(K).
  Module Import et := Elt.

  Notation t := (map.t elt).
  Notation empty := (map.empty elt).

  Definition get (m: t) (k: K.t) : elt :=
    match find k m with
    | Some v => v
    | None => elt_zero
    end.

  Definition equal (m m': t) := forall k, get m k = get m' k.

  Definition upd (m: t) (k: K.t) (v: elt) : t :=
    add k v m.

  Definition upd_inc (m: t) (k: K.t) (v: elt): t :=
    upd m k (elt_add (get m k) v).

  Definition upd_dec (m: t) (k: K.t) (v: elt): t :=
    upd m k (elt_sub (get m k) v).

  Fixpoint sum_raw (elst: list (K.t * elt)) : elt :=
    match elst with
    | nil => elt_zero
    | (k, v) :: lst => elt_add_raw v (sum_raw lst)
    end.

  Definition sum (m: t) : elt :=
    sum_raw (elements m).

  Definition sum_filter (m: t) (f: (K.t * elt) -> bool) : elt :=
    sum_raw (filter f (elements m)).

  Definition map_filter (m: t) (f: (K.t * elt) -> bool): list (K.t * elt) :=
    filter f (elements m).

  Section Aux.
    Lemma not_eq_sym:
      forall (k k': K.t), ~ K.eq k k' -> ~ K.eq k' k.
    Proof.
      intros k k' Hneq Heq.
      apply Hneq.
      apply K.eq_sym; auto.
    Qed.

    Lemma find_add_eq:
      forall (m: t) (k k': K.t) (v: elt),
        K.eq k' k -> find k (add k' v m) = Some v.
    Proof.
      intros.
      apply find_1; apply add_1; auto.
    Qed.

    Lemma find_add_neq:
      forall (m: t) (k k': K.t) (v: elt),
        ~ K.eq k' k -> find k' (add k v m) = find k' m.
    Proof.
      intros.
      case_eq (find k' m).

      - intros e Hfind.
        apply find_2 in Hfind.
        apply find_1.
        apply add_2; auto.

      - unfold find, Raw.find.
        destruct m. simpl.
        generalize this0 NoDup0 k k' v H; clear this0 NoDup0 k k' v H.
        induction this0.

        + intros. simpl.
          destruct (K.eq_dec k' k); auto.
          apply H in e; inversion e.

        + intros. simpl.
          destruct a.
          destruct (K.eq_dec k t).

          * {
              destruct (K.eq_dec k' k).
              - apply H in e1; inversion e1.
              - destruct (K.eq_dec k' t); auto.
                apply K.eq_sym in e0.
                apply (K.eq_trans e1) in e0.
                apply n in e0; inversion e0.
            }

          * {
              destruct (K.eq_dec k' t); auto.
              inversion NoDup0; auto.
            }
    Qed.

    Lemma not_in_neq:
      forall k v k' v' m,
        ~ InA (Raw.PX.eqk (elt := elt)) (k, v) ((k', v') :: m) ->
        ~ K.eq k k'.
    Proof.
      intros k v k' v' m Hnotin Heq.
      apply Hnotin.
      constructor; auto.
    Qed.

    Lemma not_in_neq':
      forall k k' v' m nodup,
        ~ In (elt:=elt) k {| this := (k', v') :: m; NoDup := nodup |} ->
        ~ K.eq k k'.
    Proof.
      unfold In, Raw.PX.In, Raw.PX.MapsTo.
      intros k k' v' m nodup Hnotin Heq.
      apply Hnotin.
      exists v'.
      constructor 1; auto.
    Qed.

    Lemma not_in_not_in:
      forall k v k' v' m,
        ~ InA (Raw.PX.eqk (elt := elt)) (k, v) ((k', v') :: m) ->
        ~ InA (Raw.PX.eqk (elt := elt)) (k, v) m.
    Proof.
      intros k v k' v' m Hnotin Hin.
      apply Hnotin.
      constructor 2; auto.
    Qed.

    Lemma not_in_not_in':
      forall k a m nodup nodup',
        ~ In (elt:=elt) k {| this := a :: m; NoDup := nodup |} ->
        ~ In (elt:=elt) k {| this := m; NoDup := nodup' |}.
    Proof.
      unfold In, Raw.PX.In, Raw.PX.MapsTo.
      intros k a m nodup nodup' Hnotin Hin.
      apply Hnotin.
      destruct Hin.
      exists x.
      constructor 2; auto.
    Qed.

    Lemma find_hd_eq:
      forall m k v nodup,
        find (elt:=elt) k {| this := (k, v) :: m; NoDup := nodup |} = Some v.
    Proof.
      unfold find. simpl; intros.
      destruct (K.eq_dec k k); auto.
      destruct n; auto.
    Qed.

    Lemma find_hd_neq_none:
      forall k v m
             (Hm: NoDupA (Raw.PX.eqk (elt := elt)) ((k, v) :: m))
             dup,
        find (elt := elt) k {| this := m; NoDup := dup |} = None.
    Proof.
      intros k v m Hm Hm'.

      inversion Hm. subst.
      unfold find.
      unfold Raw.find.
      simpl.
      induction m.

      - reflexivity.

      - destruct a.
        generalize (not_in_neq H1); intros Hneq.
        destruct (K.eq_dec k t).

        + apply Hneq in e0; inversion e0.

        + generalize (not_in_not_in H1); intros Hnotin.

          assert (Hlst: (k, v) :: (t, e) :: m = ((k, v) :: nil) ++ (t, e) :: m).
          { reflexivity. }
          rewrite Hlst in Hm.
          apply SetoidList.NoDupA_split in Hm; simpl in Hm.

          inversion_clear Hm'.

          apply IHm; auto.
    Qed.

    Lemma find_hd_neq_tl:
      forall k k' v m
             (Hm: NoDupA (Raw.PX.eqk (elt:=elt)) ((k, v) :: m))
             dup,
        ~ K.eq k' k ->
        find (elt:=elt) k' {| this := (k, v) :: m; NoDup := Hm |} =
        find (elt:=elt) k' {| this := m; NoDup := dup |}.
    Proof.
      intros k k' v m Hm Hm' Hneq.

      unfold find.
      unfold Raw.find.
      simpl.
      destruct (K.eq_dec k' k).
      - apply Hneq in e; inversion e.
      - reflexivity.
    Qed.

    Lemma find_get:
      forall m k v,
        find k m = Some v ->
        get m k = v.
    Proof.
      intros m k v Hfind.
      unfold get.
      rewrite Hfind.
      auto.
    Qed.

    Lemma not_find_get:
      forall m k,
        find k m = None ->
        get m k = elt_zero.
    Proof.
      intros m k Hfind.
      unfold get.
      rewrite Hfind.
      auto.
    Qed.

    Lemma filter_true_eq:
      forall (T: Type) (l: list T), l = filter (fun _ => true) l.
    Proof.
      induction l; auto.
      simpl. rewrite <- IHl. reflexivity.
    Qed.
    Arguments filter_true_eq [T].

    Lemma not_in_not_find:
      forall k v m nodup,
        ~ InA (Raw.PX.eqk (elt:=elt)) (k, v) m ->
        find k {| this := m; NoDup := nodup |} = None.
    Proof.
      induction m; simpl; auto.

      intros nodup Hnotin.
      inversion nodup; subst.
      destruct a.
      generalize (not_in_not_in Hnotin); intros Hnotin'.
      generalize (IHm H2 Hnotin'); intros Hfind.
      generalize (not_in_neq Hnotin); intros Hneq.
      rewrite (find_hd_neq_tl nodup H2 Hneq).
      auto.
    Qed.

    Lemma not_in_not_find':
      forall (m: t) k,
        ~ In k m -> find k m = None.
    Proof.
      destruct m.
      induction this0; auto.

      intros k Hnotin.
      inversion NoDup0; subst.
      generalize (not_in_not_in' (nodup' := H2) Hnotin); intros Hnotin'.
      generalize (IHthis0 H2 k Hnotin'); intros Hfind.
      destruct a.
      generalize (not_in_neq' Hnotin); intros Hneq.
      rewrite (find_hd_neq_tl NoDup0 H2 Hneq).
      auto.
    Qed.
  End Aux.

  Section Rewrite.
    Lemma emp_zero:
      forall k, get empty k = elt_zero.
    Proof.
      auto.
    Qed.

    Lemma get_eq:
      forall m k k0, K.eq k k0 -> get m k = get m k0.
    Proof.
      intros.
      unfold get, find.
      rewrite (Raw.find_eq m.(NoDup) H).
      auto.
    Qed.

    Lemma get_hd_eq:
      forall m k k' v nodup,
        K.eq k' k ->
        get {| this := (k, v) :: m; NoDup := nodup |} k' = v.
    Proof.
      intros m k k' v nodup Heq.
      unfold get. unfold find. unfold Raw.find. simpl.
      destruct (K.eq_dec k' k); auto.
      apply n in Heq. inversion Heq.
    Qed.

    Lemma get_hd_eq':
      forall m k v nodup,
        get {| this := (k, v) :: m; NoDup := nodup |} k = v.
    Proof.
      intros.
      apply get_hd_eq.
      apply K.eq_refl.
    Qed.

    Lemma get_hd_neq:
      forall m k k' v nodup nodup',
        ~ K.eq k' k ->
        get {| this := (k, v) :: m; NoDup := nodup |} k' =
        get {| this := m; NoDup := nodup' |} k'.
    Proof.
      intros m k k' v nodup nodup' Hneq.
      unfold get. unfold find. unfold Raw.find. simpl.
      destruct (K.eq_dec k' k); auto.
      apply Hneq in e; inversion e.
    Qed.

    Lemma get_upd_eq:
      forall (m: t) (k k': K.t) (v: elt), K.eq k' k -> get (upd m k v) k' = v.
    Proof.
      intros m k k' v Hneq.
      unfold get, upd; rewrite find_add_eq; auto.
    Qed.

    Lemma get_upd_eq':
      forall (m: t) (k: K.t) (v: elt), get (upd m k v) k = v.
    Proof.
      intros. exact (get_upd_eq m v (K.eq_refl k)).
    Qed.

    Lemma get_upd_inc_eq:
      forall (m: t) (k k': K.t) (v: elt),
        K.eq k' k -> get (upd_inc m k v) k' = elt_add (get m k) v.
    Proof.
      intros m k k' v Heq.
      unfold upd_inc.
      rewrite get_upd_eq; auto.
    Qed.

    Lemma get_upd_inc_eq':
      forall (m: t) (k: K.t) (v: elt),
        get (upd_inc m k v) k = elt_add (get m k) v.
    Proof.
      intros m k v. exact (get_upd_inc_eq m v (K.eq_refl k)).
    Qed.

    Lemma get_upd_dec_eq:
      forall (m: t) (k k': K.t) (v: elt),
        K.eq k' k -> get (upd_dec m k v) k' = elt_sub (get m k) v.
    Proof.
      intros m k k' v Heq.
      unfold upd_dec.
      rewrite get_upd_eq; auto.
    Qed.

    Lemma get_upd_dec_eq':
      forall (m: t) (k: K.t) (v: elt),
        get (upd_dec m k v) k = elt_sub (get m k) v.
    Proof.
      intros m k v. exact (get_upd_dec_eq m v (K.eq_refl k)).
    Qed.

    Lemma get_upd_neq:
      forall (m: t) (k k': K.t) (v: elt), ~ K.eq k' k -> get (upd m k v) k' = get m k'.
    Proof.
      intros m k k' v Hneq.
      unfold upd, get.
      rewrite (find_add_neq m v Hneq).
      auto.
    Qed.

    Lemma get_upd_inc_neq:
      forall (m: t) (k k': K.t) (v: elt),
        ~ K.eq k' k -> get (upd_inc m k v) k' = get m k'.
    Proof.
      intros m k k' v Hneq.
      unfold upd_inc.
      destruct (find (elt:=elt) k m);
        apply get_upd_neq; auto.
    Qed.

    Lemma get_upd_dec_neq:
      forall (m: t) (k k': K.t) (v: elt),
        ~ K.eq k' k -> get (upd_dec m k v) k' = get m k'.
    Proof.
      intros m k k' v Hneq.
      unfold upd_dec.
      destruct (find (elt:=elt) k m);
        apply get_upd_neq; auto.
    Qed.
  End Rewrite.

  Section Equality.
    Lemma eq_equal:
      forall (m m': t),
        m = m' -> equal m m'.
    Proof.
      intros.
      subst.
      unfold equal.
      reflexivity.
    Qed.

    Lemma neq_not_equal:
      forall (m m': t), ~ equal m m' -> m <> m'.
    Proof.
      unfold equal.
      intros m m' Hneq Heq.
      apply Hneq.
      rewrite Heq.
      reflexivity.
    Qed.

    Lemma equal_refl:
      forall (m: t), equal m m.
    Proof.
      intros; apply eq_equal; auto.
    Qed.

    Lemma equal_sym:
      forall (m m': t), equal m m' -> equal m' m.
    Proof.
      unfold equal; auto.
    Qed.

    Lemma equal_trans:
      forall m m' m'', equal m m' -> equal m' m'' -> equal m m''.
    Proof.
      unfold equal; intros.
      generalize (H k); clear H; intros H; rewrite H.
      generalize (H0 k); clear H0; intros H0; rewrite H0.
      reflexivity.
    Qed.

    Lemma get_equal:
      forall m m' k k',
        equal m m' ->
        K.eq k k' ->
        get m k = get m' k'.
    Proof.
      intros m m' k k' Hmeq Hkeq.
      apply (get_eq m) in Hkeq.
      rewrite Hkeq.
      auto.
    Qed.

    Lemma upd_equal:
      forall m m' k v, equal m m' -> equal (upd m k v) (upd m' k v).
    Proof.
      unfold equal.
      intros m m' k v Heq k'.
      destruct (K.eq_dec k' k).
      - repeat rewrite get_upd_eq; auto.
      - repeat rewrite get_upd_neq; auto.
    Qed.

    Lemma upd_upd_equal:
      forall (m m': t) (k k': K.t) (v v': elt),
        equal m m' ->
        K.eq k k' ->
        equal (upd (upd m k v) k' v')
              (upd m' k' v').
    Proof.
      unfold equal.
      intros m m' k k' v v' Hmeq Hkeq k0.

      case (K.eq_dec k0 k').
      - (* k = k0 *)
        intros Heq0.
        repeat rewrite (get_upd_eq _ _ Heq0).
        reflexivity.

      - (* k <> k0 *)
        intros Hneq0.
        assert (~ K.eq k0 k).
        { intros Heq0. apply Hneq0. eapply K.eq_trans; eauto. }
        repeat rewrite (get_upd_neq _ _ Hneq0).
        rewrite (get_upd_neq _ _ H).
        auto.
    Qed.

    Lemma upd_get_equal:
      forall (m m': t) (k k': K.t),
        equal m m' ->
        K.eq k k' ->
        equal m (upd m' k (get m' k')).
    Proof.
      unfold equal.
      intros m m' k k' Hmeq Hkeq k0.

      case (K.eq_dec k k0).
      - (* k0 = k *)
        intros Heq0.
        rewrite (get_upd_eq m' (get m' k')); auto.
        apply K.eq_sym in Hkeq.
        apply (K.eq_trans Hkeq) in Heq0.
        rewrite (Hmeq k0).
        apply get_eq; auto.

      - (* k0 <> k *)
        intros Hneq.
        rewrite get_upd_neq; auto.
    Qed.

    Lemma upd_upd_swap_equal:
      forall (m m': t) (k k': K.t) (v v': elt),
        equal m m' ->
        ~ K.eq k k' ->
        equal (upd (upd m k v) k' v')
              (upd (upd m' k' v') k v).
    Proof.
      unfold equal.
      intros m m' k k' v v' Hmeq Hneq k0.
      apply not_eq_sym in Hneq.

      case (K.eq_dec k0 k); case (K.eq_dec k0 k').
      - (* k = k' = k0 *)
        intros Heq Heq'.
        apply K.eq_sym in Heq.
        apply (K.eq_trans Heq) in Heq'.
        apply Hneq in Heq'; inversion Heq'.

      - (* k = k0 /\ k' <> k0 *)
        intros Hneq0' Heq0.
        repeat (try rewrite (get_upd_eq _ _ Heq0);
                try rewrite (get_upd_neq _ _ Hneq0');
                auto).

      - (* k <> k0 /\ k' = k0 *)
        intros Heq0 Hneq0'.
        repeat (try rewrite (get_upd_eq _ _ Heq0);
                try rewrite (get_upd_neq _ _ Hneq0');
                auto).

      - (* k <> k0 /\ k' <> k0 *)
        intros Hneq0' Hneq0''.
        repeat (try rewrite (get_upd_neq _ _ Hneq0');
                try rewrite (get_upd_neq _ _ Hneq0'');
                auto).
    Qed.

    Lemma upd_inc_equal:
      forall m m' k k' v,
        equal m m' ->
        K.eq k k' ->
        equal (upd_inc m k v)
              (upd_inc m' k' v).
    Proof.
      intros m m' k k' v Hmeq Hkeq k0.
      destruct (K.eq_dec k0 k).

      - (* k0 = k *)
        rewrite get_upd_inc_eq; auto.
        destruct (K.eq_dec k0 k').
        + (* k0 = k' *)
          rewrite get_upd_inc_eq; auto.
          rewrite (get_equal Hmeq Hkeq); auto.
        + (* k0 <> k *)
          generalize (K.eq_trans e Hkeq); intros Htrans.
          apply n in Htrans; inversion Htrans.

      - (* k0 <> k *)
        rewrite get_upd_inc_neq; auto.
        destruct (K.eq_dec k0 k').
        + (* k0 = k' *)
          generalize (K.eq_sym (K.eq_trans Hkeq (K.eq_sym e))); intros Htrans.
          apply n in Htrans; inversion Htrans.
        + (* k0 <> k' *)
          rewrite get_upd_inc_neq; auto.
    Qed.

    Lemma upd_dec_equal:
      forall m m' k k' v,
        equal m m' ->
        K.eq k k' ->
        equal (upd_dec m k v)
              (upd_dec m' k' v).
    Proof.
      intros m m' k k' v Hmeq Hkeq k0.
      destruct (K.eq_dec k0 k).

      - (* k0 = k *)
        rewrite get_upd_dec_eq; auto.
        destruct (K.eq_dec k0 k').
        + (* k0 = k' *)
          rewrite get_upd_dec_eq; auto.
          rewrite (get_equal Hmeq Hkeq); auto.
        + (* k0 <> k *)
          generalize (K.eq_trans e Hkeq); intros Htrans.
          apply n in Htrans; inversion Htrans.

      - (* k0 <> k *)
        rewrite get_upd_dec_neq; auto.
        destruct (K.eq_dec k0 k').
        + (* k0 = k' *)
          generalize (K.eq_sym (K.eq_trans Hkeq (K.eq_sym e))); intros Htrans.
          apply n in Htrans; inversion Htrans.
        + (* k0 <> k' *)
          rewrite get_upd_dec_neq; auto.
    Qed.

    Lemma upd_inc_unfold_equal:
      forall m m' k k' v,
        equal m m' ->
        K.eq k k' ->
        equal (upd_inc m k v)
              (upd m' k' (elt_add (get m' k') v)).
    Proof.
      intros m m' k k' v Hmeq Hkeq.
      apply equal_trans with (m' := upd_inc m' k' v); auto.
      - apply upd_inc_equal; auto.
      - intros k0.
        destruct (K.eq_dec k0 k').
        + (* k0 = k' *)
          erewrite get_upd_eq; eauto.
          erewrite get_upd_inc_eq; eauto.
        + (* k0 <> k' *)
          erewrite get_upd_neq; eauto.
          erewrite get_upd_inc_neq; eauto.
    Qed.

    Lemma upd_dec_unfold_equal:
      forall m m' k k' v,
        equal m m' ->
        K.eq k k' ->
        equal (upd_dec m k v)
              (upd m' k' (elt_sub (get m' k') v)).
    Proof.
      intros m m' k k' v Hmeq Hkeq.
      apply equal_trans with (m' := upd_dec m' k' v); auto.
      - apply upd_dec_equal; auto.
      - intros k0.
        destruct (K.eq_dec k0 k').
        + (* k0 = k' *)
          erewrite get_upd_eq; eauto.
          erewrite get_upd_dec_eq; eauto.
        + (* k0 <> k' *)
          erewrite get_upd_neq; eauto.
          erewrite get_upd_dec_neq; eauto.
    Qed.

    Lemma upd_upd_inc_equal:
      forall (m m': t) (k k': K.t) (v v': elt),
        equal m m' ->
        K.eq k k' ->
        equal (upd (upd_inc m k v) k' v')
              (upd m' k' v').
    Proof.
      intros m m' k k' v v' Hmeq Hkeq.
      apply equal_trans with
          (m' := upd (upd m k (elt_add (get m k) v)) k' v').
      - apply upd_equal.
        apply upd_inc_unfold_equal; auto.
        apply equal_refl.
      - apply upd_upd_equal; auto.
    Qed.

    Lemma upd_upd_dec_equal:
      forall (m m': t) (k k': K.t) (v v': elt),
        equal m m' ->
        K.eq k k' ->
        equal (upd (upd_dec m k v) k' v')
              (upd m' k' v').
    Proof.
      intros m m' k k' v v' Hmeq Hkeq.
      apply equal_trans with
          (m' := upd (upd m k (elt_sub (get m k) v)) k' v').
      - apply upd_equal.
        apply upd_dec_unfold_equal; auto.
        apply equal_refl.
      - apply upd_upd_equal; auto.
    Qed.
  End Equality.

  Section Sum.
    Lemma sum_empty:
      sum empty = elt_zero.
    Proof.
      auto.
    Qed.

    Lemma sum_empty':
      elt_eq (sum empty) elt_zero.
    Proof.
      rewrite sum_empty.
      apply elt_eq_refl.
    Qed.

    Lemma sum_cons:
      forall m k v nodup nodup',
        elt_eq (sum {| this := (k, v) :: m; NoDup := nodup |})
               (elt_add_raw (sum {| this := m; NoDup := nodup' |}) v).
    Proof.
      unfold sum.
      unfold map.elements.
      unfold map.Raw.elements.
      intros. simpl.
      apply elt_add_raw_comm.
    Qed.

    Lemma sum_filter_empty:
      forall f,
        sum_filter empty f = elt_zero.
    Proof.
      intros f.
      unfold sum_filter.
      simpl.
      reflexivity.
    Qed.

    Lemma sum_filter_true:
      forall (m: t),
        sum_filter m (fun _ => true) = sum m.
    Proof.
      intros.
      unfold sum, sum_filter.
      fold key.
      rewrite <- (filter_true_eq (elements (elt:=elt) m)).
      reflexivity.
    Qed.

    Lemma sum_filter_hd_true:
      forall m k v nodup nodup' f,
        f (k, v) = true ->
        sum_filter {| this := (k, v) :: m; NoDup := nodup |} f =
        elt_add_raw v (sum_filter {| this := m; NoDup := nodup' |} f).
    Proof.
      intros m k v nodup nodup' f Hf.
      unfold sum_filter. simpl.
      rewrite Hf; simpl.
      reflexivity.
    Qed.

    Lemma sum_filter_hd_false:
      forall m k v nodup nodup' f,
        f (k, v) = false ->
        sum_filter {| this := (k, v) :: m; NoDup := nodup |} f =
        sum_filter {| this := m; NoDup := nodup' |} f.
    Proof.
      intros m k v nodup nodup' f Hf.
      unfold sum_filter. simpl.
      rewrite Hf; simpl.
      reflexivity.
    Qed.

    Lemma sum_filter_f_eq:
      forall f g,
        (forall k, f k = g k) ->
        forall m,
          sum_filter m f = sum_filter m g.
    Proof.
      destruct m.
      induction this0; unfold sum_filter; simpl; auto.
      rewrite (H a).
      destruct (g a).
      - destruct a as [k' v'].
        simpl.
        inversion NoDup0; subst.
        generalize (IHthis0 H3); clear IHthis0;
          unfold sum_filter; simpl; intros IHthis0.
        rewrite IHthis0.
        reflexivity.
      - inversion NoDup0; subst.
        generalize (IHthis0 H3); clear IHthis0;
          unfold sum_filter; simpl; intros IHthis0.
        auto.
    Qed.

    Lemma sum_equal:
      forall m m',
        equal m m' ->
        sum m = sum m'.
    Proof.
    Admitted.

    Lemma sum_filter_equal:
      forall f m m',
        equal m m' ->
        sum_filter m f = sum_filter m' f.
    Proof.
    Admitted.
  End Sum.

  Section Filter.
    Lemma filter_empty:
      forall f,
        map_filter empty f = nil.
    Proof.
      auto.
    Qed.

    Lemma filter_hd_true:
      forall f e this nodup nodup',
        f e = true ->
        map_filter {| this := e :: this; NoDup := nodup |} f =
        e :: map_filter {| this := this; NoDup := nodup' |} f.
    Proof.
      intros f e this nodup nodup' Hf_true.
      unfold map_filter; simpl.
      rewrite Hf_true; auto.
    Qed.

    Lemma filter_hd_false:
      forall f e this nodup nodup',
        f e = false ->
        map_filter {| this := e :: this; NoDup := nodup |} f =
        map_filter {| this := this; NoDup := nodup' |} f.
    Proof.
      intros f e this nodup nodup' Hf_false.
      unfold map_filter; simpl.
      rewrite Hf_false; auto.
    Qed.

    Lemma filter_not_in:
      forall (m: t) e f,
        ~ InA (Raw.PX.eqk (elt:=elt)) e (this m) ->
        ~ InA (Raw.PX.eqk (elt:=elt)) e (map_filter m f).
    Proof.
      intros m e f Hnot_in.
      destruct m as [this nodup].
      induction this; simpl; auto.

      inversion nodup; subst; simpl in *.
      case_eq (f a); intros Hf; simpl in *.

      - rewrite (filter_hd_true nodup H2 Hf).
        intros Hin; apply InA_cons in Hin; destruct Hin.
        + apply Hnot_in. constructor 1; auto.
        + destruct a as [k v].
          destruct e as [k' v'].
          generalize (not_in_not_in Hnot_in); intros Hnot_in'.
          generalize (IHthis H2 Hnot_in'); clear Hnot_in'; intros Hnot_in'.
          apply Hnot_in'; auto.

      - rewrite (filter_hd_false nodup H2 Hf).
        destruct a as [k v].
        destruct e as [k' v'].
        generalize (not_in_not_in Hnot_in); intros Hnot_in'.
        apply IHthis; auto.
    Qed.

    Lemma filter_nodup:
      forall (m: t) f,
        NoDupA (Raw.PX.eqk (elt:=elt)) (map_filter m f).
    Proof.
      intros m f.
      destruct m as [this nodup].
      induction this; simpl; auto.

      inversion nodup; subst.
      case_eq (f a); intros Hf.
      - rewrite (filter_hd_true nodup H2 Hf).
        constructor; auto.
        apply filter_not_in; auto.
      - rewrite (filter_hd_false nodup H2 Hf).
        apply IHthis; auto.
    Qed.

    Lemma filter_true_in:
      forall (m: t) e f,
        InA (Raw.PX.eqke (elt:=elt)) e (this m) ->
        (forall e0 e1, K.eq (fst e0) (fst e1) -> snd e0 = snd e1 -> f e0 = f e1) ->
        f e = true ->
        InA (Raw.PX.eqke (elt:=elt)) e (map_filter m f).
    Proof.
      intros m e f Hin Hf Hfe_true.
      destruct m as [this nodup].
      induction this; simpl; auto.

      inversion nodup; subst; simpl in *.
      destruct a as [k v].
      destruct e as [k' v'].
      destruct (K.eq_dec k' k).

      - (* k' = k *)
        destruct (elt_eq_dec v' v).
        + (* v' = v *)
          generalize (Hf (k', v') (k, v) e e0); intros Hfkv.
          rewrite Hfe_true in Hfkv; apply eq_sym in Hfkv.
          rewrite (filter_hd_true nodup H2 Hfkv).
          constructor 1; auto.

        + (* v' <> v *)
          case_eq (f (k, v)); intros Hfkv.
          * rewrite (filter_hd_true nodup H2 Hfkv).
            constructor 2; auto.
            apply IHthis; auto.
            apply InA_cons in Hin;
              unfold Raw.PX.eqke in Hin;
              simpl in Hin;
              destruct Hin; auto.
            destruct H; contradiction.
          * rewrite (filter_hd_false nodup H2 Hfkv).
            apply IHthis.
            apply InA_cons in Hin;
              unfold Raw.PX.eqke in Hin;
              simpl in Hin;
              destruct Hin; auto.
            destruct H; contradiction.

      - (* k' <> k *)
        case_eq (f (k, v)); intros Hfkv.

        + rewrite (filter_hd_true nodup H2 Hfkv).
          constructor 2; auto.
          apply IHthis; auto.
          apply InA_cons in Hin;
            unfold Raw.PX.eqke in Hin;
            simpl in Hin;
            destruct Hin; auto.
          destruct H; contradiction.

        + rewrite (filter_hd_false nodup H2 Hfkv).
          apply IHthis.
          apply InA_cons in Hin;
            unfold Raw.PX.eqke in Hin;
            simpl in Hin;
            destruct Hin; auto.
          destruct H; contradiction.
    Qed.

    Lemma filter_false_not_in:
      forall (m: t) e f,
        InA (Raw.PX.eqk (elt:=elt)) e (this m) ->
        f e = false ->
        ~ InA (Raw.PX.eqk (elt:=elt)) e (map_filter m f).
    Proof.
    Admitted.

    Lemma filter_length_equal:
      forall m m' f,
        equal m m' ->
        length (map_filter m f) = length (map_filter m' f).
    Proof.
    Admitted.

    Lemma filter_length_upd_false_true:
      forall m m' f k,
        f (k, get m k) = false ->
        f (k, get m' k) = true ->
        (forall k', ~ K.eq k' k -> f (k', get m k') = f (k', get m' k')) ->
        length (map_filter m' f) = length (map_filter m f) + 1.
    Proof.
    Admitted.

    Lemma filter_length_upd_true_false:
      forall m m' f k,
        f (k, get m k) = true ->
        f (k, get m' k) = false ->
        (forall k', ~ K.eq k' k -> f (k', get m k') = f (k', get m' k')) ->
        length (map_filter m' f) = length (map_filter m f) - 1.
    Proof.
    Admitted.

    Lemma filter_length_f_equal:
      forall m m' f,
        (forall k, f (k, get m k) = f (k, get m' k)) ->
        length (map_filter m' f) = length (map_filter m f).
    Proof.
    Admitted.

    Lemma filter_length_exist_nonzero:
      forall m f,
        (exists k, f (k, get m k) = true) ->
        length (map_filter m f) > 0.
    Proof.
    Admitted.
  End Filter.

  Hint Resolve
       (* Aux *)
       not_eq_sym
       find_add_eq find_add_neq
       not_in_neq not_in_neq' not_in_not_in not_in_not_in'
       find_hd_eq find_hd_neq_none find_hd_neq_tl
       find_get not_find_get
       filter_true_eq
       not_in_not_find not_in_not_find'
       (* Rewrite *)
       emp_zero
       get_eq
       get_hd_eq get_hd_eq' get_hd_neq
       get_upd_eq get_upd_eq'
       get_upd_inc_eq get_upd_inc_eq'
       get_upd_dec_eq get_upd_dec_eq'
       get_upd_neq
       get_upd_inc_neq get_upd_dec_neq
       (* Equality *)
       eq_equal neq_not_equal
       equal_refl equal_sym equal_trans
       get_equal upd_equal
       upd_upd_equal upd_get_equal upd_upd_inc_equal upd_upd_dec_equal
       upd_upd_swap_equal
       upd_inc_equal upd_dec_equal
       upd_inc_unfold_equal upd_dec_unfold_equal
       (* Sum *)
       sum_empty sum_empty' sum_cons
       sum_filter_equal
       sum_filter_true sum_filter_hd_true sum_filter_hd_false
       sum_equal sum_filter_equal
       (* filter *)
       filter_empty filter_nodup
       filter_hd_true filter_hd_false filter_not_in
       filter_true_in filter_false_not_in
       filter_length_equal
       filter_length_upd_false_true
       filter_length_upd_true_false
       filter_length_f_equal
       filter_length_exist_nonzero.

  Hint Rewrite
       emp_zero
       get_hd_eq' get_upd_eq' get_upd_inc_eq' get_upd_dec_eq'
       sum_empty
       sum_filter_true
    : mapping_rewrite.

  Ltac msimpl :=
    match goal with
    (* emp_zero *)
    | [ |- context [ get empty ?k ]
      ] =>
      rewrite (emp_zero k);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_hd_eq *)
    | [ H: K.eq ?k' ?k
        |- context [ get {| this := (?k, ?v) :: ?m; NoDup := ?nodup |} ?k' ]
      ] =>
      rewrite (get_hd_eq nodup H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: K.eq ?k ?k'
        |- context [ get {| this := (?k, ?v) :: ?m; NoDup := ?nodup |} ?k' ]
      ] =>
      rewrite (get_hd_eq nodup (K.eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ |- context [ get {| this := (?k, ?v) :: ?m; NoDup := ?nodup |} ?k ]
      ] =>
      rewrite (get_hd_eq' nodup);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_eq *)
    | [ H: K.eq ?k' ?k
        |- context [ get (upd ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_eq m v H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: K.eq ?k ?k'
        |- context [ get (upd ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_eq m v (K.eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_eq' *)
    | [ |- context [ get (upd ?m ?k ?v) ?k ]
      ] =>
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_inc_eq *)
    | [ H: K.eq ?k' ?k
        |- context [ get (upd_inc ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_inc_eq m v H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: K.eq ?k ?k'
        |- context [ get (upd_inc ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_inc_eq m v (K.eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_inc_eq' *)
    | [ |- context [ get (upd_inc ?m ?k ?v) ?k ]
      ] =>
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_dec_eq *)
    | [ H: K.eq ?k' ?k
        |- context [ get (upd_dec ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_dec_eq m v H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: K.eq ?k ?k'
        |- context [ get (upd_dec ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_dec_eq m v (K.eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_dec_eq' *)
    | [ |- context [ get (upd_dec ?m ?k ?v) ?k ]
      ] =>
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_neq *)
    | [ H: ~ K.eq ?k' ?k
        |- context [ get (upd ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_neq m v H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: ~ K.eq ?k ?k'
        |- context [ get (upd ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_neq m v (not_eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_inc_neq *)
    | [ H: ~ K.eq ?k' ?k
        |- context [ get (upd_inc ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_inc_neq m v H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: ~ K.eq ?k ?k'
        |- context [ get (upd_inc ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_inc_neq m v (not_eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_dec_neq *)
    | [ H: ~ K.eq ?k' ?k
        |- context [ get (upd_dec ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_dec_neq m v H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: ~ K.eq ?k ?k'
        |- context [ get (upd_dec ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_dec_neq m v (not_eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | _ => idtac
    end.

  Ltac msimpl_in H :=
    let T := type of H in
    generalize H; clear H; msimpl; intros H.
End Mapping.
