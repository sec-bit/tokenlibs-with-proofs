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
        Coq.FSets.FMapList
        Coq.Structures.OrderedType
        Coq.Structures.OrderedTypeEx.


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

  Axiom elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.

  Axiom elt_add_raw_comm:
    forall x y, (elt_add_raw x y) = (elt_add_raw y x).

  Axiom elt_zero_add_raw:
    forall x, elt_add_raw elt_zero x = x.

  Axiom elt_zero_add_raw':
    forall x, elt_add_raw x elt_zero = x.

  Axiom elt_zero_add:
    forall x, elt_add elt_zero x = x.

  Axiom elt_zero_add':
    forall x, elt_add x elt_zero = x.
End ElemType.

Module Mapping (K: OrderedType) (Elt: ElemType).
  Module Import map := FMapList.Make(K).
  Module Import et := Elt.

  Module MK:=OrderedTypeFacts(K).
  Import MK.

  Notation t := (map.t elt).
  Notation empty := (map.empty elt).

  Definition get (m: t) (k: K.t) : elt :=
    match find k m with
    | Some v => v
    | None => elt_zero
    end.

  Fixpoint eq_list (m m' : list (K.t * elt)) : Prop :=
    match m, m' with
    | nil, nil => True
    | (x,e)::l, (x',e')::l' =>
      match K.compare x x' with
      | EQ _ => e = e' /\ eq_list l l'
      | _ => False
      end
    | _, _ => False
    end.

  Definition equal m m' := eq_list m.(this) m'.(this).

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
    Lemma kv_eq_dec:
      forall (e e': K.t * elt), { Raw.PX.eqke e e' } + { ~ Raw.PX.eqke e e' }.
    Proof.
      intros [k v] [k' v'].
      destruct (K.eq_dec k k'); destruct (elt_eq_dec v v');
        unfold Raw.PX.eqke;
        simpl; tauto.
    Qed.

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

    Lemma find_upd_eq:
      forall (m: t) (k k': K.t) (v: elt),
        K.eq k' k -> find k (upd m k' v) = Some v.
    Proof.
      intros.
      apply find_1; apply add_1; auto.
    Qed.

    Lemma find_add_lt:
      forall (m: t) (k k': K.t) (v: elt),
        K.lt k' k -> find k' (add k v m) = find k' m.
    Proof.
      intros.
      case_eq (find k' m).

      intros e Hfind.
      apply find_2 in Hfind.
      apply find_1.
      apply add_2; auto.

      unfold find, Raw.find.
      destruct m. simpl.
      generalize this0 sorted0 k k' v H; clear this0 sorted0 k k' v H.
      induction this0.

      intros. simpl.
      destruct (K.compare k' k); try order; auto.

      intros.
      simpl.
      destruct a.
      destruct (K.compare k t); destruct (K.compare k' k); try order; auto.
      generalize H0.
      destruct (K.compare k' t); try order; auto.
      apply IHthis0; auto.
      inversion sorted0; auto.
    Qed.

    Lemma find_add_gt:
      forall (m: t) (k k': K.t) (v: elt),
        K.lt k k' -> find k' (add k v m) = find k' m.
    Proof.
      intros.
      case_eq (find k' m).

      intros e Hfind.
      apply find_2 in Hfind.
      apply find_1.
      apply add_2; auto.

      unfold find, Raw.find.
      destruct m. simpl.
      generalize this0 sorted0 k k' v H; clear this0 sorted0 k k' v H.
      induction this0.

      intros. simpl.
      destruct (K.compare k' k); try order; auto.

      intros.
      simpl.
      destruct a.
      destruct (K.compare k t); destruct (K.compare k' k); try order; auto.
      generalize H0.
      destruct (K.compare k' t); try order; auto.
      destruct (K.compare k' t); auto.
      apply IHthis0; auto.
      inversion sorted0; auto.
    Qed.

    Lemma find_add_neq:
      forall (m: t) (k k': K.t) (v: elt),
        ~ K.eq k' k -> find k' (add k v m) = find k' m.
    Proof.
      intros.
      destruct (K.compare k' k).
      apply find_add_lt; auto.
      tauto.
      apply find_add_gt; auto.
    Qed.

    Lemma find_upd_neq:
      forall (m: t) (k k': K.t) (v: elt),
        ~ K.eq k' k -> find k' (upd m k v) = find k' m.
    Proof.
      intros.
      destruct (K.compare k' k).
      apply find_add_lt; auto.
      tauto.
      apply find_add_gt; auto.
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
      forall k k' v' m sorted,
        ~ In (elt:=elt) k {| this := (k', v') :: m; sorted := sorted |} ->
        ~ K.eq k k'.
    Proof.
      unfold In, Raw.PX.In, Raw.PX.MapsTo.
      intros k k' v' m sorted Hnotin Heq.
      apply Hnotin.
      exists v'.
      constructor 1; auto.
    Qed.

    Lemma not_InA_not_InA_tl:
      forall A (eqA: A -> A -> Prop) e e' m,
        ~ InA eqA e' (e :: m) ->
        ~ InA eqA e' m.
    Proof.
      intros k v k' v' m Hnot_in Hin.
      apply Hnot_in.
      constructor 2; auto.
    Qed.

    Lemma not_In_not_In_tl:
      forall k a m sorted sorted',
        ~ In (elt:=elt) k {| this := a :: m; sorted := sorted |} ->
        ~ In (elt:=elt) k {| this := m; sorted := sorted' |}.
    Proof.
      unfold In, Raw.PX.In, Raw.PX.MapsTo.
      intros k a m sorted sorted' Hnotin Hin.
      apply Hnotin.
      destruct Hin.
      exists x.
      constructor 2; auto.
    Qed.

    Lemma find_hd_eq:
      forall m k v sorted,
        find (elt:=elt) k {| this := (k, v) :: m; sorted := sorted |} = Some v.
    Proof.
      unfold find. simpl; intros.
      destruct (K.compare k k); try order; auto.
    Qed.

    Lemma find_hd_lt_none:
      forall k v m
             (Hm: Sorted (Raw.PX.ltk (elt := elt)) ((k, v) :: m))
             sorted,
        find (elt := elt) k {| this := m; sorted := sorted |} = None.
    Proof.
      intros k v m Hm Hm'.

      unfold find.
      unfold Raw.find.
      simpl.
      induction m; auto.
      destruct a.
      inversion Hm.
      generalize (HdRel_inv H2).
      compute.
      destruct (K.compare k t); try order; auto.
    Qed.

    Lemma find_hd_lt_none':
      forall k k' v m
             (Hm: Sorted (Raw.PX.ltk (elt := elt)) ((k, v) :: m))
             sorted,
        K.eq k' k ->
        find (elt := elt) k' {| this := m; sorted := sorted |} = None.
    Proof.
      intros k k' v m Hm Hm' Heq.

      unfold find.
      unfold Raw.find.
      simpl.
      induction m; auto.
      destruct a.
      inversion Hm.
      generalize (HdRel_inv H2).
      compute.
      destruct (K.compare k' t); try order; auto.
    Qed.

    Lemma find_hd_lt_none'':
      forall k k' v m
             (Hm: Sorted (Raw.PX.ltk (elt := elt)) ((k, v) :: m))
             sorted,
        K.lt k' k ->
        find (elt := elt) k' {| this := m; sorted := sorted |} = None.
    Proof.
      intros k k' v m Hm Hm' Heq.

      unfold find; unfold Raw.find; simpl.
      induction m; auto.
      destruct a.
      inversion Hm.
      generalize (HdRel_inv H2).
      compute.
      destruct (K.compare k' t); try order; auto.
    Qed.

    Lemma sorted_lt_sorted:
      forall k k' v v' m,
        K.lt k' k ->
        Sorted (Raw.PX.ltk (elt:=elt)) ((k, v) :: m) ->
        Sorted (Raw.PX.ltk (elt:=elt)) ((k', v') :: m).
    Proof.
      intros k k' v v' m Hlt Hsorted.
      induction m; inversion Hsorted.
      apply Sorted_cons.
      apply Sorted_nil.
      apply HdRel_nil.
      apply Sorted_cons; auto.
      apply HdRel_cons.
      destruct a.
      inversion H2.
      generalize H4.
      compute.
      order.
    Qed.

    Lemma find_hd_lt_tl:
      forall k k' v m
             (Hm: Sorted (Raw.PX.ltk (elt:=elt)) ((k, v) :: m))
             sorted,
        K.lt k' k ->
        find (elt:=elt) k' {| this := (k, v) :: m; sorted := Hm |} =
        find (elt:=elt) k' {| this := m; sorted := sorted |}.
    Proof.
      intros k k' v m Hm Hm' Hlt.
      unfold find.
      unfold Raw.find.
      simpl.
      destruct (K.compare k' k); try order; auto.
      apply eq_sym.
      inversion Hm.
      apply (find_hd_lt_none (sorted_lt_sorted v Hlt Hm) Hm').
    Qed.

    Lemma find_hd_gt_tl:
      forall k k' v m
             (Hm: Sorted (Raw.PX.ltk (elt:=elt)) ((k, v) :: m))
             sorted,
        K.lt k k' ->
        find (elt:=elt) k' {| this := (k, v) :: m; sorted := Hm |} =
        find (elt:=elt) k' {| this := m; sorted := sorted |}.
    Proof.
      intros k k' v m Hm Hm' Hgt.
      unfold find.
      unfold Raw.find.
      simpl.
      destruct (K.compare k' k); try order; auto.
    Qed.

    Lemma find_hd_neq_tl:
      forall k k' v m
             (Hm: Sorted (Raw.PX.ltk (elt:=elt)) ((k, v) :: m))
             sorted,
        ~ K.eq k' k ->
        find (elt:=elt) k' {| this := (k, v) :: m; sorted := Hm |} =
        find (elt:=elt) k' {| this := m; sorted := sorted |}.
    Proof.
      intros.
      destruct (K.compare k' k).
      apply find_hd_lt_tl; auto.
      tauto.
      apply find_hd_gt_tl; auto.
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

    Lemma find_eq:
      forall (k k': K.t) (m: t),
        K.eq k k' ->
        find k m = find k' m.
    Proof.
      intros k k' m Hkeq.
      destruct m as [this sorted].
      unfold find; unfold Raw.find.
      induction this.
      compute;auto.
      simpl.
      destruct a.
      destruct (K.compare k t); destruct (K.compare k' t); try order; auto.
      simpl in IHthis.
      inversion sorted.
      apply IHthis; auto.
    Qed.

    Lemma sorted_cons_lt:
      forall k v k' v' m,
        Sorted (Raw.PX.ltk (elt:=elt)) ((k, v) :: (k', v') :: m) ->
        K.lt k k'.
    Proof.
      intros.
      inversion H.
      generalize (HdRel_inv H3).
      compute; auto.
    Qed.

    Lemma HdRel_trans:
      forall k v k' v' m,
        K.lt k k' ->
        HdRel (Raw.PX.ltk (elt:=elt)) (k', v') m ->
        HdRel (Raw.PX.ltk (elt:=elt)) (k, v) m.
    Proof.
      intros.
      induction m.
      apply HdRel_nil.
      apply HdRel_cons.
      destruct a.
      inversion H0.
      generalize H2; compute.
      order.
    Qed.

    Lemma sorted_cons_sorted:
      forall k v k' v' m,
        Sorted (Raw.PX.ltk (elt:=elt)) ((k, v) :: (k', v') :: m) ->
        Sorted (Raw.PX.ltk (elt:=elt)) ((k, v) :: m).
    Proof.
      intros.
      inversion H.
      inversion H2.
      apply Sorted_cons; auto.
      generalize (HdRel_inv H3); intro Hlt; compute in Hlt.
      generalize (HdRel_trans v Hlt H7); auto.
    Qed.

    Lemma sorted_in_lt:
      forall t e k v m,
        Sorted (Raw.PX.ltk (elt:=elt)) ((t, e)::m) ->
        InA (Raw.PX.eqke (elt:=elt)) (k, v) m ->
        K.lt t k.
    Proof.
      intros.
      induction m.
      inversion H0.
      destruct a.
      inversion H0.
      compute in H2; destruct H2.
      generalize (sorted_cons_lt H); order.
      apply (IHm (sorted_cons_sorted H)); auto.
    Qed.

    Lemma in_find:
      forall m k v sorted,
        InA (Raw.PX.eqke (elt:=elt)) (k, v) m ->
        find k {| this := m; sorted := sorted |} = Some v.
    Proof.
      intros.
      induction m.
      inversion H.
      unfold find; unfold Raw.find; destruct a; simpl.
      inversion H.
      compute in H1; destruct H1.
      destruct (K.compare k t); try order; auto.
      rewrite H3; auto.
      inversion sorted0.
      inversion H.
      compute in H8; destruct H8.
      destruct (K.compare k t); try order; auto.
      rewrite H10; auto.
      destruct (K.compare k t).
      generalize (sorted_in_lt sorted0 H1); order.
      generalize (sorted_in_lt sorted0 H1); order.
      apply (IHm H5 H8).
    Qed.

    Lemma not_in_not_find:
      forall k v m sorted,
        ~ InA (Raw.PX.eqk (elt:=elt)) (k, v) m ->
        find k {| this := m; sorted := sorted |} = None.
    Proof.
      induction m; simpl; auto.

      intros sorted Hnotin.
      inversion sorted; subst.
      destruct a.
      generalize (not_InA_not_InA_tl Hnotin); intros Hnotin'.
      generalize (IHm H1 Hnotin'); intros Hfind.
      generalize (not_in_neq Hnotin); intros Hneq.
      rewrite (find_hd_neq_tl sorted H1 Hneq).
      auto.
    Qed.

    Lemma not_in_not_find':
      forall (m: t) k,
        ~ In k m -> find k m = None.
    Proof.
      destruct m.
      induction this0; auto.

      intros k Hnotin.
      inversion sorted0; subst.
      generalize (not_In_not_In_tl (sorted' := H1) Hnotin); intros Hnotin'.
      generalize (IHthis0 H1 k Hnotin'); intros Hfind.
      destruct a.
      generalize (not_in_neq' Hnotin); intros Hneq.
      rewrite (find_hd_neq_tl sorted0 H1 Hneq).
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
      unfold get.
      rewrite (find_eq m H).
      tauto.
    Qed.

    Lemma get_hd_eq:
      forall m k k' v sorted,
        K.eq k' k ->
        get {| this := (k, v) :: m; sorted := sorted |} k' = v.
    Proof.
      intros m k k' v sorted Heq.
      unfold get.
      unfold find. unfold Raw.find. simpl.
      destruct (K.compare k' k); try order; auto.
    Qed.

    Lemma get_hd_eq':
      forall m k v sorted,
        get {| this := (k, v) :: m; sorted := sorted |} k = v.
    Proof.
      intros.
      apply get_hd_eq.
      apply K.eq_refl.
    Qed.

    Lemma get_hd_neq:
      forall m k k' v sorted sorted',
        ~ K.eq k' k ->
        get {| this := (k, v) :: m; sorted := sorted |} k' =
        get {| this := m; sorted := sorted' |} k'.
    Proof.
      intros m k k' v sorted sorted' Hneq.
      unfold get. unfold find. unfold Raw.find. simpl.
      destruct (K.compare k' k); try order; auto.
      generalize (find_hd_lt_none (sorted_lt_sorted v l sorted) sorted').
      unfold find. unfold Raw.find. simpl.
      intro Heq; rewrite Heq; tauto.
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
      unfold equal; unfold map.equal; unfold Raw.equal.
      destruct m'.
      induction this0; simpl; auto.
      destruct a; destruct (K.compare t t); try order; auto.
      split; auto.
      inversion sorted0.
      apply (IHthis0 H1).
    Qed.

    Lemma neq_not_equal:
      forall (m m': t), ~ equal m m' -> m <> m'.
    Proof.
      unfold equal.
      intros m m' Hneq Heq.
      apply Hneq.
      rewrite Heq.
      apply eq_equal; auto.
    Qed.

    Lemma equal_refl:
      forall (m: t), equal m m.
    Proof.
      intros; apply eq_equal; auto.
    Qed.

    Lemma equal_sym:
      forall (m m': t), equal m m' -> equal m' m.
    Proof.
      intros (m, Hm); induction m.
      intros (m', Hm'); destruct m'; unfold equal; simpl; try tauto; auto.
      destruct a as (x,e).
      destruct m'; unfold equal; simpl.
      destruct this0; try tauto.
      destruct p.
      destruct (K.compare x t) as [Hlt|Heq|Hlt]; try order; intuition.
      inversion_clear Hm; inversion_clear sorted0.
      simpl.
      destruct (K.compare t x); try order; auto.
      split; auto.
      apply (IHm H (Build_slist H3)); auto.
    Qed.

    Lemma equal_trans:
      forall m m' m'', equal m m' -> equal m' m'' -> equal m m''.
    Proof.
       intros (m1,Hm1); induction m1;
         intros (m2, Hm2); destruct m2;
           intros (m3, Hm3); destruct m3; unfold equal; simpl;
             try destruct a as (x,e);
             try destruct p as (x',e');
             try destruct p0 as (x'',e''); try contradiction; auto.
       destruct (K.compare x x') as [Hlt|Heq|Hlt];
         destruct (K.compare x' x'') as [Hlt'|Heq'|Hlt'];
         destruct (K.compare x x'') as [Hlt''|Heq''|Hlt''];
         try order; intuition.
       apply eq_trans with e'; auto.
       inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
       apply (IHm1 H0 (Build_slist H5) (Build_slist H7)); intuition.
    Qed.

    Lemma equal_find_eq:
      forall m m' k,
        equal m m' ->
        find k m = find k m'.
    Proof.
      intros (l, Hl); induction l;
        intros (l', Hl'); destruct l'; unfold equal;
          unfold find; simpl; try destruct a; try destruct p;
            intuition.
      generalize H.
      destruct (K.compare k t);
        destruct (K.compare k t0);
        destruct (K.compare t t0);
        try order; intuition.
      rewrite H1; tauto.
       inversion_clear Hl; inversion_clear Hl'.
      apply (IHl H0 (Build_slist H5) k); auto.
    Qed.

    Lemma equal_get_eq:
      forall m m' k,
        equal m m' ->
        get m k = get m' k.
    Proof.
      intros m m' k Heq.
      unfold get.
      rewrite (equal_find_eq k Heq).
      tauto.
    Qed.

    Lemma find_eq_equal:
      forall m m',
        (forall k, find k m = find k m') ->
        equal m m'.
    Proof.
      intros (l, Hl); induction l;
        intros (l', Hl'); destruct l'; intro Hfind.
      unfold equal; simpl; tauto.
      destruct p.
      generalize (Hfind t).
      unfold find; simpl.
      destruct (K.compare t t);
        try order; intro Hf; inversion Hf.
      destruct a.
      generalize (Hfind t).
      unfold find; simpl.
      destruct (K.compare t t);
        try order; intro Hf; inversion Hf.
      destruct a; destruct p.
      generalize (Hfind t).
      unfold find; unfold equal; simpl.
      destruct (K.compare t t0); destruct (K.compare t t); try order; intro Hf.
      inversion Hf.
      split.
      inversion Hf; auto.
      inversion_clear Hl; inversion_clear Hl'.
      apply (IHl H (Build_slist H1)).
      intro k.
      generalize (Hfind k).
      unfold find; simpl.
      destruct (K.compare k t); destruct (K.compare k t0); try order; intro Hf2; auto.
      generalize (find_hd_lt_none'' Hl H l0).
      generalize (find_hd_lt_none'' Hl' H1 l1).
      unfold find; simpl; intros.
      rewrite H3; rewrite H4; auto.
      generalize (find_hd_lt_none' Hl H e3).
      generalize (find_hd_lt_none' Hl' H1 e4).
      unfold find; simpl; intros.
      rewrite H3; rewrite H4; auto.
      generalize (Hfind t0).
      unfold find; simpl.
      destruct (K.compare t0 t); destruct (K.compare t0 t0); try order.
      intro Hn; inversion Hn.
    Qed.

    Lemma upd_equal:
      forall m m' k v, equal m m' -> equal (upd m k v) (upd m' k v).
    Proof.
      intros m m' k v Heq.
      apply find_eq_equal; intro k'.
      destruct (K.eq_dec k' k).
      - repeat rewrite find_upd_eq; auto.
      - repeat rewrite find_upd_neq; auto.
        apply (equal_find_eq k' Heq).
    Qed.

    Lemma upd_upd_equal:
      forall (m m': t) (k k': K.t) (v v': elt),
        equal m m' ->
        K.eq k k' ->
        equal (upd (upd m k v) k' v')
              (upd m' k' v').
    Proof.
      intros m m' k k' v v' Heq Heqk.
      apply find_eq_equal; intro k0.
      case (K.eq_dec k' k0).
      intros Heq0.
      - repeat rewrite (find_upd_eq _ _ Heq0);
        reflexivity.

      - (* k <> k0 *)
        intros Hneq0.
        assert (~ K.eq k0 k').
        eauto.
        assert (~ K.eq k0 k).
        { intros Heq0. apply Hneq0. eapply K.eq_trans; eauto. }
        repeat rewrite (find_upd_neq _ _ H).
        rewrite (find_upd_neq _ _ H0).
        apply equal_find_eq; auto.
    Qed.

    Lemma upd_get_equal:
      forall (m m': t) (k k': K.t),
        equal m m' ->
        K.eq k k' ->
        find k m <> None ->
        equal m (upd m' k (get m' k')).
    Proof.
      intros m m' k k' Hmeq Hkeq Hfind.
      apply find_eq_equal; intro k0.

      case (K.eq_dec k k0).
      - (* k0 = k *)
        intros Heq0.
        rewrite (find_upd_eq m' (get m' k')); auto.
        apply K.eq_sym in Hkeq.
        apply (K.eq_trans Hkeq) in Heq0.
        generalize Hfind.
        assert (K.eq k k').
        order.
        rewrite (find_eq m H).
        rewrite (equal_find_eq k0 Hmeq).
        rewrite (equal_find_eq k' Hmeq).
        assert (K.eq k0 k').
        order.
        rewrite (find_eq m' H0).
        unfold get.
        destruct (find (elt:=elt) k' m').
        auto.
        intro Hn; destruct Hn; auto.
      - (* k0 <> k *)
        intros Hneq.
        rewrite find_upd_neq; auto.
        apply (equal_find_eq k0 Hmeq).
    Qed.

    Lemma upd_upd_swap_equal:
      forall (m m': t) (k k': K.t) (v v': elt),
        equal m m' ->
        ~ K.eq k k' ->
        equal (upd (upd m k v) k' v')
              (upd (upd m' k' v') k v).
    Proof.
      intros m m' k k' v v' Hmeq Hneq.
      apply find_eq_equal; intro k0.
      apply not_eq_sym in Hneq.

      case (K.eq_dec k k0); case (K.eq_dec k0 k').
      - (* k = k' = k0 *)
        order.

      - (* k = k0 /\ k' <> k0 *)
        intros Hneq0' Heq0.
        repeat (try rewrite (find_upd_eq _ _ Heq0);
                try rewrite (find_upd_neq _ _ Hneq0');
                auto).

      - (* k <> k0 /\ k' = k0 *)
        intros Heq0 Hneq0'.
        apply K.eq_sym in Heq0.
        apply not_eq_sym in Hneq0'.
        repeat (try rewrite (find_upd_eq _ _ Heq0);
                try rewrite (find_upd_neq _ _ Hneq0');
                auto).

      - (* k <> k0 /\ k' <> k0 *)
        intros Hneq0' Hneq0''.
        apply not_eq_sym in Hneq0''.
        repeat (try rewrite (find_upd_neq _ _ Hneq0');
                try rewrite (find_upd_neq _ _ Hneq0'');
                auto).
        apply equal_find_eq; auto.
    Qed.

    Lemma upd_inc_equal:
      forall m m' k k' v,
        equal m m' ->
        K.eq k k' ->
        equal (upd_inc m k v)
              (upd_inc m' k' v).
    Proof.
      intros m m' k k' v Hmeq Hkeq.
      apply find_eq_equal; intro k0.
      unfold upd_inc.
      case (K.eq_dec k k0); case (K.eq_dec k' k0).
      (* k = k' = k0 *)
      intro Heq'.
      intro Heq.
      rewrite (find_upd_eq _ _ Heq).
      rewrite (find_upd_eq _ _ Heq').
      rewrite (equal_get_eq k Hmeq).
      rewrite (get_eq m' Hkeq).
      tauto.
      (* k' <> k0 /\ k = k0 *)
      order.
      (* k' = k0 /\ k <> k0 *)
      order.
      (* k' <> k0 /\ k <> k0 *)
      intros Hneq' Hneq.
      apply not_eq_sym in Hneq'.
      apply not_eq_sym in Hneq.
      rewrite (find_upd_neq _ _ Hneq).
      rewrite (find_upd_neq _ _ Hneq').
      apply equal_find_eq; auto.
    Qed.

    Lemma upd_dec_equal:
      forall m m' k k' v,
        equal m m' ->
        K.eq k k' ->
        equal (upd_dec m k v)
              (upd_dec m' k' v).
    Proof.
      intros m m' k k' v Hmeq Hkeq.
      apply find_eq_equal; intro k0.
      unfold upd_dec.
      case (K.eq_dec k k0); case (K.eq_dec k' k0).
      (* k = k' = k0 *)
      intro Heq'.
      intro Heq.
      rewrite (find_upd_eq _ _ Heq).
      rewrite (find_upd_eq _ _ Heq').
      rewrite (equal_get_eq k Hmeq).
      rewrite (get_eq m' Hkeq).
      tauto.
      (* k' <> k0 /\ k = k0 *)
      order.
      (* k' = k0 /\ k <> k0 *)
      order.
      (* k' <> k0 /\ k <> k0 *)
      intros Hneq' Hneq.
      apply not_eq_sym in Hneq'.
      apply not_eq_sym in Hneq.
      rewrite (find_upd_neq _ _ Hneq).
      rewrite (find_upd_neq _ _ Hneq').
      apply equal_find_eq; auto.
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
      apply upd_inc_equal; auto.

      apply find_eq_equal.
      intros k0.
      unfold upd_inc.
        destruct (K.eq_dec k0 k').
        + (* k0 = k' *)
          erewrite find_upd_eq; eauto.
        + (* k0 <> k' *)
          erewrite find_upd_neq; eauto.
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
      - apply find_eq_equal; intros k0.
        unfold upd_dec.
        destruct (K.eq_dec k0 k').
        + (* k0 = k' *)
          erewrite find_upd_eq; eauto.
        + (* k0 <> k' *)
          erewrite find_upd_neq; eauto.
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

    Lemma sum_cons:
      forall m k v sorted sorted',
        sum {| this := (k, v) :: m; sorted := sorted |} =
        elt_add_raw (sum {| this := m; sorted := sorted' |}) v.
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
      forall m k v sorted sorted' f,
        f (k, v) = true ->
        sum_filter {| this := (k, v) :: m; sorted := sorted |} f =
        elt_add_raw v (sum_filter {| this := m; sorted := sorted' |} f).
    Proof.
      intros m k v sorted sorted' f Hf.
      unfold sum_filter. simpl.
      rewrite Hf; simpl.
      reflexivity.
    Qed.

    Lemma sum_filter_hd_false:
      forall m k v sorted sorted' f,
        f (k, v) = false ->
        sum_filter {| this := (k, v) :: m; sorted := sorted |} f =
        sum_filter {| this := m; sorted := sorted' |} f.
    Proof.
      intros m k v sorted sorted' f Hf.
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
        inversion sorted0; subst.
        generalize (IHthis0 H2); clear IHthis0;
          unfold sum_filter; simpl; intros IHthis0.
        rewrite IHthis0.
        reflexivity.
      - inversion sorted0; subst.
        generalize (IHthis0 H2); clear IHthis0;
          unfold sum_filter; simpl; intros IHthis0.
        auto.
    Qed.

    Lemma sum_equal:
      forall m m',
        equal m m' ->
        sum m = sum m'.
    Proof.
      intros (l, Hl); induction l;
      intros (l', Hl'); destruct l'; unfold equal;
        unfold sum; simpl; try destruct a; try destruct p;
          intuition.
      destruct (K.compare t t0); try order; intuition.
      rewrite H0.
      assert (sum_raw l = sum_raw l').
      inversion_clear Hl; inversion_clear Hl'.
      apply (IHl H (Build_slist H3) H1).
      rewrite H; auto.
    Qed.

    Lemma sum_filter_equal:
      forall f m m',
        (forall k k' v, K.eq k k' -> f (k, v) = f (k',v)) ->
        equal m m' ->
        sum_filter m f = sum_filter m' f.
    Proof.
      intros f.
      intros (l, Hl); induction l;
      intros (l', Hl'); destruct l'; unfold equal;
        unfold sum_filter; simpl; try destruct a; try destruct p;
          intuition.
      destruct (K.compare t t0); try order; intuition.
      rewrite H1.
      rewrite (H _ _ _ e1).
      assert (sum_raw (filter f l) = sum_raw (filter f l')).
      inversion_clear Hl; inversion_clear Hl'.
      apply (IHl H0 (Build_slist H4) H H2).
      case (f (t0, e0)); auto.
      simpl.
      rewrite H0; auto.
    Qed.

  End Sum.

  Section Filter.
    Lemma filter_empty:
      forall f,
        map_filter empty f = nil.
    Proof.
      auto.
    Qed.

    Lemma filter_nil:
      forall f sorted,
        map_filter {| this := nil; sorted := sorted |} f = nil.
    Proof.
      auto.
    Qed.

    Lemma filter_hd_true:
      forall f e this sorted sorted',
        f e = true ->
        map_filter {| this := e :: this; sorted := sorted |} f =
        e :: map_filter {| this := this; sorted := sorted' |} f.
    Proof.
      intros f e this sorted sorted' Hf_true.
      unfold map_filter; simpl.
      rewrite Hf_true; auto.
    Qed.

    Lemma filter_hd_false:
      forall f e this sorted sorted',
        f e = false ->
        map_filter {| this := e :: this; sorted := sorted |} f =
        map_filter {| this := this; sorted := sorted' |} f.
    Proof.
      intros f e this sorted sorted' Hf_false.
      unfold map_filter; simpl.
      rewrite Hf_false; auto.
    Qed.

    Lemma filter_not_in_eqk:
      forall (m: t) e f,
        ~ InA (Raw.PX.eqk (elt:=elt)) e (this m) ->
        ~ InA (Raw.PX.eqk (elt:=elt)) e (map_filter m f).
    Proof.
      intros m e f Hnot_in.
      destruct m as [this sorted].
      induction this; simpl; auto.

      inversion sorted; subst; simpl in *.
      case_eq (f a); intros Hf; simpl in *.

      - rewrite (filter_hd_true sorted H1 Hf).
        intros Hin; apply InA_cons in Hin; destruct Hin.
        + apply Hnot_in. constructor 1; auto.
        + destruct a as [k v].
          destruct e as [k' v'].
          generalize (not_InA_not_InA_tl Hnot_in); intros Hnot_in'.
          generalize (IHthis H1 Hnot_in'); clear Hnot_in'; intros Hnot_in'.
          apply Hnot_in'; auto.

      - rewrite (filter_hd_false sorted H1 Hf).
        destruct a as [k v].
        destruct e as [k' v'].
        generalize (not_InA_not_InA_tl Hnot_in); intros Hnot_in'.
        apply IHthis; auto.
    Qed.

    Lemma filter_not_in_eqke:
      forall (m: t) e f,
        ~ InA (Raw.PX.eqke (elt:=elt)) e (this m) ->
        ~ InA (Raw.PX.eqke (elt:=elt)) e (map_filter m f).
    Proof.
      intros m e f Hnot_in.
      destruct m as [this sorted].
      induction this; simpl; auto.

      inversion sorted; subst; simpl in *.
      case_eq (f a); intros Hf; simpl in *.

      - rewrite (filter_hd_true sorted H1 Hf).
        intros Hin; apply InA_cons in Hin; destruct Hin.
        + apply Hnot_in. constructor 1; auto.
        + destruct a as [k v].
          destruct e as [k' v'].
          generalize (not_InA_not_InA_tl Hnot_in); intros Hnot_in'.
          generalize (IHthis H1 Hnot_in'); clear Hnot_in'; intros Hnot_in'.
          apply Hnot_in'; auto.

      - rewrite (filter_hd_false sorted H1 Hf).
        destruct a as [k v].
        destruct e as [k' v'].
        generalize (not_InA_not_InA_tl Hnot_in); intros Hnot_in'.
        apply IHthis; auto.
    Qed.

    Lemma filter_sorted:
      forall (m: t) f,
        Sorted (Raw.PX.ltk (elt:=elt)) (map_filter m f).
    Proof.
      intros m f.
      destruct m as [this sorted].
      induction this.
      compute; auto.
      inversion_clear sorted.
      generalize (IHthis H).
      unfold map_filter. simpl.
      case_eq (f a); auto.
      intros Hf Hs.
      apply Sorted_cons; auto.
      clear IHthis sorted Hs.
      induction this0.
      simpl; auto.
      simpl.
      destruct (f a0).
      apply HdRel_cons.
      inversion H0; auto.
      apply IHthis0.
      inversion H; auto.
      inversion_clear H.
      destruct a.
      destruct a0.
      inversion H0.
      compute in H3.
      apply (HdRel_trans _ H3 H2).
    Qed.

    Lemma filter_true_in:
      forall (m: t) e f,
        InA (Raw.PX.eqke (elt:=elt)) e (this m) ->
        (forall e0 e1, K.eq (fst e0) (fst e1) -> snd e0 = snd e1 -> f e0 = f e1) ->
        f e = true ->
        InA (Raw.PX.eqke (elt:=elt)) e (map_filter m f).
    Proof.
      intros m e f Hin Hf Hfe_true.
      destruct m as [this sorted].
      induction this; simpl; auto.

      inversion sorted; subst; simpl in *.
      destruct a as [k v].
      destruct e as [k' v'].
      destruct (K.eq_dec k' k).

      - (* k' = k *)
        destruct (elt_eq_dec v' v).
        + (* v' = v *)
          generalize (Hf (k', v') (k, v) e e0); intros Hfkv.
          rewrite Hfe_true in Hfkv; apply eq_sym in Hfkv.
          rewrite (filter_hd_true sorted H1 Hfkv).
          constructor 1; auto.

        + (* v' <> v *)
          case_eq (f (k, v)); intros Hfkv.
          * rewrite (filter_hd_true sorted H1 Hfkv).
            constructor 2; auto.
            apply IHthis; auto.
            apply InA_cons in Hin;
              unfold Raw.PX.eqke in Hin;
              simpl in Hin;
              destruct Hin; auto.
            destruct H; contradiction.
          * rewrite (filter_hd_false sorted H1 Hfkv).
            apply IHthis.
            apply InA_cons in Hin;
              unfold Raw.PX.eqke in Hin;
              simpl in Hin;
              destruct Hin; auto.
            destruct H; contradiction.

      - (* k' <> k *)
        case_eq (f (k, v)); intros Hfkv.

        + rewrite (filter_hd_true sorted H1 Hfkv).
          constructor 2; auto.
          apply IHthis; auto.
          apply InA_cons in Hin;
            unfold Raw.PX.eqke in Hin;
            simpl in Hin;
            destruct Hin; auto.
          destruct H; contradiction.

        + rewrite (filter_hd_false sorted H1 Hfkv).
          apply IHthis.
          apply InA_cons in Hin;
            unfold Raw.PX.eqke in Hin;
            simpl in Hin;
            destruct Hin; auto.
          destruct H; contradiction.
    Qed.

    Lemma filter_false_not_in:
      forall f,
        (forall e0 e1, K.eq (fst e0) (fst e1) -> snd e0 = snd e1 -> f e0 = f e1) ->
        forall (m: t) e,
          f e = false ->
          ~ InA (Raw.PX.eqke (elt:=elt)) e (map_filter m f).
    Proof.
      intros f Hf m.
      destruct m as [this sorted].
      induction this; simpl; auto.

      - intros; rewrite filter_nil.
        intros Hin'; eapply (proj1 (InA_nil _ _ )); eauto.

      - intros e Hfe_false.
        case (InA_dec kv_eq_dec e (a :: this0));
          intros Hin_dec.

        + destruct a as [k v].
          destruct e as [k' v'].
          inversion sorted; subst; simpl in *.

          destruct (K.eq_dec k' k).

          * (* k' = k *)
            {
              destruct (elt_eq_dec v' v).

              - (* v' = v *)
                generalize (Hf (k', v') (k, v) e e0); clear Hf; intros Hf.
                rewrite Hfe_false in Hf; apply eq_sym in Hf.
                rewrite (filter_hd_false sorted H1 Hf).
                eapply filter_not_in_eqke; eauto.
                simpl; intros Hin.
                generalize (sorted_in_lt sorted Hin); order.

              - (* v' <> v *)
                apply InA_cons in Hin_dec.
                destruct Hin_dec.

                (* eliminate impossible branch *)
                destruct H; simpl in *; congruence.

                case_eq (f (k, v)); intros Hf'.

                + rewrite (filter_hd_true sorted H1 Hf').
                  intros Hin; apply InA_cons in Hin; destruct Hin.

                  (* eliminate impossible branch *)
                  destruct H0; simpl in *; congruence.

                  generalize H0; clear H0.
                  apply IHthis; auto.

                + rewrite (filter_hd_false sorted H1 Hf').
                  apply IHthis; auto.
            }

          * (* k' <> k *)
            apply InA_cons in Hin_dec.
            destruct Hin_dec.

            (* eliminate impossible branch *)
            destruct H; simpl in *; congruence.

            case_eq (f (k, v)); intros Hf'.
            {
              rewrite (filter_hd_true sorted H1 Hf').
              intros Hin; apply InA_cons in Hin; destruct Hin.

              (* eliminate impossible branch *)
              destruct H0; simpl in *; congruence.

              generalize H0; clear H0.
              apply IHthis; auto.
            }
            {
              rewrite (filter_hd_false sorted H1 Hf').
              apply IHthis; auto.
            }

        + apply filter_not_in_eqke; auto.
    Qed.

    Lemma filter_length_equal:
      forall f m m',
        (forall k k' v, K.eq k k' -> f (k, v) = f (k',v)) ->
        equal m m' ->
        length (map_filter m f) = length (map_filter m' f).
    Proof.
      intros f.
      intros (l, Hl); induction l;
      intros (l', Hl'); destruct l'; unfold equal;
        unfold sum_filter; simpl; try destruct a; try destruct p; intro Hf;
          intuition.
      destruct (K.compare t t0); try order; intuition.
      unfold map_filter; simpl.
      rewrite H0.
      rewrite (Hf _ _ _ e1).
      assert (length (filter f l) = length (filter f l')).
      inversion_clear Hl; inversion_clear Hl'.
      apply (IHl H (Build_slist H3) Hf H1).
      case_eq (f (t0, e0)); intro Hc; simpl; eauto.
    Qed.

    (* The following doesn't seem to be right though. *)
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
       not_in_neq not_in_neq' not_InA_not_InA_tl not_In_not_In_tl
       find_hd_eq find_hd_lt_none find_hd_lt_tl
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
       find_eq_equal equal_find_eq upd_equal
       upd_upd_equal upd_get_equal upd_upd_inc_equal upd_upd_dec_equal
       upd_upd_swap_equal
       upd_inc_equal upd_dec_equal
       upd_inc_unfold_equal upd_dec_unfold_equal
       (* Sum *)
       sum_empty sum_cons
       sum_filter_equal
       sum_filter_true sum_filter_hd_true sum_filter_hd_false
       sum_equal sum_filter_equal
       (* filter *)
       filter_empty filter_nil filter_sorted
       filter_hd_true filter_hd_false filter_not_in_eqk filter_not_in_eqke
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
        |- context [ get {| this := (?k, ?v) :: ?m; sorted := ?sorted |} ?k' ]
      ] =>
      rewrite (get_hd_eq sorted H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: K.eq ?k ?k'
        |- context [ get {| this := (?k, ?v) :: ?m; sorted := ?sorted |} ?k' ]
      ] =>
      rewrite (get_hd_eq sorted (K.eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ |- context [ get {| this := (?k, ?v) :: ?m; sorted := ?sorted |} ?k ]
      ] =>
      rewrite (get_hd_eq' sorted);
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
