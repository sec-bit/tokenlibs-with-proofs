Require Import ZArith.
Require Import DecidableType.

Require Import Mapping.
Require Import ElemTypes.
Require Import Types.

Module AA_as_DT := DecidableTypeEx.PairDecidableType (Address_as_DT) (Address_as_DT).

Module AA2V := Mapping (AA_as_DT) (ValElem).
Definition aa2v := AA2V.t.

Notation "$0" := (AA2V.empty) (only parsing) : aa2v_scope.

Notation "m '$' '[' k0 ',' k1 ']'" :=
  (AA2V.get m (k0, k1))
    (at level 50, left associativity, only parsing) : aa2v_scope.

Notation "m '$' '{' k0 ',' k1 '<~' v '}'" :=
  (AA2V.upd m (k0, k1) v)
    (at level 50, left associativity, only parsing) : aa2v_scope.

Notation "m '$' '{' k0 ',' k1  '<+~' v '}'" :=
  (AA2V.upd_inc m (k0, k1) v)
    (at level 50, left associativity, only parsing) : aa2v_scope.

Notation "m '$' '{' k0 ',' k1 '<-~' v '}'" :=
  (AA2V.upd_dec m (k0, k1) v)
    (at level 50, left associativity, only parsing) : aa2v_scope.

Notation "m '~' m'" :=
  (AA2V.equal m m')
    (at level 70, no associativity, only parsing) : aa2v_scope.

Open Scope aa2v_scope.

Section EqDec.
  Lemma aa_eqdec:
    forall (k k': address * address),
      { (fun x y : nat * nat => fst x = fst y /\ snd x = snd y) k k' } +
      { ~ (fun x y : nat * nat => fst x = fst y /\ snd x = snd y) k k' }.
  Proof.
    intros.
    destruct k as [a0 a1].
    destruct k' as [a0' a1'].
    destruct (Nat.eq_dec a0 a0'); destruct (Nat.eq_dec a1 a1');
      solve [ left; auto |
              right;
              intros Heq; inversion Heq;
              apply n; auto
            ].
  Qed.
End EqDec.

Section Range.
  Lemma upd_in_range:
    forall (m: aa2v) lo hi,
      (forall k, lo <= AA2V.get m k <= hi) ->
      forall v,
        lo <= v <= hi ->
        forall k k',
          lo <= AA2V.get (AA2V.upd m k v) k' <= hi.
  Proof.
    intros.

    destruct (aa_eqdec k' k).
    - rewrite (AA2V.get_upd_eq); auto.
    - rewrite (AA2V.get_upd_neq); auto.
  Qed.

  Lemma upd_inc_in_range:
    forall (m: aa2v) lo hi,
      (forall k, lo <= AA2V.get m k <= hi) ->
      forall k v,
        AA2V.get m k + v <= hi ->
        forall k',
          lo <= AA2V.get (AA2V.upd m k (AA2V.get m k + v)) k' <= hi.
  Proof.
    intros.

    destruct (aa_eqdec k' k).
    - rewrite (AA2V.get_upd_eq); auto.
      generalize (H k); clear H; intros H.
      omega.
    - rewrite (AA2V.get_upd_neq); auto.
  Qed.

  Lemma upd_dec_in_range:
    forall (m: aa2v) lo hi,
      (forall k, lo <= AA2V.get m k <= hi) ->
      forall k v,
        AA2V.get m k - lo >= v ->
        forall k',
          lo <= AA2V.get (AA2V.upd m k (AA2V.get m k - v)) k' <= hi.
  Proof.
    intros.

    destruct (aa_eqdec k' k).
    - rewrite (AA2V.get_upd_eq); auto.
      generalize (H k); clear H; intros H.
      omega.
    - rewrite (AA2V.get_upd_neq); auto.
  Qed.

End Range.

Close Scope aa2v_scope.

Hint Resolve
     upd_in_range
     upd_inc_in_range
     upd_dec_in_range.