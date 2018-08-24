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

Require Import ZArith.
Require Import DecidableType.

Require Import Mapping.
Require Import ElemTypes.
Require Import Types.

Module AA_as_DT := DecidableTypeEx.PairDecidableType (Address_as_DT) (Address_as_DT).

Module AA2B := Mapping (AA_as_DT) (BoolElem).
Definition aa2b := AA2B.t.

Notation "$0" := (AA2B.empty) (only parsing) : aa2b_scope.

Notation "m '$' '[' k0 ',' k1 ']'" :=
  (AA2B.get m (k0, k1))
    (at level 50, left associativity, only parsing) : aa2b_scope.

Notation "m '$' '{' k0 ',' k1 '<~' v '}'" :=
  (AA2B.upd m (k0, k1) v)
    (at level 50, left associativity, only parsing) : aa2b_scope.

Notation "m '~' m'" :=
  (AA2B.equal m m')
    (at level 70, no associativity, only parsing) : aa2b_scope.

Open Scope aa2b_scope.

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
