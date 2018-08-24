Require Import Mapping.
Require Import ElemTypes.
Require Import Types.

Module Import A2B := Mapping (Address_as_DT) (BoolElem).
Definition a2b: Type := A2B.t.

Notation "$0" := (A2B.empty) (only parsing) : a2b_scope.

Notation "m '$' k" :=
  (A2B.get m k)
    (at level 50, left associativity, only parsing) : a2b_scope.

Notation "m '$=' m'" :=
  (A2B.equal m m')
    (at level 50, left associativity, only parsing) : a2b_scope.

Notation "m '$' '{' k '<~' v '}'" :=
  (A2B.upd m k v)
    (at level 50, left associativity, only parsing) : a2b_scope.
