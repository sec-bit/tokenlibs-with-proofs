Require Import Mapping.
Require Import ElemTypes.
Require Import Types.
Require Import LibEx.

Module Import V2A := Mapping (UINT256_as_DT) (AddrElem).
Definition v2a: Type := V2A.t.

Notation "$0" := (V2A.empty) (only parsing) : v2a_scope.

Notation "m '$' k" :=
  (V2A.get m k)
    (at level 50, left associativity, only parsing) : v2a_scope.

Notation "m '$' '{' k '<~' v '}'" :=
  (V2A.upd m k v)
    (at level 50, left associativity, only parsing) : v2a_scope.

Notation "m '~' m'" :=
  (V2A.equal m m')
    (at level 70, no associativity, only parsing) : v2a_scope.

Open Scope v2a_scope.
