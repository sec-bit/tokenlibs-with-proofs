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
