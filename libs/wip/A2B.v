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

Module Import A2B := Mapping (Address_as_DT) (BoolElem).
Definition a2b: Type := A2B.t.

Notation "$0" := (A2B.empty) (only parsing) : a2b_scope.

Notation "m '$' k" :=
  (A2B.get m k)
    (at level 50, left associativity, only parsing) : a2b_scope.

Notation "m '$' '{' k '<~' v '}'" :=
  (A2B.upd m k v)
    (at level 50, left associativity, only parsing) : a2b_scope.

Notation "m '~' m'" :=
  (A2B.equal m m')
    (at level 70, no associativity, only parsing) : a2b_scope.
