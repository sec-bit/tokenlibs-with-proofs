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

(*
   Types. All integer types are modeled as nat.
*)
Definition label := nat.
Definition value := nat.
Definition uint256 := nat.
Definition uint8 := nat.
Definition time := nat.
Definition address := nat.

(*
   Over/underflow is modeled in map update functions.
*)
Parameter MAX_UINT256 : uint256.
