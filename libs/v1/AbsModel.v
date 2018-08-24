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

Require Export Lists.List.
Require Export Types.

Set Implicit Arguments.

(* Abstract the common part of contract model definitions. *)

(* Abstract type of the event list *)
Definition TEventList(TEvent: Type): Type := list TEvent.

(* Abstract type of the contract *)
Record TContract(TState: Type): Type :=
  mk_contract {
      w_a: address; (* contract address *)
      w_st: TState; (* contract storage state *)
    }.

(* Abstract type of the call message *)
Record TMessage(Tmcall: Type): Type :=
  mk_msg {
      m_sender: address; (* msg.sender *)
      m_func: Tmcall;    (* function name and arguments *)
      m_val: value;      (* msg.value *)
    }.

(* Abstract environment *)
Record TEnv : Type :=
  mk_env {
      env_time:  time;   (* timestamp *)
      env_bhash: uint256 (* block hash *)
    }.
