(*
  This file is part of the verified smart contract project of SECBIT Labs.

  Copyright 2018 SECBIT Labs

  Author: Even Lu

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
Require Export ZArith.
Require Export Integers.
Require Export String.
Require Export LibEx.
Require Export Types.
Require Export Mapping.
Require Export AbsModel.

Record state : Type :=
  mk_st {
      st_symbol: string;
      st_name: string;
      st_decimals: uint8;
      st_totalSupply: uint256;

      st_balances: a2v;
      st_allowed: aa2v;

      st_paused: bool;
      st_owner: address;
    }.

Inductive event : Type :=
| ev_revert (this: address): event
| ev_return (A: Type) (ret: A) : event
| ev_transfer (to: address) (v: value) (z: bool) : event
| ev_send (to: address) (v: value) (z: bool) : event
| ev_call (A B: Set) (ct: address) (func: string)
          (args: A) (ret: B) (v: value) (z: bool): event
| ev_dcall (A B: Set) (ct: address) (func: string)
           (args: A) (ret: B) (v: value): event
| ev_Transfer (a: address) (from: address) (to: address) (v: value): event
| ev_Approval (a: address) (owner: address) (spender: address) (v: value): event
| ev_PausableToken (a: address) (ia: uint256) (name: string) (dec: uint8) (sym: string)
| ev_Pause: event
| ev_Unpause: event
.

Definition eventlist := TEventList event.

Definition env := TEnv.

Definition contract := TContract state.

(* Method call *)
Inductive mcall : Type :=
| mc_PausableToken (ia: uint256) (name: string) (dec: uint8) (sym: string)
| mc_fallback
| mc_balanceOf (owner: address)
| mc_transfer (to: address) (v: value)
| mc_transferFrom (from: address) (to: address) (v: value)
| mc_approve (spender: address) (v: value)
| mc_allowance (owner: address) (spender: value)
| mc_totalSupply
| mc_pause
| mc_unpause
| mc_increaseApproval (spender: address) (value: uint256)
| mc_decreaseApproval (spender: address) (value: uint256)
.

(* Message, with a simplication that args are embedded in `m_func`,
   instead of calldata *)
Definition message := TMessage mcall.
