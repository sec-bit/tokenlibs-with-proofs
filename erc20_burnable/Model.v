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
| ev_BurnableToken (a: address) (ia: uint256) (name: string) (dec: uint8) (sym: string)
| ev_Burn (a: address)(burner: address)(v: value):event
.

Definition eventlist := TEventList event.

Definition env := TEnv.

Definition contract := TContract state.

(* Method call *)
Inductive mcall : Type :=
| mc_BurnableToken (ia: uint256) (name: string) (dec: uint8) (sym: string)
(* | mc_user (A: Set) (m: A): mcall *)
| mc_fallback: mcall
| mc_balanceOf (owner: address): mcall
| mc_transfer (to: address) (v: value): mcall
| mc_transferFrom (from: address) (to: address) (v: value): mcall
| mc_approve (spender: address) (v: value): mcall
| mc_allowance (owner: address) (spender: value): mcall
| mc_burn (v: value):mcall
| mc_totalSupply: mcall
.

(* Message, with a simplication that args are embedded in `m_func`,
   instead of calldata *)
Definition message := TMessage mcall.

(* Assume parameters of message calls are in valid ranges. *)

Axiom ctor_totalSupply_inrange:
  forall ia name dec sym msg,
    msg = mc_BurnableToken ia name dec sym -> 0 <= ia /\ ia <= MAX_UINT256.

Axiom transfer_value_inrange:
  forall to v msg,
    msg = mc_transfer to v -> 0 <= v /\ v <= MAX_UINT256.

Axiom transferFrom_value_inrange:
  forall from to v msg,
    msg = mc_transferFrom from to v -> 0 <= v /\ v <= MAX_UINT256.

Axiom approve_value_inrange:
  forall spender v msg,
    msg = mc_approve spender v -> 0 <= v /\ v <= MAX_UINT256.

Axiom burn_value_inrange:
  forall v msg,
    msg = mc_burn v -> 0 <= v /\ v <= MAX_UINT256.