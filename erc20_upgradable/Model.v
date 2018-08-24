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

Require Export LibEx.
Require Export Lists.List.
Require Export ZArith.
Require Export Integers.
Require Export String.
Require Export Types.
Require Export Maps.
Require Export AbsModel.

Record oldState : Type :=
  mk_ost {
      ost_symbol: string;
      ost_name: string;
      ost_decimals: uint8;
      ost_totalSupply: uint256;
      ost_balances: a2v;
      ost_allowed: aa2v;

      ost_owner: address;
      ost_stopped: bool;
   }.

Record state : Type :=
  mk_st {
      st_symbol: string;
      st_name: string;
      st_decimals: uint8;
      st_totalSupply: uint256;
      st_balances: a2v;
      st_allowed: aa2v;
      st_owner: address;
      st_migratedBalances: a2b;
      st_oldToken: address;
   }.

Inductive event : Type :=
  | ev_constructor (a: address) (oldToken: address)
  | ev_Transfer (a: address) (from: address) (to: address) (v: uint256)
  | ev_Approval (a: address) (owner: address) (spender: address) (v: uint256)
  | ev_Migrate (old new acct: address) (v: uint256)
  | ev_OwnershipTransferred (a: address) (old: address) (new: address)
  | ev_return (A: Type) (ret: A)
  | ev_revert (this: address)
.

Definition eventlist := TEventList event.

Definition env := TEnv oldState.

Definition contract := TContract state.

(* Method call *)
Inductive mcall : Type :=
  | mc_constructor (oldToken: address) : mcall
  | mc_totalSupply: mcall
  | mc_balanceOf (owner: address): mcall
  | mc_transfer (to: address) (v: uint256): mcall
  | mc_transferFrom (from: address) (to: address) (v: uint256): mcall
  | mc_approve (spender: address) (v: uint256): mcall
  | mc_allowance (owner: address) (spender: uint256): mcall
  | mc_increaseApproval (spender: address)(addValue: uint256): mcall
  | mc_decreaseApproval (spender: address)(subValue: uint256): mcall
  | mc_transferOwnership (onwer: address)
.

(* Message, with a simplication that args are embedded in `m_func`,
   instead of calldata *)
Definition message := TMessage mcall.

(* Assume all message call parameters are in valid ranges. *)

Axiom transfer_value_inrange:
  forall msg to v,
    m_func msg = mc_transfer to v -> 0 <= v <= MAX_UINT256.

Axiom transferFrom_value_inrange:
  forall msg from to v,
    m_func msg = mc_transferFrom from to v -> 0 <= v <= MAX_UINT256.

Axiom approve_value_inrange:
  forall msg spender v,
    m_func msg = mc_approve spender v -> 0 <= v <= MAX_UINT256.

Axiom increaseApproval_value_inrange:
  forall msg spender v,
    m_func msg = mc_increaseApproval spender v -> 0 <= v <= MAX_UINT256.

Axiom decreaseApproval_value_inrange:
  forall msg spender v,
    m_func msg = mc_decreaseApproval spender v -> 0 <= v <= MAX_UINT256.