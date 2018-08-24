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

Require Import
        Integers
        Lists.List
        String
        ZArith.
Require Export
        AbsModel
        LibEx
        Maps
        Types.

Record State : Type :=
  mk_st {
      st_tokenOwner: v2a;
      st_tokenApprovals: v2a;
      st_ownedTokensCount: a2v;
      st_operatorApprovals: aa2b;
    }.

Record ReceiverState : Type :=
  mk_rev_st {
    }.

Inductive Event : Type :=
| ev_Transfer (this: address) (from: address) (to: address) (token_id: uint256)
| ev_Approval (this: address) (owner: address) (approved: address) (token_id: uint256)
| ev_ApprovalForAll (this: address) (owner: address) (operator: address) (approved: bool)
| ev_constructor (sender: address)
| ev_return {A: Type} (ret: A)
| ev_revert (this: address)
.

Definition EventList := TEventList Event.

Definition Env := TEnv ReceiverState.

Definition Contract := TContract State.

Inductive Mcall : Type :=
| mc_constructor
| mc_balanceOf (owner: address)
| mc_ownerOf (token_id: uint256)
| mc_safeTransferFrom (from: address) (to: address) (token_id: uint256) (data: option bytes)
| mc_transferFrom (from: address) (to: address) (token_id: uint256)
| mc_approve (approved: address) (token_id: uint256)
| mc_setApprovalForAll (operator: address) (approved: bool)
| mc_getApproved (token_id: uint256)
| mc_isApprovedForAll (owner: address) (opeartor: address)
| mc_supportsInterface (if_id: bytes4)
| mc_mint (to: address) (token_id: uint256)
.

Definition Message := TMessage Mcall.

Axiom safeTransferFrom_token_id_in_range:
  forall msg from to id data,
    m_func msg = mc_safeTransferFrom from to id data ->
    0 <= id <= MAX_UINT256.

Axiom transferFrom_token_id_in_range:
  forall msg from to id,
    m_func msg = mc_transferFrom from to id ->
    0 <= id <= MAX_UINT256.

Axiom approve_token_id_in_range:
  forall msg approved id,
    m_func msg = mc_approve approved id ->
    0 <= id <= MAX_UINT256.

Axiom getApproved_token_id_in_range:
  forall msg id,
    m_func msg = mc_getApproved id ->
    0 <= id <= MAX_UINT256.

Axiom ownedTokensCount_in_range:
  forall addr st,
    0 <= A2V.get (st_ownedTokensCount st) addr <= MAX_UINT256.
    

Parameter ERC721_INTERFACE_ID : bytes4.
Parameter ERC165_INTERFACE_ID : bytes4.

Axiom if_neq:
  ERC721_INTERFACE_ID <> ERC165_INTERFACE_ID.
