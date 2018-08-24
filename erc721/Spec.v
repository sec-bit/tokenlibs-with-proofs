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
        Maps
        Model
        Types.

Delimit Scope a2v_scope with a2v.
Delimit Scope aa2b_scope with aa2b.
Delimit Scope v2a_scope with v2a.

(* We use an oracle to represent the possible return value from a call
   to the may-not-existing onERC721Received() on the receiver address. *)
Parameter onERC721Received_oracle: address -> address -> uint256 -> option bytes -> option bytes4.
Parameter onERC721Received_succ_ret: bytes4.

Definition INV (S: State) (env: Env) (msg: Message) : Prop :=
  forall owner,
    owner <> 0 ->
    length (V2A.map_filter (st_tokenOwner S) (fun e => Nat.eqb (snd e) owner)) = (st_ownedTokensCount S $ owner)%a2v.

Record Spec: Type :=
  mk_spec {
      spec_require: State -> Prop;
      spec_events: State -> EventList -> Prop;
      spec_trans: State -> State -> Prop
    }.

Definition funcspec_constructor :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          (st_tokenOwner S ~ $0)%v2a
          /\ (st_tokenApprovals S ~ $0)%v2a
          /\ (st_ownedTokensCount S ~ $0)%a2v
          /\ (st_operatorApprovals S ~ $0)%aa2b
       )

       (fun S E =>
          E = ev_constructor (m_sender msg) :: nil
       )

       (fun S S' =>
          (st_tokenOwner S' ~ $0)%v2a
          /\ (st_tokenApprovals S' ~ $0)%v2a
          /\ (st_ownedTokensCount S' ~ $0)%a2v
          /\ (st_operatorApprovals S' ~ $0)%aa2b
       )
    ).

Definition funcspec_balanceOf (owner: address) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          owner <> 0
       )

       (fun S E =>
          E = ev_return (st_ownedTokensCount S $ owner)%a2v :: nil
       )

       (fun S S' =>
          S' = S
       )
    ).

Definition funcspec_ownerOf (token_id: uint256) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          (st_tokenOwner S $ token_id)%v2a <> 0
       )

       (fun S E =>
          E = ev_return (st_tokenOwner S $ token_id)%v2a :: nil
       )

       (fun S S' =>
          S' = S
       )
    ).

Definition funcspec_safeTransferFrom
           (from: address) (to: address) (token_id: uint256) (data: option bytes) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          let owner := (st_tokenOwner S $ token_id)%v2a in
          let sender := m_sender msg in
          (* token is valid *)
          owner <> 0
          /\ owner = from
          (* msg.sender is the token owner, the approved account, or the operator
             of token owner *)
          /\ (sender = owner \/
              (sender <> owner /\ sender = (st_tokenApprovals S $ token_id)%v2a) \/
              (sender <> owner /\ sender <> (st_tokenApprovals S $ token_id)%v2a /\ st_operatorApprovals S $ [owner, sender] = true))
          (* cannot transfer to an invalid address *)
          /\ to <> 0
          (* receiver either is not a contract, or has onERC721Received() which
             can return the expected signature *)
          /\ (env_contract env to = None \/
              exists RS,
                env_contract env to = Some RS /\
                onERC721Received_oracle from to token_id data = Some onERC721Received_succ_ret)
          /\ (from <> to -> st_ownedTokensCount S $ to <= MAX_UINT256 - 1)%a2v
       )

       (fun S E =>
          E = ev_Transfer this from to token_id :: nil
       )

       (fun S S' =>
          (st_tokenOwner S' ~ st_tokenOwner S $ { token_id <~ to })%v2a
          /\ (st_tokenApprovals S' ~ st_tokenApprovals S $ { token_id <~ 0 })%v2a
          /\ (st_ownedTokensCount S' ~ st_ownedTokensCount S $ { from <-~ 1 } $ { to <+~ 1 })%a2v
          /\ (st_operatorApprovals S' ~ st_operatorApprovals S)%aa2b
       )
    ).

Definition funcspec_transferFrom
           (from: address) (to: address) (token_id: uint256) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          let owner := (st_tokenOwner S $ token_id)%v2a in
          let sender := m_sender msg in
          (* token is valid *)
          owner <> 0
          /\ owner = from
          (* msg.sender is the token owner, the approved account, or the operator
             of token owner *)
          /\ (sender = owner \/
              (sender <> owner /\ sender = (st_tokenApprovals S $ token_id)%v2a) \/
              (sender <> owner /\ sender <> (st_tokenApprovals S $ token_id)%v2a /\ st_operatorApprovals S $ [owner, sender] = true))
          (* cannot transfer to an invalid address *)
          /\ to <> 0
          /\ (from <> to -> st_ownedTokensCount S $ to <= MAX_UINT256 - 1)%a2v
       )

       (fun S E =>
          E = ev_Transfer this from to token_id :: nil
       )

       (fun S S' =>
          (st_tokenOwner S' ~ st_tokenOwner S $ { token_id <~ to })%v2a
          /\ (st_tokenApprovals S' ~ st_tokenApprovals S $ { token_id <~ 0 })%v2a
          /\ (st_ownedTokensCount S' ~ st_ownedTokensCount S $ { from <-~ 1 } $ { to <+~ 1 })%a2v
          /\ (st_operatorApprovals S' ~ st_operatorApprovals S)%aa2b
       )
    ).

Definition funcspec_approve (approved: address) (token_id: uint256) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          let owner := (st_tokenOwner S $ token_id)%v2a in
          let sender := m_sender msg in
          (sender = owner
           \/ (sender <> owner /\ st_operatorApprovals S $ [owner, sender] = true))
          /\ approved <> owner
       )

       (fun S E =>
          E = ev_Approval this (st_tokenOwner S $ token_id)%v2a approved token_id :: nil
       )

       (fun S S' =>
          st_tokenOwner S' ~ st_tokenOwner S
          /\ (st_tokenApprovals S' ~ st_tokenApprovals S $ { token_id <~ approved })%v2a
          /\ (st_ownedTokensCount S' ~ st_ownedTokensCount S)%a2v
          /\ (st_operatorApprovals S' ~ st_operatorApprovals S)%aa2b
       )
    ).

Definition funcspec_setApprovalForAll (operator: address) (approved: bool) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          m_sender msg <> operator
       )

       (fun S E =>
          E = ev_ApprovalForAll this (m_sender msg) operator approved :: nil
       )

       (fun S S' =>
          st_tokenOwner S' ~ st_tokenOwner S
          /\ (st_tokenApprovals S' ~ st_tokenApprovals S)%v2a
          /\ (st_ownedTokensCount S' ~ st_ownedTokensCount S)%a2v
          /\ (st_operatorApprovals S' ~ st_operatorApprovals S $ { m_sender msg, operator <~ approved })%aa2b
       )
    ).

Definition funcspec_getApproved (token_id: uint256) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          (st_tokenOwner S $ token_id)%v2a <> 0
       )

       (fun S E =>
          E = ev_return (st_tokenApprovals S $ token_id)%v2a :: nil
       )

       (fun S S' =>
          S' = S
       )
    ).

Definition funcspec_isApprovedForAll (owner: address) (operator: address) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          True
       )

       (fun S E =>
          E = ev_return (st_operatorApprovals S $ [owner, operator])%aa2b :: nil
       )

       (fun S S' =>
          S' = S
       )
    ).

Definition funcspec_supportsInterface (if_id: bytes4) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          True
       )

       (fun S E =>
          if Nat.eqb if_id ERC165_INTERFACE_ID then
            E = ev_return true :: nil
          else
            if Nat.eqb if_id ERC721_INTERFACE_ID then
              E = ev_return true :: nil
            else
              E = ev_return false :: nil
       )

       (fun S S' =>
          S' = S
       )
    ).

Definition funcspec_mint (to: address) (token_id: uint256) :=
  fun (this: address) (env: Env) (msg: Message) =>
    (mk_spec
       (fun S =>
          (st_tokenOwner S $ token_id)%v2a = 0
          /\ (st_ownedTokensCount S $ to)%a2v <= MAX_UINT256 - 1
          /\ to <> 0
       )

       (fun S E =>
          E = ev_Transfer this 0 to token_id :: nil
       )

       (fun S S' =>
          st_tokenOwner S' ~ st_tokenOwner S $ { token_id <~ to }
          /\ (st_tokenApprovals S' ~ st_tokenApprovals S)%v2a
          /\ (st_ownedTokensCount S' ~ st_ownedTokensCount S $ { to <+~ 1 })%a2v
          /\ (st_operatorApprovals S' ~ st_operatorApprovals S)%aa2b
       )
    ).

Inductive create : Env-> Message -> Contract -> EventList -> Prop :=
| create_constructor:
    forall env msg C' evts' sender S spec,
      msg = mk_msg sender mc_constructor 0
      -> spec = funcspec_constructor (w_a C') env msg
      -> spec_require spec S
      -> spec_events spec S evts'
      -> spec_trans spec S (w_st C')
      -> create env msg C' evts'.

Definition func_step
           (msg: Message)
           (spec: Spec)
           (env: Env)
           (C C': Contract)
           (E: EventList) : Prop :=
  w_a C = w_a C'
  /\ INV (w_st C) env msg
  /\ INV (w_st C') env msg
  /\ (spec_require spec) (w_st C)
  /\ (spec_events spec) (w_st C) E
  /\ (spec_trans spec) (w_st C) (w_st C').

Inductive step : Env -> Contract -> Message -> Contract -> EventList -> Prop :=
| step_balanceOf: forall msg spec env C C' E' sender owner,
    msg = mk_msg sender (mc_balanceOf owner) 0
    -> spec = funcspec_balanceOf owner (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_ownerOf: forall msg spec env C C' E' sender token,
    msg = mk_msg sender (mc_ownerOf token) 0
    -> spec = funcspec_ownerOf token (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_safeTransferFrom: forall msg spec env C C' E' sender from to token data,
    msg = mk_msg sender (mc_safeTransferFrom from to token data) 0
    -> spec = funcspec_safeTransferFrom from to token data (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_transferFrom: forall msg spec env C C' E' sender from to token,
    msg = mk_msg sender (mc_transferFrom from to token) 0
    -> spec = funcspec_transferFrom from to token (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_approve: forall msg spec env C C' E' sender approved token,
    msg = mk_msg sender (mc_approve approved token) 0
    -> spec = funcspec_approve approved token (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_setApprovalForAll: forall msg spec env C C' E' sender operator approved,
    msg = mk_msg sender (mc_setApprovalForAll operator approved) 0
    -> spec = funcspec_setApprovalForAll operator approved (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_getApproved: forall msg spec env C C' E' sender token,
    msg = mk_msg sender (mc_getApproved token) 0
    -> spec = funcspec_getApproved token (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_isApprovedForAll: forall msg spec env C C' E' sender owner operator,
    msg = mk_msg sender (mc_isApprovedForAll owner operator) 0
    -> spec = funcspec_isApprovedForAll owner operator (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_supportsInterface: forall msg spec env C C' E' sender id,
    msg = mk_msg sender (mc_supportsInterface id) 0
    -> spec = funcspec_supportsInterface id (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_mint: forall msg spec env C C' E' sender to token,
    msg = mk_msg sender (mc_mint to token) 0
    -> spec = funcspec_mint to token (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'
.

Definition env_step (env1: Env) (env2: Env) : Prop :=
  env_time env2 >= env_time env1 /\ env_bhash env2 <> env_bhash env1.

Fixpoint steps
         (env: Env)
         (C: Contract)
         (ml: list Message)
         (env': Env)
         (C': Contract)
         (E: EventList) : Prop :=
  match ml with
  | nil => C' = C /\ E = nil /\ env = env'
  | cons msg ml =>
    exists env'', exists C'', exists E'', exists E',
            step env C msg C'' E'' /\ steps env'' C'' ml env' C' E'
            /\ E = E'' ++ E'
            /\ env_step env env''
  end.

(* Running a smart contract c in environment env over a list of messages. *)
Definition run
           (env: Env)
           (C: Contract)
           (ml: list Message)
           (C': Contract)
           (E: EventList) : Prop :=
  exists env',
    steps env C ml env' C' E.
