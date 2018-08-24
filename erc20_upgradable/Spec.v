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

Require Export Model.
Require Export Lists.List.
Require Export Maps.

Delimit Scope a2v_scope with a2v.
Delimit Scope aa2v_scope with aa2v.
Delimit Scope a2b_scope with a2b.

Open Scope a2b.
Open Scope aa2v_scope.
Open Scope a2v_scope.

(* Global invariant that must hold before and after each function call. *)
Definition INV_sum_blncs (S: state) (OS: oldState) : Prop :=
  A2V.sum (st_balances S) +
  A2V.sum_filter (ost_balances OS)
                 (fun e => negb (st_migratedBalances S $ (fst e))%a2b) <= MAX_UINT256.

Definition INV (S: state) (env: env) (msg: message) : Prop :=
  (* The total supply of tokens is always in the valid range. *)
  0 <= st_totalSupply S <= MAX_UINT256 /\
  (* Every allowance is in the valid range. *)
  (forall k: address * address, 0 <= AA2V.get (st_allowed S) k <= MAX_UINT256) /\
  exists OS,
    (* The old contract must exist *)
    env_contract env (st_oldToken S) = Some OS /\
    (* The old contract is always in the stopped state *)
    ost_stopped OS = true /\
    INV_sum_blncs S OS.

(* Function specification:
   - spec_require PreS: requirements that must be satisfied before the function execution;
   - spec_events PreS events: events that occurred during the function execution;
   - spec_trans PreS PostS: how the contract state is changed by the function execution.
*)
Record Spec: Type :=
  mk_spec {
      spec_require: state -> Prop;
      spec_events: state -> eventlist -> Prop;
      spec_trans: state -> state -> Prop
    }.

Definition funcspec_constructor (oldTokenAddr: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S: state =>
          st_balances S = ($0)%a2v
          /\ st_allowed S = ($0)%aa2v
          /\ st_migratedBalances S = ($0)%a2b
          /\ exists OS,
            env_contract env (oldTokenAddr) = Some OS
            (* old contract must be stopped to avoid race conditions *)
            /\ ost_stopped OS = true
            (* the sum of balances in old contract must equal the total supply *)
            /\ A2V.sum (ost_balances OS) = ost_totalSupply OS
            (* the old total supply must be in the valid range *)
            /\ 0 <= ost_totalSupply OS <= MAX_UINT256
       )

       (fun S E =>
          E = ev_constructor (m_sender msg) oldTokenAddr :: nil
       )

       (* State transition: *)
       (fun S S' : state =>
          st_oldToken S' = oldTokenAddr
          (* following fields are migrated immediately *)
          /\ (exists OS, env_contract env oldTokenAddr = Some OS
                         /\ st_totalSupply S' = ost_totalSupply OS
                         /\ st_name S' = ost_name OS
                         /\ st_decimals S' = ost_decimals OS
                         /\ st_symbol S' =  ost_symbol OS)
          (* balances[] will be migrated on demand *)
          /\ A2V.equal (st_balances S') $0
          /\ A2B.equal (st_migratedBalances S') ($0)%a2b
          /\ AA2V.equal (st_allowed S') ($0)%aa2v
          (* update token owner to the new caller*)
          /\ st_owner S' = m_sender msg
       )
    ).

(* Spec of transferFrom for the case that
   - the withdraw account has not been migrated
   - the allowance is not unlimited
 *)
Definition funcspec_transferFrom_1
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          (* the withdraw account has not been migrated *)
          (st_migratedBalances S  $ from)%a2b = false
          (* the allowance is sufficient and not unlimited *)
          /\ value <= st_allowed S $ [from, m_sender msg] < MAX_UINT256
          /\ exists OS,
              (* the old contract still exists *)
              env_contract env (st_oldToken S) = Some OS
              (* the withdraw account has sufficient balance *)
              /\ (st_balances S $ from) + (ost_balances OS $ from) >= value
       )

       (fun S E =>
          exists OS,
            env_contract env (st_oldToken S) = Some OS
            /\  E = ev_Migrate (st_oldToken S) this from (ost_balances OS $ from)
                    :: ev_Transfer this from to value
                    :: ev_return _ true
                    :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ (exists OS,
                 env_contract env (st_oldToken S) = Some OS
                 /\ A2V.equal (st_balances S')
                              (st_balances S
                                           $ { from <+~ ost_balances OS $ from }
                                           $ { from <-~ value }
                                           $ { to <+~ value }))
          /\ AA2V.equal (st_allowed S') (st_allowed S $ { from, m_sender msg <-~ value })
          /\ st_owner S' = st_owner S
          /\ A2B.equal (st_migratedBalances S') (st_migratedBalances S $ { from <~ true })%a2b
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec of transferFrom for the case that
   - the withdraw account has been migrated
   - the allowance is not unlimited
*)
Definition funcspec_transferFrom_2
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          (st_migratedBalances S $ from)%a2b = true
          /\ value <= st_allowed S $ [from, m_sender msg] < MAX_UINT256
          /\ st_balances S $ from >= value
       )

       (fun S E =>
          exists OS,
            env_contract env (st_oldToken S) = Some OS
            /\  E = ev_Transfer this from to value
                    :: ev_return _ true
                    :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ A2V.equal (st_balances S')
                       (st_balances S
                                    $ { from <-~ value }
                                    $ { to <+~ value })
          /\ AA2V.equal (st_allowed S') (st_allowed S $ { from, m_sender msg <-~ value })
          /\ st_owner S' = st_owner S
          /\ A2B.equal (st_migratedBalances S') (st_migratedBalances S)
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec of transferFrom for the case that
   - the withdraw account has not been migrated
   - the allowance if unlimited
*)
Definition funcspec_transferFrom_3
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          (st_migratedBalances S $ from)%a2b = false
          /\ st_allowed S $ [from, m_sender msg] = MAX_UINT256
          /\ exists OS,
              env_contract env (st_oldToken S) = Some OS
              /\ (st_balances S $ from) + (ost_balances OS $ from) >= value
       )

       (fun S E =>
          exists OS,
            env_contract env (st_oldToken S) = Some OS
            /\  E = ev_Migrate (st_oldToken S) this from (ost_balances OS $ from)
                    :: ev_Transfer this from to value
                    :: ev_return _ true
                    :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ (exists OS,
                 env_contract env (st_oldToken S) = Some OS
                 /\ A2V.equal (st_balances S')
                              (st_balances S
                                           $ { from <+~ ost_balances OS $ from }
                                           $ { from <-~ value }
                                           $ { to <+~ value }))
          /\ AA2V.equal (st_allowed S') (st_allowed S)
          /\ st_owner S' = st_owner S
          /\ A2B.equal (st_migratedBalances S') (st_migratedBalances S $ { from <~ true })%a2b
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec of transferFrom for the case that
   - the withdraw account has been migrated
   - the allowance is unlimited
*)
Definition funcspec_transferFrom_4
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          (st_migratedBalances S $ from)%a2b = true
          /\ st_allowed S $ [from, m_sender msg] = MAX_UINT256
          /\ st_balances S $ from >= value
       )

       (fun S E =>
          exists OS,
            env_contract env (st_oldToken S) = Some OS
            /\  E = ev_Transfer this from to value
                    :: ev_return _ true
                    :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ A2V.equal (st_balances S')
                       (st_balances S
                                    $ { from <-~ value }
                                    $ { to <+~ value })
          /\ AA2V.equal (st_allowed S') (st_allowed S)
          /\ st_owner S' = st_owner S
          /\ A2B.equal (st_migratedBalances S') (st_migratedBalances S)
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec of transfer() for the case that the withdraw account has not been migrated. *)
Definition funcspec_transfer_1
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          (* migration is needed *)
          (st_migratedBalances S $ (m_sender msg))%a2b = false
          /\ exists OS,
            env_contract env (st_oldToken S) = Some OS
            (* the withdrew account after migration has enough balance *)
            /\ (st_balances S $ (m_sender msg)) + (ost_balances OS $ (m_sender msg)) >= value
       )

       (fun S E =>
          exists OS,
            env_contract env (st_oldToken S) = Some OS
            /\  E = ev_Migrate (st_oldToken S) this (m_sender msg) (ost_balances OS $ (m_sender msg))
                    :: ev_Transfer this (m_sender msg) to value
                    :: ev_return _ true
                    :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ (exists OS,
                 env_contract env (st_oldToken S) = Some OS
                 /\ st_balances S' = st_balances S
                                                 $ { m_sender msg <+~ ost_balances OS $ (m_sender msg) }
                                                 $ { m_sender msg <-~ value }
                                                 $ { to <+~ value })
          /\ st_allowed S' = st_allowed S
          /\ st_owner S' = st_owner S
          /\ st_migratedBalances S' = (st_migratedBalances S $ { m_sender msg <~ true })%a2b
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec of transfer() for the case that the withdraw balance has been migrated. *)
Definition funcspec_transfer_2
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
            (st_migratedBalances S $ (m_sender msg))%a2b = true
            (* the withdrew account has enough balance *)
            /\ st_balances S $ (m_sender msg) >= value
       )

       (fun S E =>
          exists OS,
            env_contract env (st_oldToken S) = Some OS
            /\  E = ev_Transfer this (m_sender msg) to value
                    :: ev_return _ true
                    :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ st_balances S' = st_balances S
                                          $ { m_sender msg <-~ value }
                                          $ { to <+~ value }
          /\ st_allowed S' = st_allowed S
          /\ st_owner S' = st_owner S
          /\ st_migratedBalances S' = st_migratedBalances S
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec of balanceOf() for the case that the balance of owner has not been migrated. *)
Definition funcspec_balanceOf_1
           (owner: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          (st_migratedBalances S $ owner)%a2b = false
       )

       (fun S E =>
          exists OS,
            env_contract env (st_oldToken S) = Some OS
            /\ E = ev_Migrate (st_oldToken S) this owner (ost_balances OS $ owner)
                   :: ev_return _ ((st_balances S $ owner) + (ost_balances OS $ owner))
                   :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ (exists OS,
                 env_contract env (st_oldToken S) = Some OS
                 /\ st_balances S' = st_balances S $ { owner <+~ (ost_balances OS $ owner) })
          /\ st_allowed S' = st_allowed S
          /\ st_owner S' = st_owner S
          /\ st_migratedBalances S' = (st_migratedBalances S $ { owner <~ true })%a2b
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec of balanceOf() for the case that the balance of owner has been migrated. *)
Definition funcspec_balanceOf_2
           (owner: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          (st_migratedBalances S $ owner)%a2b = true
       )

       (fun S E =>
          E = ev_return _ (st_balances S $ owner) :: nil
       )

       (fun S S' : state => S = S')
    ).

Definition funcspec_approve
           (spender: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state => True)

       (* emit Approval(msg.sender, _spender, _value); *)
       (* return True; *)
       (fun S E => E = ev_Approval this (m_sender msg) spender value
                       :: ev_return _ true
                       :: nil
       )

       (* State transition: *)
       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ st_balances S' = st_balances S
          /\ st_allowed S' = st_allowed S $ { m_sender msg, spender <~ value }
          /\ st_owner S' = st_owner S
          /\ st_migratedBalances S' = st_migratedBalances S
          /\ st_oldToken S' = st_oldToken S
       )
    ).

Definition funcspec_allowance
           (owner: address)
           (spender: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (* No requirement *)
       (fun S : state => True)

       (* return allowed[_owner][_spender]; *)
       (fun S E => E = (ev_return _ (st_allowed S $ [owner, spender])) :: nil)

       (* Unchanged. *)
       (fun S S' : state => S' = S)
    ).

Definition funcspec_increaseApproval
           (spender: address)
           (addValue: value):=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          st_allowed S $ [m_sender msg , spender] <= MAX_UINT256 - addValue
       )

       (fun S E =>
          E = ev_Approval this (m_sender msg) spender ((st_allowed S $ [m_sender msg, spender] + addValue))
              :: (ev_return _ true)
              :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ st_balances S' = st_balances S
          /\ st_allowed S' = st_allowed S $ { m_sender msg, spender <+~ addValue }
          /\ st_owner S' = st_owner S
          /\ st_migratedBalances S' = st_migratedBalances S
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec for decreaseApproval() for the case that the existing allowance is insufficient. *)
Definition funcspec_decreaseApproval_1
           (spender: address)
           (subValue: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          st_allowed S $ [m_sender msg, spender] < subValue
       )

       (fun S E =>
          E = ev_Approval this (m_sender msg) spender 0
              :: (ev_return _ true)
              :: nil
       )

       (* State transition: *)
       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ st_balances S' = st_balances S
          /\ st_allowed S' = st_allowed S $ { m_sender msg, spender <~ 0 }
          /\ st_owner S' = st_owner S
          /\ st_migratedBalances S' = st_migratedBalances S
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Spec for decreaseApproval() for the case that the existing allowance is sufficient.*)
Definition funcspec_decreaseApproval_2
           (spender: address)
           (subValue: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          st_allowed S $ [m_sender msg, spender] >= subValue
       )

       (fun S E =>
          E = ev_Approval this (m_sender msg) spender ((st_allowed S $ [m_sender msg, spender]) - subValue)
              :: (ev_return _ true)
              :: nil
       )

       (fun S S' : state =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ st_balances S' = st_balances S
          /\ st_allowed S' = st_allowed S $ { m_sender msg, spender <-~ subValue }
          /\ st_owner S' = st_owner S
          /\ st_migratedBalances S' = st_migratedBalances S
          /\ st_oldToken S' = st_oldToken S
       )
    ).

Definition funcspec_transferOwnership
           (new: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
          m_sender msg = st_owner S
       )

       (fun S E =>
          E = ev_OwnershipTransferred this (st_owner S) new
              :: (ev_return _ true)
              :: nil
       )

       (fun S S' =>
          st_symbol S' = st_symbol S
          /\ st_name S' = st_name S
          /\ st_decimals S' = st_decimals S
          /\ st_totalSupply S' = st_totalSupply S
          /\ st_balances S' = st_balances S
          /\ st_allowed S' = st_allowed S
          /\ st_owner S' = new
          /\ st_migratedBalances S' = st_migratedBalances S
          /\ st_oldToken S' = st_oldToken S
       )
    ).

(* Constructor invocation. *)
Inductive create : env-> message -> contract -> eventlist -> Prop :=
| create_constructor:
    forall env msg C' evts' oldAddr sender S spec,
      msg = mk_msg sender (mc_constructor oldAddr) 0
      -> spec = funcspec_constructor oldAddr (w_a C') env msg
      -> spec_require spec S
      -> spec_events spec S evts'
      -> spec_trans spec S (w_st C')
      -> create env msg C' evts'.

(* Evaluation step: any of the possible invocations. *)
Definition func_step
           (msg: message)
           (spec: Spec)
           (env: env)
           (C C': contract)
           (E: eventlist) : Prop :=
  w_a C = w_a C'
  /\ INV (w_st C) env msg
  /\ INV (w_st C') env msg
  /\ (spec_require spec) (w_st C)
  /\ (spec_events spec) (w_st C) E
  /\ (spec_trans spec) (w_st C) (w_st C').

Inductive step : env -> contract -> message -> contract -> eventlist -> Prop :=
| step_transfer_1: forall msg spec env C C' E' sender to v,
    msg = mk_msg sender (mc_transfer to v) 0
    -> spec = funcspec_transfer_1 to v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_transfer_2: forall msg spec env C C' E' sender to v,
    msg = mk_msg sender (mc_transfer to v) 0
    -> spec = funcspec_transfer_2 to v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_balanceOf_1: forall msg spec env C C' E' sender owner,
    msg = mk_msg sender (mc_balanceOf owner) 0
    -> spec = funcspec_balanceOf_1 owner (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_balanceOf_2: forall msg spec env C C' E' sender owner,
    msg = mk_msg sender (mc_balanceOf owner) 0
    -> spec = funcspec_balanceOf_2 owner (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_transferFrom_1: forall msg spec env C C' E' sender from to v,
    msg = mk_msg sender (mc_transferFrom from to v) 0
    -> spec = funcspec_transferFrom_1 from to v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_transferFrom_2: forall msg spec env C C' E' sender from to v,
    msg = mk_msg sender (mc_transferFrom from to v) 0
    -> spec = funcspec_transferFrom_2 from to v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_transferFrom_3: forall msg spec env C C' E' sender from to v,
    msg = mk_msg sender (mc_transferFrom from to v) 0
    -> spec = funcspec_transferFrom_3 from to v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_transferFrom_4: forall msg spec env C C' E' sender from to v,
    msg = mk_msg sender (mc_transferFrom from to v) 0
    -> spec = funcspec_transferFrom_4 from to v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_approve: forall msg spec env C C' E' sender spender v,
    msg = mk_msg sender (mc_approve spender v) 0
    -> spec = funcspec_approve spender v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_allowance: forall msg spec env C C' E' sender owner spender,
    msg = mk_msg sender (mc_allowance owner spender) 0
    -> spec = funcspec_allowance owner spender (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_increaseApproval: forall msg spec env C C' E' sender spender v,
    msg = mk_msg sender (mc_increaseApproval spender v) 0
    -> spec = funcspec_increaseApproval spender v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_decreaseApproval_1: forall msg spec env C C' E' sender spender v,
    msg = mk_msg sender (mc_decreaseApproval spender v) 0
    -> spec = funcspec_decreaseApproval_1 spender v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_decreaseApproval_2: forall msg spec env C C' E' sender spender v,
    msg = mk_msg sender (mc_decreaseApproval spender v) 0
    -> spec = funcspec_decreaseApproval_2 spender v (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'

| step_transferOwnership: forall msg spec env C C' E' sender new,
    msg = mk_msg sender (mc_transferOwnership new) 0
    -> spec = funcspec_transferOwnership new (w_a C) env msg
    -> func_step msg spec env C C' E'
    -> step env C msg C' E'
.

(* Evaluation step for the environment. *)
Definition env_step (env1: env) (env2: env) : Prop :=
  env_time env2 >= env_time env1 /\ env_bhash env2 <> env_bhash env1.

(* Big step *)
Definition EnvReq : Type := env -> contract -> env -> contract -> Prop.

Fixpoint steps
         (env: env)
         (C: contract)
         (ml: list message)
         (env': Model.env)
         (C': contract)
         (E: eventlist)
         (env_req: EnvReq): Prop :=
  match ml with
  | nil => C' = C /\ E = nil /\ env = env' /\ env_req env C env' C'
  | cons msg ml =>
    exists env'', exists C'', exists E'', exists E',
            step env C msg C'' E'' /\ steps env'' C'' ml env' C' E' env_req
            /\ E = E'' ++ E'
            /\ env_step env env''
            /\ env_req env C env'' C''
  end.

(* Running a smart contract c in environment env over a list of messages. *)
Definition run
           (env: env) (env_req: EnvReq)
           (C: contract) (ml: list message) (C': contract) (E: eventlist) :Prop :=
  exists env',
    steps env C ml env' C' E env_req.
