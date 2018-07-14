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

Require Export Model.
Require Export Lists.List.

(*
  A specification of a function consists of:
    1) [spec_require] requirements via the `require()` calls
    2) [spec_events ] events generated via event calls
    3) [spec_trans  ] state transition done by the function
*)
Record Spec: Type :=
  mk_spec {
      spec_require: state -> Prop;
      spec_events: state -> eventlist -> Prop;
      spec_trans: state -> state -> Prop
    }.

Definition funcspec_PausableToken (ia: uint256) (name: string) (dec: uint8) (sym: string) :=
  fun (this: address)(env: env)(msg: message) =>
    (mk_spec
       (fun S: state => ia <=  MAX_UINT256)
       (fun S E => E = (ev_PausableToken this ia name dec sym)::nil)
       (fun S S': state => st_totalSupply S' = ia
                           /\ st_balances S' = $0 $+{(m_sender msg) <- ia}
                           /\ st_symbol S' = sym
                           /\ st_name S' = name
                           /\ st_decimals S' = dec
                           /\ st_allowed S' = $0
                           /\ st_paused S' = false
                           /\ st_owner S' = m_sender msg
       )
    ).

Definition funcspec_totalSupply :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S: state => True)
       (fun S E => E = (ev_return _ (st_totalSupply S)) :: nil)
       (fun S S': state => S = S')
    ).

Definition funcspec_balanceOf (owner: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S: state => True)
       (fun S E => E=((ev_return _ (st_balances S owner)) :: nil))
       (fun S S':state => S = S')
    ).

Definition funcspec_transfer(to: address)(value: value):=
  fun (this: address) (env: env) (msg: message) =>
    (
      mk_spec
        (fun S: state =>
           (st_paused S) = false /\
           (st_balances S (m_sender msg )) >= value /\
           ((m_sender msg = to) \/ (m_sender msg <> to /\ st_balances S to <= MAX_UINT256 - value)))
        (fun S E => E = (ev_Transfer (m_sender msg) (m_sender msg) to value)::(ev_return _ true)::nil)
        (fun S S': state =>st_totalSupply S = st_totalSupply S'
                           /\ st_symbol S' = st_symbol S
                           /\ st_name S' = st_name S
                           /\ st_decimals S' = st_decimals S
                           /\ st_allowed S' = st_allowed S
                           /\ st_balances S' =  (st_balances S) $+{(m_sender msg) <- -= value } $+{ to <-  += value }
                           /\ st_owner S' = st_owner S
                           /\ st_paused S' = st_paused S)
    ).

Definition funcspec_transferFrom_1
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
       (* require(paused == false); *)
          st_paused S = false /\
       (* require(balances[_from] >= _value); *)
          st_balances S from >= value /\
       (* require(_from == _to || balances[_to] <= MAX_UINT256 - _value); *)
          ((from = to) \/ (from <> to /\ st_balances S to <= MAX_UINT256 - value)) /\
       (* require(allowance >= _value); *)
          st_allowed S (from, m_sender msg) >= value /\
       (* allowance < MAX_UINT256 *)
          st_allowed S (from, m_sender msg) < MAX_UINT256
       )

       (* emit Transfer(_from, _to, _value); *)
       (* return True; *)
       (fun S E => E = (ev_Transfer (m_sender msg) from to value) :: (ev_return _ true) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
          st_paused S' = st_paused S /\
          st_owner S' = st_owner S /\
       (* balances[_from] -= _value; *)
          st_balances S' = (st_balances S) $+{ from <- -= value }
       (* balances[_to] += _value; *)
                                           $+{ to <- += value } /\
       (* allowed[_from][msg.sender] -= _value; *)
          st_allowed S' = (st_allowed S) $+{ from, m_sender msg <- -= value }
       )
    ).

Definition funcspec_transferFrom_2
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
       (* require(paused == false); *)
          st_paused S = false /\
       (* require(balances[_from] >= _value); *)
          st_balances S from >= value /\
       (* require(_from == _to || balances[_to] <= MAX_UINT256 - _value); *)
          ((from = to) \/ (from <> to /\ st_balances S to <= MAX_UINT256 - value)) /\
       (* require(allowance >= _value); *)
          st_allowed S (from, m_sender msg) >= value /\
       (* allowance = MAX_UINT256 *)
          st_allowed S (from, m_sender msg) = MAX_UINT256)

       (* emit Transfer(_from, _to, _value); *)
       (* return True; *)
       (fun S E => E = (ev_Transfer (m_sender msg) from to value) :: (ev_return _ true) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
          st_paused S' = st_paused S /\
          st_owner S' = st_owner S /\
       (* balances[_from] -= _value; *)
          st_balances S' = (st_balances S) $+{ from <- -= value }
       (* balances[_to] += _value; *)
                                           $+{ to <- += value } /\
       (* Unchanged. *)
          st_allowed S' = st_allowed S
       )
    ).

Definition funcspec_approve
           (spender: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (* No requirement *)
       (fun S : state => st_paused S = false)

       (* emit Approval(msg.sender, _spender, _value); *)
       (* return True; *)
       (fun S E => E = (ev_Approval (m_sender msg) (m_sender msg) spender value) :: (ev_return _ true) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
          st_balances S' = st_balances S /\
          st_paused S' = st_paused S /\
          st_owner S' = st_owner S /\
       (* allowed[msg.sender][_spender] = _value; *)
          st_allowed S' = (st_allowed S) $+{ m_sender msg, spender <- value}
       )
    ).

Definition funcspec_allowance
           (owner: address)
           (spender: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S: state => True)
       (fun S E => E = ((ev_return _ (st_allowed S (owner,spender)))::nil))
       (fun S S': state => S = S')
    ).

Definition funcspec_increaseApproval
           (spender: address)
           (addValue: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S: state => st_paused S = false /\
                        st_allowed S (m_sender msg, spender) <= MAX_UINT256 - addValue)

       (fun S E => E = (ev_Approval (m_sender msg) (m_sender msg) spender
                                    (st_allowed S (m_sender msg,spender)))
                         :: (ev_return _ true) :: nil)

       (fun S S': state =>
          st_symbol S' = st_symbol S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_totalSupply S' = st_totalSupply S /\
          st_balances S' = st_balances S /\
          st_allowed S' = st_allowed S $+ { m_sender msg, spender <- += addValue} /\
          st_paused S' = st_paused S /\
          st_owner S' = st_owner S)
    ).

Definition funcspec_decreaseApproval_1
           (spender: address)
           (decValue: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S: state =>
          st_paused S = false /\
          (st_allowed S) (m_sender msg, spender) < decValue)

       (fun S E => E = (ev_Approval (m_sender msg) (m_sender msg) spender 0)
                         :: (ev_return _ true) :: nil)

       (fun S S': state =>
          st_symbol S' = st_symbol S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_totalSupply S' = st_totalSupply S /\
          st_balances S' = st_balances S /\
          st_allowed S' = st_allowed S $+ { m_sender msg, spender <- 0} /\
          st_paused S' = st_paused S /\
          st_owner S' = st_owner S)
    ).


Definition funcspec_decreaseApproval_2
           (spender: address)
           (decValue: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S: state =>
          st_paused S = false /\
          (st_allowed S) (m_sender msg, spender) >= decValue)

       (fun S E => E = (ev_Approval (m_sender msg) (m_sender msg) spender
                                    (st_allowed S (m_sender msg, spender)))
                         :: (ev_return _ true) :: nil)

       (fun S S': state =>
          st_symbol S' = st_symbol S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_totalSupply S' = st_totalSupply S /\
          st_balances S' = st_balances S /\
          st_allowed S' = st_allowed S $+ { m_sender msg, spender <- -= decValue} /\
          st_paused S' = st_paused S /\
          st_owner S' = st_owner S)
    ).

Definition funcspec_pause :=
  fun (this: address) (env: env) (msg: message) =>
    (
      mk_spec
        (fun S: state => st_paused S = false /\ st_owner S = m_sender msg)

        (fun S E => E = ev_Pause :: nil)

        (fun S S':state =>
          st_symbol S' = st_symbol S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_totalSupply S' = st_totalSupply S /\
          st_balances S' = st_balances S /\
          st_allowed S' = st_allowed S /\
          st_paused S' = true /\
          st_owner S' = st_owner S)
    ).

Definition funcspec_unpause :=
  fun (this: address)(env: env)(msg: message) =>
    (
      mk_spec
        (fun S: state => st_paused S = true /\ st_owner S = m_sender msg)

        (fun S E => E = ev_Unpause :: nil)

        (fun S S':state =>
          st_symbol S' = st_symbol S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_totalSupply S' = st_totalSupply S /\
          st_balances S' = st_balances S /\
          st_allowed S' = st_allowed S /\
          st_paused S' = false /\
          st_owner S' = st_owner S)
    ).

Inductive create : env -> contract -> eventlist -> Prop :=
  | create_BasicToken : forall env msg S C E sender ia name dec sym spec preP evP postP,
      msg = mk_msg sender (mc_PausableToken ia name dec sym) 0
      -> spec = funcspec_PausableToken ia name dec sym (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP S E /\ postP S (w_st C)
      -> create env C E.

Inductive step : env -> contract -> message -> contract -> eventlist -> Prop :=
  | step_transfer: forall env msg C C' E' sender to v spec preP evP postP,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_transfer to v) 0
      -> spec = funcspec_transfer to v (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_transferFrom_1 : forall env sender msg from to v spec C C' E' ,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_transferFrom from to v) 0
      -> spec = funcspec_transferFrom_1 from to v (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_transferFrom_2 : forall env sender msg from to v spec C C' E' ,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_transferFrom from to v) 0
      -> spec = funcspec_transferFrom_2 from to v (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_balanceOf : forall env sender msg owner spec C C' E' preP evP postP,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_balanceOf owner) 0
      -> spec = funcspec_balanceOf owner (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_approve : forall env sender msg spender v spec C C' E' ,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_approve spender v) 0
      -> spec = funcspec_approve spender v (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_allowance : forall env sender msg owner spender spec C C' E' ,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_allowance owner spender) 0
      -> spec = funcspec_allowance owner spender (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_totalSupply: forall env msg C C' E' sender spec preP evP postP,
      w_a C = w_a C'
      -> msg = mk_msg sender mc_totalSupply 0
      -> spec = funcspec_totalSupply (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_increaseApproval: forall env msg C C' E' sender spec preP evP postP spender value,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_increaseApproval spender value) 0
      -> spec = funcspec_increaseApproval spender value (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_decreaseApproval_1: forall env msg C C' E' sender spec preP evP postP spender value,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_decreaseApproval spender value) 0
      -> spec = funcspec_decreaseApproval_1 spender value (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_decreaseApproval_2: forall env msg C C' E' sender spec preP evP postP spender value,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_decreaseApproval spender value) 0
      -> spec = funcspec_decreaseApproval_2 spender value (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_pause: forall env msg C C' E' sender spec preP evP postP,
      w_a C = w_a C'
      -> msg = mk_msg sender mc_pause 0
      -> spec = funcspec_pause (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_unpause: forall env msg C C' E' sender spec preP evP postP,
      w_a C = w_a C'
      -> msg = mk_msg sender mc_unpause 0
      -> spec = funcspec_unpause (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'
.

Definition env_step (env1: env) (env2: env) : Prop :=
  env_time env2 >= env_time env1
  /\ env_bhash env2 <> env_bhash env1.

Fixpoint steps (env: env) (C: contract) (ml: list message) (env': Model.env) (C': contract) (E: eventlist) :Prop :=
  match ml with
    | nil => C' = C /\ E = nil /\ env = env'
    | cons msg ml => exists env'', exists C'', exists E'', exists E',
                    step env C msg C'' E'' /\ steps env'' C'' ml env' C' E'
                    /\ E = E'' ++ E'
                    /\ env_step env env''
  end.

Definition run (env: env) (C: contract) (ml: list message) (C': contract) (E: eventlist) :Prop :=
  exists env',
    steps env C ml env' C' E.
