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

(*
  This specification follows the smart contract as implemented in
    https://github.com/ConsenSys/Tokens/blob/master/contracts/eip20/EIP20.sol
*)

(*
    constructor(
        uint256 _initialAmount,
        string _tokenName,
        uint8 _decimalUnits,
        string _tokenSymbol
    ) public {
        balances[msg.sender] = _initialAmount;               // Give the creator all initial tokens
        totalSupply = _initialAmount;                        // Update total supply
        name = _tokenName;                                   // Set the name for display purposes
        decimals = _decimalUnits;                            // Amount of decimals for display purposes
        symbol = _tokenSymbol;                               // Set the symbol for display purposes
    }
 *)
Definition funcspec_EIP20
           (_initialAmount: uint256)
           (_tokenName: string)
           (_decimalUnits: uint8)
           (_tokenSymbol: string) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (* No require in this function. *)
       (fun S : state => True)

       (* Models an EIP20 event here. *)
       (fun S E => E = ev_EIP20 (m_sender msg) _initialAmount _tokenName _decimalUnits _tokenSymbol :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* totalSupply = _initialAmount;                        // Update total supply *)
          st_totalSupply S' = _initialAmount /\
       (* name = _tokenName;                                   // Set the name for display purposes *)
          st_name S' = _tokenName /\
       (* decimals = _decimalUnits;                            // Amount of decimals for display purposes *)
          st_decimals S' = _decimalUnits /\
       (* symbol = _tokenSymbol;                               // Set the symbol for display purposes *)
          st_symbol S' = _tokenSymbol /\
       (* balances[msg.sender] = _initialAmount;               // Give the creator all initial tokens *)
          st_balances S' = $0 $+ {m_sender msg <- _initialAmount } /\
       (* Init to all zero. *)
          st_allowed S' = $0
       )
    ).

(*
    function transfer(
        address _to,
        uint256 _value
    ) public returns (bool) {
        require(balances[msg.sender] >= _value);
        require(msg.sender == _to || balances[_to] <= MAX_UINT256 - _value);
        balances[msg.sender] -= _value;
        balances[_to] += _value;
        emit Transfer(msg.sender, _to, _value);
        return true;
    }
*)
Definition funcspec_transfer
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (* require(balances[msg.sender] >= _value); *)
       (fun S : state =>
          (st_balances S (m_sender msg )) >= value /\
       (* require(msg.sender == _to || balances[_to] <= MAX_UINT256 - _value); *)
          ((m_sender msg = to) \/ (m_sender msg <> to /\ st_balances S to <= MAX_UINT256 - value)))

       (* emit Transfer(msg.sender, _to, _value); *)
       (* return True; *)
       (fun S E => E = (ev_Transfer (m_sender msg) (m_sender msg) to value) :: (ev_return _ True) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
       (* balances[msg.sender] -= _value; *)
          st_balances S' = (st_balances S) $+{ (m_sender msg) <- -= value }
       (* balances[_to] += _value; *)
                                           $+{ to <- += value }
       (* Unchanged. *)
          /\ st_allowed S' = st_allowed S)

    ).

(*
    function transferFrom(
        address _from,
        address _to,
        uint256 _value
    ) public returns (bool) {
        uint256 allowance = allowed[_from][msg.sender];
        require(balances[_from] >= _value);
        require(_from == _to || balances[_to] <= MAX_UINT256 -_value);
        require(allowance >= _value);
        balances[_from] -= _value;
        balances[_to] += _value;
        if (allowance < MAX_UINT256) {
            allowed[_from][msg.sender] -= _value;
        }
        emit Transfer(_from, _to, _value);
        return true;
    }

  Case 1: if condition taking true branch.
*)
Definition funcspec_transferFrom_1
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
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
       (fun S E => E = (ev_Transfer (m_sender msg) from to value) :: (ev_return _ True) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
       (* balances[_from] -= _value; *)
          st_balances S' = (st_balances S) $+{ from <- -= value }
       (* balances[_to] += _value; *)
                                           $+{ to <- += value } /\
       (* allowed[_from][msg.sender] -= _value; *)
          st_allowed S' = (st_allowed S) $+{ from, m_sender msg <- -= value }
       )
    ).

(* Case 2: if condition taking true branch. *)
Definition funcspec_transferFrom_2
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec

       (fun S : state =>
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
       (fun S E => E = (ev_Transfer (m_sender msg) from to value) :: (ev_return _ True) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
       (* balances[_from] -= _value; *)
          st_balances S' = (st_balances S) $+{ from <- -= value }
       (* balances[_to] += _value; *)
                                           $+{ to <- += value } /\
       (* Unchanged. *)
          st_allowed S' = st_allowed S
       )
    ).

(*
    function balanceOf(
        address _owner
    ) public view returns (uint256) {
        return balances[_owner];
    }
*)
Definition funcspec_balanceOf
           (owner: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (* No requirement *)
       (fun S : state => True)

       (* return balances[_owner]; *)
       (fun S E => E = (ev_return _ (st_balances S owner)) :: nil)

       (* Unchanged. *)
       (fun S S' : state => S = S')
    ).

(*
    function approve(
        address _spender,
        uint256 _value
    ) public returns (bool) {
        allowed[msg.sender][_spender] = _value;
        emit Approval(msg.sender, _spender, _value);
        return true;
    }
*)
Definition funcspec_approve
           (spender: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (* No requirement *)
       (fun S : state => True)

       (* emit Approval(msg.sender, _spender, _value); *)
       (* return True; *)
       (fun S E => E = (ev_Approval (m_sender msg) (m_sender msg) spender value) :: (ev_return _ True) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
          st_balances S' = st_balances S /\
       (* allowed[msg.sender][_spender] = _value; *)
          st_allowed S' = (st_allowed S) $+{ m_sender msg, spender <- value}
       )
    ).

(*
    function allowance(
        address _owner,
        address _spender
    ) public view returns (uint256) {
        return allowed[_owner][_spender];
    }
*)
Definition funcspec_allowance (owner: address) (spender: address) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (* No requirement *)
       (fun S : state => True)

       (* return allowed[_owner][_spender]; *)
       (fun S E => E = (ev_return _ (st_allowed S (owner, spender))) :: nil)

       (* Unchanged. *)
       (fun S S' : state => S' = S)
    ).


(* Constructor invocation. *)
Inductive create : env -> message -> contract -> eventlist -> Prop :=
  | create_EIP20 : forall env msg S C E sender ia name dec sym spec preP evP postP,
      msg = mk_msg sender (mc_EIP20 ia name dec sym) 0
      -> spec = funcspec_EIP20 ia name dec sym (w_a C) env msg
      -> ia <= MAX_UINT256
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> evP S E /\ postP S (w_st C)
      -> create env msg C E.

(* Evaluation step: any of the possible invocations. *)
Inductive step : env -> contract -> message -> contract -> eventlist -> Prop :=

  | step_transfer: forall env msg C C' E' sender  to v spec preP evP postP,
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

  | step_balanceOf : forall env sender msg owner spec C C' E' ,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_balanceOf owner) 0
      -> spec = funcspec_balanceOf owner (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
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
.

(* Evaluation step for the environment. *)
Definition env_step (env1: env) (env2: env) : Prop :=
  env_time env2 >= env_time env1 /\ env_bhash env2 <> env_bhash env1.

(* Big step *)
Fixpoint steps (env: env) (C: contract) (ml: list message) (env': Model.env) (C': contract) (E: eventlist) :Prop :=
  match ml with
    | nil => C' = C /\ E = nil /\ env = env'
    | cons msg ml => exists env'', exists C'', exists E'', exists E',
                    step env C msg C'' E'' /\ steps env'' C'' ml env' C' E'
                    /\ E = E'' ++ E'
                    /\ env_step env env''
  end.

(* Running a smart contract c in environment env over a list of messages. *)
Definition run (env: env) (C: contract) (ml: list message) (C': contract) (E: eventlist) :Prop :=
  exists env',
    steps env C ml env' C' E.
