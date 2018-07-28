
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
    constructor(uint256 _initialAmount, string _name, string _symbol, uint8 _decimals, uint256 _unLockTime) public {

        require (_unLockTime >= block.timestamp);
        totalSupply = _initialAmount;
        balances[msg.sender] = _initialAmount;
        name = _name;
        symbol = _symbol;
        decimals = _decimals;
        UnLockTime = _unLockTime;
        emit Transfer(0x0, msg.sender, _initialAmount);
    }
*)
Definition funcspec_constructor (_initialAmount: uint256) (_tokenName: string) 
            (_tokenSymbol: string)(_decimalUnits: uint8)(_unLockTime: uint256) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (* No require in this function. *)
       (fun S : state => _unLockTime >= env_time env)

       (* Models an constructor event here. *)
       (fun S E => E = ((ev_constructor (m_sender msg) _initialAmount _tokenName _tokenSymbol _decimalUnits _unLockTime):: (ev_Transfer (m_sender msg) 0  (m_sender msg) _initialAmount) :: nil))

       (* State transition: *)
       (fun S S' : state =>                  
       (* totalSupply = _initialAmount;                        // Update total supply *)
          st_totalSupply S' = _initialAmount /\
       (* Name = _tokenName;                                   // Set the name for display purposes *)
          st_name S' = _tokenName /\
       (* decimals = _decimalUnits;                            // Amount of decimals for display purposes *)
          st_decimals S' = _decimalUnits /\
       (* symbol = _tokenSymbol;                               // Set the symbol for display purposes *)
          st_symbol S' =  _tokenSymbol /\
       (* balances[msg.sender] = _initialAmount;               // Give the creator all initial tokens *)
          st_balances S' = $0 $+ {m_sender msg <- _initialAmount} /\
       (* Init to all zero. *)
          st_allowed S' = $0 /\
       (* st_owner = msg.sender *)
          st_owner S' = (m_sender msg) /\
       (* UnLockTime = _unLockTime *)
          st_unLockTime S'= _unLockTime
       )
    ).

(*
function name() public view returns (string){
   return name;
}
 *)
Definition funcspec_name :=
  fun (this: address)(env: env)(msg: message) =>
    (mk_spec
        (* No require in this function. *)
       (fun S : state => True)
       
        (* return name; *)
       (fun S E => E = (ev_return _ (st_name S)) :: nil)

       (* Unchanged. *)
       (fun S S' : state => S = S')  
    ).

(*
    function symbol() public view returns (string){
        return symbol;
    }
*)
Definition funcspec_symbol :=
    fun (this: address)(env: env)(msg: message) =>
    (mk_spec
        (* No require in this function. *)
       (fun S : state => True)
       
        (* return name; *)
       (fun S E => E = (ev_return _ (st_symbol S)) :: nil)

       (* Unchanged. *)
       (fun S S' : state => S = S')  
    ).

(*
function decimals() public view returns (uint8){
   return decimals;
}
 *)
Definition funcspec_decimals :=
    fun (this: address)(env: env)(msg: message) =>
    (mk_spec
        (* No require in this function. *)
       (fun S : state => True)
       
        (* return name; *)
       (fun S E => E = (ev_return _ (st_decimals S)) :: nil)

       (* Unchanged. *)
       (fun S S' : state => S = S')  
    ).

(*
function totalSupply() public view returns (uint256){
        return totalSupply;
    }
*)
Definition funcspec_totalSupply :=
  fun (this: address)(env: env)(msg:message) =>
    (mk_spec
       (* No require in this function. *)
       (fun S : state => True)
       
        (* return totalSupply_; *)
       (fun S E => E = (ev_return _ (st_totalSupply S)) :: nil)

       (* Unchanged. *)
       (fun S S' : state => S = S')  
    ).

(*
    function balanceOf(address _owner) public view returns (uint256){
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
function transfer(address _to, uint256 _value) isUnLocked public returns (bool success){
        require (balances[_to] + _value >= balances[_to]);
        require (balances[msg.sender] >= _value);
        balances[_to] = balances[_to] + _value;
        balances[msg.sender] = balances[_to] + _value;
        emit Transfer(msg.sender, _to, _value);
        return true;
    }
*)
Definition funcspec_transfer
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
            (* block.timestamp > UnLockTime *)
           (env_time env >= st_unLockTime S /\
            (*  balances[msg.sender]>= _value *)
            st_balances S (m_sender msg ) >= value /\
            (* balances[_to] + _value <= MAX_UINT256 *)
           (st_balances S to <= MAX_UINT256 - value)))

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
          /\ st_allowed S' = st_allowed S
          /\ st_owner S' =  st_owner S
          /\ st_unLockTime S' = st_unLockTime S
       )
    ).


(*
    function transferFrom(address _from, address _to, uint256 _value) isUnLocked public returns (bool success){
        uint256 allowance = allowed[_from][msg.sender];
        require (balances[_to] + _value >= balances[_to]);
        require (balances[_from] >= _value);
        require (allowance >= _value);
        balances[_to] = balances[_to] + _value;
        balances[_from] = balances[_from] - _value;
       
        if (allowance < MAX_UINT256) {
            allowed[_from][msg.sender] = allowed[_from][msg.sender] - _value;
        }
        emit Transfer(_from, _to, _value);
        return true;
    }
*)
Definition funcspec_transferFrom_1
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
        (* block.timestamp > UnLockTime *)
       env_time env >= st_unLockTime S /\
       (* _value <= balances[_from] *)
         st_balances S from >= value /\
       (* balances[_to] + _value <= MAX_UINT256 *)
         st_balances S to <= MAX_UINT256 - value /\
        (* _value <= allowed[_from][msg.sender] *)
         st_allowed S (from, m_sender msg) >= value /\
       st_allowed S (from, m_sender msg) < MAX_UINT256)
       
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
          st_allowed S' = (st_allowed S) $+{ from, (m_sender msg) <-  -= value} /\
          st_owner S' = st_owner S /\
          st_unLockTime S' = st_unLockTime S
           
       )
    ).

Definition funcspec_transferFrom_2
           (from: address)
           (to: address)
           (value: value) :=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
        (* block.timestamp > UnLockTime *)
       env_time env >= st_unLockTime S /\
       (* _value <= balances[_from] *)
         st_balances S from >= value /\
       (* balances[_to] + _value <= MAX_UINT256 *)
         st_balances S to <= MAX_UINT256 - value /\
        (* _value <= allowed[_from][msg.sender] *)
         st_allowed S (from, m_sender msg) >= value /\
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
       (* allowed[_from][msg.sender] -= _value; *)
          st_allowed S' = st_allowed S /\
          st_owner S' = st_owner S /\
          st_unLockTime S' = st_unLockTime S
           
       )
    ).

(*
 function approve(address _spender, uint256 _value) isUnLocked public returns (bool){
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
       (* block.timestamp > UnLockTime *)
       (fun S : state => (env_time env >= st_unLockTime S))

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
          st_allowed S' = (st_allowed S) $+{ m_sender msg, spender <- value} /\
          st_owner S' = st_owner S /\
          st_unLockTime S' = st_unLockTime S
       )
    ).

(*
function allowance(address _owner, address _spender) public view returns (uint256){
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

(*
function increaseApproval(address _spender, uint _addedValue) isUnLocked public returns (bool) {
        
        require (allowed[msg.sender][_spender]+ _addedValue >= allowed[msg.sender][_spender]);
        allowed[msg.sender][_spender] = allowed[msg.sender][_spender]+ _addedValue;
        emit Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
        return true;
    }
 *)
Definition funcspec_increaseApproval (spender: address)(addValue: value):=
  fun (this: address) (env: env) (msg: message) =>
    (mk_spec
       (fun S : state =>
           (* block.timestamp > UnLockTime *)
          (env_time env >= st_unLockTime S /\
           st_allowed S (m_sender msg , spender) + addValue <= MAX_UINT256)
        )
       
       (* emit Approval(msg.sender, _spender, _value); *)
       (* return True; *)
       (fun S E => E = (ev_Approval (m_sender msg) (m_sender msg) spender (st_allowed S (m_sender msg, spender) )) :: (ev_return _ True) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
          st_balances S' = st_balances S /\
       (* allowed[msg.sender][_spender] = _value; *)
          st_allowed S' = (st_allowed S) $+{ m_sender msg, spender <- += addValue} /\
          st_owner S' = st_owner S /\
          st_unLockTime S' = st_unLockTime S
       )
    ).

(*
function decreaseApproval(address _spender, uint _subtractedValue) isUnLocked public returns (bool success) {
        
        uint oldValue = allowed[msg.sender][_spender];
        if (_subtractedValue > oldValue) {
            allowed[msg.sender][_spender] = 0;
        } else {
            allowed[msg.sender][_spender] = oldValue - _subtractedValue;
        }
        emit Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
        return true;
    }
 *)
Definition funcspec_decreaseApproval_1 (spender: address)(subValue: value) :=
  fun (this: address)(env: env)(msg: message) =>
    (mk_spec
       (* !stopped  *)
       (fun S : state =>
          (* block.timestamp > UnLockTime *)
          (env_time env >= st_unLockTime S /\
           (st_allowed S (m_sender msg, spender ) < subValue)))
                          
       (* emit Approval(msg.sender, _spender, 0); *)
       (* return True; *)
       (fun S E => E = (ev_Approval (m_sender msg) (m_sender msg) spender 0) :: (ev_return _ True) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
          st_balances S' = st_balances S /\
          (* allowed[msg.sender][_spender] = 0; *)
          st_allowed S' = (st_allowed S) $+{ m_sender msg, spender <- 0} /\
          st_owner S' = st_owner S /\
          st_unLockTime S' = st_unLockTime S
       ) 
  ).

Definition funcspec_decreaseApproval_2 (spender: address)(subValue: value) :=
  fun (this: address)(env: env)(msg: message) =>
    (mk_spec
       (* !stopped  *)
       (fun S : state =>  (* block.timestamp > UnLockTime *)
          (env_time env >= st_unLockTime S /\
              (st_allowed S (m_sender msg, spender ) >= subValue)))
                          
       (* emit Approval(msg.sender, _spender, 0); *)
       (* return True; *)
       (fun S E => E = (ev_Approval (m_sender msg) (m_sender msg) spender (st_allowed S (m_sender msg, spender))) :: (ev_return _ True) :: nil)

       (* State transition: *)
       (fun S S' : state =>
       (* Unchanged. *)
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
          st_balances S' = st_balances S /\
          (* allowed[msg.sender][_spender] = 0; *)
          st_allowed S' = (st_allowed S) $+{ m_sender msg, spender <- -= subValue } /\
          st_owner S' = st_owner S /\
           st_unLockTime S' = st_unLockTime S
       ) 
    ).

(*
funcspec transferOwnership(address newOwner){
    requir: msg.sender = owner and newOwner != address(0)
    {
        pre: True
        event: @OwnershipTransferred(owner, newOwner)
        post: owner' = newOwner
    }
}
*)
Definition funcspec_transferOwnership (newOwner: address) :=
  fun (this: address)(env: env)(msg: message) =>
    (mk_spec
       (* msg.sender = owner and newOwner != address(0) *)
       (fun S : state => (m_sender msg = st_owner S) /\ (newOwner <> 0))
       (* emit OwnershipTransferred(owner, newOwner); *)
       (fun S E => E = (ev_OwnershipTransferred (st_owner S) newOwner):: nil)
       (* State transition: *)
       (fun S S': state =>
          st_totalSupply S' = st_totalSupply S /\
          st_name S' = st_name S /\
          st_decimals S' = st_decimals S /\
          st_symbol S' = st_symbol S /\
          st_balances S' = st_balances S /\
          st_allowed S' =  st_allowed S /\
          st_owner S' = newOwner /\
           st_unLockTime S' = st_unLockTime S
       )
    ).
  

(* Constructor invocation. *)
Inductive create : env -> message -> contract -> eventlist -> Prop :=
  | create_Constructor : forall env msg S C E sender _initialAmount _tokenName _tokenSymbol _decimalUnits _unLockTime spec preP evP postP,
      msg = mk_msg sender (mc_constructor _initialAmount _tokenName _tokenSymbol _decimalUnits _unLockTime) 0
      -> spec = funcspec_constructor _initialAmount _tokenName _tokenSymbol _decimalUnits _unLockTime (w_a C) env msg
      -> _initialAmount <= MAX_UINT256
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> evP S E /\ postP S (w_st C)
      -> create env msg C E.

(* Evaluation step: any of the possible invocations. *)
Inductive step : env -> contract -> message -> contract -> eventlist -> Prop :=
  | step_totalSupply: forall env sender msg spec C C' E' preP evP postP,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_totalSupply) 0
      -> spec = funcspec_totalSupply  (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'                    

  | step_transfer: forall env msg C C' E' sender  to v spec preP evP postP,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_transfer to v) 0
      -> spec = funcspec_transfer to v (w_a C) env msg
      -> preP = spec_require spec
      -> evP = spec_events spec
      -> postP = spec_trans spec
      -> preP (w_st C) /\ evP (w_st C) E' /\ postP (w_st C) (w_st C')
      -> step env C msg C' E'
  
  | step_balanceOf : forall env sender msg owner spec C C' E' ,
      w_a C = w_a C'
      -> msg = mk_msg sender (mc_balanceOf owner) 0
      -> spec = funcspec_balanceOf owner (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
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

  | step_increaseApproval: forall env sender msg spender addValue spec C C' E',
       w_a C = w_a C'
      -> msg = mk_msg sender (mc_approve spender addValue) 0
      -> spec = funcspec_increaseApproval spender addValue (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
      -> step env C msg C' E'
  
  | step_decreaseApproval_1: forall env sender msg spender subValue spec C C' E',
       w_a C = w_a C'
      -> msg = mk_msg sender (mc_approve spender subValue) 0
      -> spec = funcspec_decreaseApproval_1 spender subValue (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
      -> step env C msg C' E'

  |  step_decreaseApproval_2: forall env sender msg spender subValue spec C C' E',
       w_a C = w_a C'
      -> msg = mk_msg sender (mc_approve spender subValue) 0
      -> spec = funcspec_decreaseApproval_2 spender subValue (w_a C) env msg
      -> (spec_require spec) (w_st C) /\ (spec_events spec) (w_st C) E' /\ (spec_trans spec) (w_st C) (w_st C')
      -> step env C msg C' E'

  | step_transferOwnership: forall env sender msg newOwner spec C C' E',
      w_a C = w_a C'
     -> msg = mk_msg sender (mc_OwnershipTransferred newOwner) 0
     -> spec = funcspec_transferOwnership newOwner (w_a C) env msg
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
