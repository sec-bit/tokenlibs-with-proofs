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

From Coq Require Import
     Arith
     List
     Nat
     String.
Import ListNotations.

From ExtLib Require Import
     Applicative
     Functor
     Monad
     MonadState
     StateMonad.
Import ApplicativeNotation FunctorNotation MonadNotation.
Open Scope monad_scope.

(* XXX: shall Model.event and .state be generated from solidity? *)
From proof Require Import Model.

(* All notations are defined in dsl_scope. *)
Delimit Scope dsl_scope with dsl.

(* *************** *)
(* DSL definitions *)
(* *************** *)

Definition State := StateMonad.state state.

Inductive Stmt :=
  DSL_require (cond: env -> message -> State bool)
| DSL_emit (evt: env -> message -> State event)
| DSL_balances_upd_inc (addr: env -> message -> State address)
                       (expr: env -> message -> State uint256)
| DSL_balances_upd_dec (addr: env -> message -> State address)
                       (expr: env -> message -> State uint256)
| DSL_balances_upd (addr: env -> message -> State address)
                   (expr: env -> message -> State uint256)
| DSL_allowed_upd_inc (from: env -> message -> State address)
                      (to: env -> message -> State address)
                      (expr: env -> message -> State uint256)
| DSL_allowed_upd_dec (from: env -> message -> State address)
                      (to: env -> message -> State address)
                      (expr: env -> message -> State uint256)
| DSL_allowed_upd (from: env -> message -> State address)
                  (to: env -> message -> State address)
                  (expr: env -> message -> State uint256)
| DSL_totalSupply_upd (expr: env -> message -> State uint256)
| DSL_name_upd (expr: env -> message -> State string)
| DSL_decimals_upd (expr: env -> message -> State uint8)
| DSL_symbol_upd (expr: env -> message -> State string)
| DSL_return (T: Type) (expr: env -> message -> State T)
| DSL_ctor
| DSL_nop
| DSL_if (cond: env -> message -> State bool) (then_stmt: Stmt) (else_stmt: Stmt)
| DSL_seq (stmt: Stmt) (stmt': Stmt).
Arguments DSL_return [T].

(* Result of statement execution *)
Definition Result := State (eventlist + eventlist).

(* Semantics of DSL statements *)
Fixpoint dsl_exec
         (stmt: Stmt)
         (st0: Model.state)
         (env: env) (msg: message) (this: address)
         (evts: eventlist) {struct stmt}: Result :=
  match stmt with
  | DSL_require cond =>
    b <- cond env msg;;
    if b
    then ret (inr evts)
    else
      put st0;;
      ret (inl [ev_revert this])
  | DSL_emit evt =>
    ev <- evt env msg;;
    ret (inr (evts ++ [ev]))
  | DSL_return expr =>
    t <- expr env msg;;
    ret (inl (evts ++ [ev_return _ t]))
  | DSL_balances_upd_inc addr expr =>
    address <- addr env msg;;
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               (st_name st)
               (st_decimals st)
               (st_totalSupply st)
               (a2v_upd_inc (st_balances st) address exp)
               (st_allowed st));;
    ret (inr evts)
  | DSL_balances_upd_dec addr expr =>
    address <- addr env msg;;
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               (st_name st)
               (st_decimals st)
               (st_totalSupply st)
               (a2v_upd_dec (st_balances st) address exp)
               (st_allowed st));;
    ret (inr evts)
  | DSL_balances_upd addr expr =>
    address <- addr env msg;;
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               (st_name st)
               (st_decimals st)
               (st_totalSupply st)
               (tmap_upd (st_balances st) address exp)
               (st_allowed st));;
    ret (inr evts)
  | DSL_allowed_upd_inc from to expr =>
    frm <- from env msg;;
    too <- to env msg;;
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               (st_name st)
               (st_decimals st)
               (st_totalSupply st)
               (st_balances st)
               (aa2v_upd_inc (st_allowed st) frm too exp));;
    ret (inr evts)
  | DSL_allowed_upd_dec from to expr =>
    frm <- from env msg;;
    too <- to env msg;;
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               (st_name st)
               (st_decimals st)
               (st_totalSupply st)
               (st_balances st)
               (aa2v_upd_dec (st_allowed st) frm too exp));;
    ret (inr evts)
  | DSL_allowed_upd from to expr =>
    frm <- from env msg;;
    too <- to env msg;;
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               (st_name st)
               (st_decimals st)
               (st_totalSupply st)
               (st_balances st)
               (aa2v_upd_2 (st_allowed st) frm too exp));;
    ret (inr evts)
  | DSL_totalSupply_upd expr =>
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               (st_name st)
               (st_decimals st)
               exp
               (st_balances st)
               (st_allowed st));;
    ret (inr evts)
  | DSL_name_upd expr =>
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               exp
               (st_decimals st)
               (st_totalSupply st)
               (st_balances st)
               (st_allowed st));;
    ret (inr evts)
  | DSL_decimals_upd expr =>
    exp <- expr env msg;;
    st <- get;;
    put (mk_st (st_symbol st)
               (st_name st)
               exp
               (st_totalSupply st)
               (st_balances st)
               (st_allowed st));;
    ret (inr evts)
  | DSL_symbol_upd expr =>
    exp <- expr env msg;;
    st <- get;;
    put (mk_st exp
               (st_name st)
               (st_decimals st)
               (st_totalSupply st)
               (st_balances st)
               (st_allowed st));;
    ret (inr evts)
  | DSL_ctor =>
    st <- get;;
    ret (inr (evts ++ [ev_EIP20 (m_sender msg)
                                (st_totalSupply st)
                                (st_name st)
                                (st_decimals st)
                                (st_symbol st)]))
  | DSL_nop => ret (inr evts)
  | DSL_if cond then_stmt else_stmt =>
    b <- cond env msg;;
    if b
    then dsl_exec then_stmt st0 env msg this evts
    else dsl_exec else_stmt st0 env msg this evts
  | DSL_seq stmt stmt' =>
    evev <- dsl_exec stmt st0 env msg this evts;;
    match evev with
    | inl evts' => ret (inl evts')
    | inr evts' =>
      dsl_exec stmt' st0 env msg this evts'
    end
  end.

(* ************************************************************** *)
(* Optional notations that makes the DSL syntax close to Solidity *)
(* ************************************************************** *)

(* Notations for state variables (XXX: shall they be generated from solidity?) *)
Notation "'symbol'" :=
  (fun (env: env) (msg: message) => st_symbol <$> get) : dsl_scope.

Notation "'name'" :=
  (fun (env: env) (msg: message) => st_name <$> get) : dsl_scope.

Notation "'decimals'" :=
  (fun (env: env) (msg: message) => st_decimals <$> get) : dsl_scope.

Notation "'totalSupply'" :=
  (fun (env: env) (msg: message) => st_totalSupply <$> get) : dsl_scope.

Notation "'balances'" :=
  (fun (env: env) (msg: message) => st_balances <$> get) : dsl_scope.

Notation "'balances' '[' addr ']'" :=
  (fun (env: env) (msg: message) =>
     balances%dsl env msg <*> addr env msg) : dsl_scope.

Notation "'allowed'" :=
  (fun (env: env) (msg: message) => st_allowed <$> get) : dsl_scope.

Notation "'allowed' '[' from ']' '[' to ']'" :=
  (fun (env: env) (msg: message) =>
     allowed%dsl env msg <*>
     (pair <$> from env msg) <*>
     to env msg) : dsl_scope.

(* Notations for events (XXX: shall they be generated from solidity?) *)
Notation "'Transfer' '(' from ',' to ',' value ')'" :=
  (fun (env: env) (msg: message) =>
     ((ev_Transfer (m_sender msg) <$> from env msg) <*> to env msg) <*> value env msg)
    (at level 210): dsl_scope.

Notation "'Approval' '(' owner ',' spender ',' value ')'" :=
  (fun (env: env) (msg: message) =>
     ((ev_Approval (m_sender msg) <$> owner env msg) <*> spender env msg) <*> value env msg)
    (at level 210): dsl_scope.

Import Model.

(* Notations for solidity expressions *)
Definition dsl_op {A B C} (op : A -> B -> C)
           (x: env -> message -> State A)
           (y: env -> message -> State B)
           (env: env) (msg: message) : State C :=
  (op <$> x env msg) <*> y env msg.

Definition dsl_lt  := dsl_op ltb.
Definition dsl_ge x y e m := negb <$> dsl_lt x y e m.
Definition dsl_le  := dsl_op ble_nat.
Definition dsl_eq  := dsl_op beq_nat.
Definition dsl_add := dsl_op add.
Definition dsl_sub := dsl_op sub.
Definition dsl_or  := dsl_op orb.

Infix "<" := dsl_lt  : dsl_scope.
Infix ">=" := dsl_ge  : dsl_scope.
Infix "<=" := dsl_le  : dsl_scope.
Infix "+" := dsl_add : dsl_scope.
Infix "-" := dsl_sub : dsl_scope.
Infix "||" := dsl_or  : dsl_scope.
Infix "==" := dsl_eq (at level 70): dsl_scope.

Notation "'msg.sender'" :=
  (fun (env: env) (msg: message) =>
     ret (m_sender msg)) : dsl_scope.

Definition otrue  : State bool := ret true.
Definition ofalse : State bool := ret false.

Notation "'true'" :=
  (fun (env: env) (msg: message) => ret True) : dsl_scope.
Notation "'false'" :=
  (fun (env: env) (msg: message) => ret False) : dsl_scope.

Notation "'require' '(' cond ')'" :=
  (DSL_require cond) (at level 200) : dsl_scope.
Notation "'emit' evt" :=
  (DSL_emit evt) (at level 200) : dsl_scope.
Notation "'balances' '[' addr ']' '+=' expr" :=
  (DSL_balances_upd_inc addr expr) (at level 0) : dsl_scope.
Notation "'balances' '[' addr ']' '-=' expr" :=
  (DSL_balances_upd_dec addr expr) (at level 0) : dsl_scope.
Notation "'balances' '[' addr ']' '=' expr" :=
  (DSL_balances_upd addr expr) (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '+=' expr" :=
  (DSL_allowed_upd_inc from to expr) (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '-=' expr" :=
  (DSL_allowed_upd_dec from to expr) (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '=' expr" :=
  (DSL_allowed_upd from to expr) (at level 0) : dsl_scope.
Notation "'totalSupply' '=' expr" :=
  (DSL_totalSupply_upd expr) (at level 0) : dsl_scope.
Notation "'symbol' '=' expr" :=
  (DSL_symbol_upd expr) (at level 0) : dsl_scope.
Notation "'name' '=' expr" :=
  (DSL_name_upd expr) (at level 0) : dsl_scope.
Notation "'decimals' '=' expr" :=
  (DSL_decimals_upd expr) (at level 0) : dsl_scope.
Notation "'return' expr" :=
  (DSL_return expr) (at level 200) : dsl_scope.
Notation "'nop'" :=
  (DSL_nop) (at level 200) : dsl_scope.
Notation "'ctor'" :=
  DSL_ctor (at level 200) : dsl_scope.

Notation "@ stmt_prim" :=
  (stmt_prim) (at level 200) : dsl_scope.

Notation "'@if' ( cond ) { stmt0 } 'else' { stmt1 }" :=
  (DSL_if cond stmt0 stmt1) (at level 210) : dsl_scope.

Notation "stmt0 ';' stmt1" :=
  (DSL_seq stmt0 stmt1) (at level 220) : dsl_scope.

Notation "'@uint256' x = expr ; stmt" :=
  (let x: env -> message -> State uint256 := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@address' x = expr ; stmt" :=
  (let x: env -> message -> State address := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@uint8' x = expr ; stmt" :=
  (let x: env -> message -> State uint8 := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@string' x = expr ; stmt" :=
  (let x: env -> message -> State string := expr in stmt)
    (at level 230, x ident) : dsl_scope.


(* *************************************************************** *)
(* Each section below represents a ERC20 function in DSL and prove *)
(* the DSL representation does implement the specification.        *)
(* *************************************************************** *)

Require Import Spec.

Section dsl_transfer_from.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{from: env -> message -> State address}.
  Context `{_from: address}.
  Context `{to: env -> message -> State address}.
  Context `{_to: address}.
  Context `{value: env -> message -> State uint256}.
  Context `{_value: uint256}.

  Context `{max_uint256: env -> message -> State uint256}.

  (* Arguments are immutable, generated from solidity *)
  Context `{from_immutable: forall st env msg, evalState (from env msg) st = _from}.
  Context `{to_immutable: forall st env msg, evalState (to env msg) st = _to}.
  Context `{value_immutable: forall st env msg, evalState (value env msg) st = _value}.
  Context `{max_uint256_immutable: forall st env msg, evalState (max_uint256 env msg) st = MAX_UINT256}.

  (* DSL representation of transferFrom(), generated from solidity *)
  Definition transferFrom_dsl : Stmt :=
    (@uint256 allowance = allowed[from][msg.sender] ;
     @require(balances[from] >= value) ;
     @require((from == to) || (balances[to] <= max_uint256 - value)) ;
     @require(allowance >= value) ;
     @balances[from] -= value ;
     @balances[to] += value ;
     @if (allowance < max_uint256) {
         (@allowed[from][msg.sender] -= value)
     } else {
         (@nop)
     } ;
     (@emit Transfer(from, to, value)) ;
     (@return true)).

  (* Auxiliary lemmas *)
  Lemma nat_nooverflow_dsl_nooverflow:
    forall (m: State a2v) st env msg,
      (_from = _to \/ (_from <> _to /\ (evalState st m _to <= MAX_UINT256 - _value)))%nat ->
      ((from == to) ||
       ((fun env msg => m <*> to env msg) <= max_uint256 - value))%dsl env msg = otrue.
  Proof. Abort.

  Close Scope dsl_scope.
End dsl_transfer_from.

Section dsl_transfer.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{to: env -> message -> State address}.
  Context `{_to: address}.
  Context `{value: env -> message -> State uint256}.
  Context `{_value: uint256}.
  Context `{max_uint256: env -> message -> State uint256}.

  (* Arguments are immutable, generated from solidity *)
  Context `{to_immutable: forall st env msg, evalState st (to env msg) = _to}.
  Context `{value_immutable: forall st env msg, evalState st (value env msg) = _value}.
  Context `{max_uint256_immutable: forall st env msg, evalState st (max_uint256 env msg) = MAX_UINT256}.

  (* DSL representation of transfer(), generated from solidity *)
  Definition transfer_dsl : Stmt :=
    (@require(balances[msg.sender] >= value) ;
     @require((msg.sender == to) || (balances[to] <= max_uint256 - value)) ;
     @balances[msg.sender] -= value ;
     @balances[to] += value ;
     (@emit Transfer(msg.sender, to, value)) ;
     (@return true)
    ).

  Close Scope dsl_scope.
End dsl_transfer.

Section dsl_balanceOf.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ owner: env -> message -> State address }.
  Context `{ _owner: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ owner_immutable: forall st env msg, evalState st (owner env msg) = _owner }.

  (* DSL representation of transfer(), generated from solidity *)
  Definition balanceOf_dsl : Stmt :=
    (@return balances[owner]).

  Close Scope dsl_scope.
End dsl_balanceOf.

Section dsl_approve.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ spender: env -> message -> State address }.
  Context `{ _spender: address }.
  Context `{ value: env -> message -> State uint256 }.
  Context `{ _value: uint256 }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ spender_immutable: forall st env msg, evalState st (spender env msg) = _spender }.
  Context `{ value_immutable: forall st env msg, evalState st (value env msg) = _value }.

  (* DSL representation of approve(), generated from solidity *)
  Definition approve_dsl : Stmt :=
    (@allowed[msg.sender][spender] = value ;
     (@emit Approval(msg.sender, spender, value)) ;
     (@return true)
    ).

  Close Scope dsl_scope.
End dsl_approve.

Section dsl_allowance.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ owner: env -> message -> State address }.
  Context `{ _owner: address }.
  Context `{ spender: env -> message -> State address }.
  Context `{ _spender: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ owner_immutable: forall st env msg, evalState st (owner env msg) = _owner }.
  Context `{ spender_immutable: forall st env msg, evalState st (spender env msg) = _spender }.

  (* DSL representation of transfer(), generated from solidity *)
  Definition allowance_dsl : Stmt :=
    (@return allowed[owner][spender]).

  Close Scope dsl_scope.
End dsl_allowance.

Section dsl_constructor.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ initialAmount : env -> message -> State uint256 }.
  Context `{ _initialAmount: uint256 }.
  Context `{ decimalUnits : env -> message -> State uint8 }.
  Context `{ _decimalUnits: uint8 }.
  Context `{ tokenName: env -> message -> State string }.
  Context `{ _tokenName: string }.
  Context `{ tokenSymbol: env -> message -> State string }.
  Context `{ _tokenSymbol: string }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ initialAmount_immutable: forall st env msg, evalState st (initialAmount env msg) = _initialAmount }.
  Context `{ decimalUnits_immutable: forall st env msg, evalState st (decimalUnits env msg) = _decimalUnits }.
  Context `{ tokenName_immutable: forall st env msg, evalState st (tokenName env msg) = _tokenName }.
  Context `{ tokenSymbol_immutable: forall st env msg, evalState st (tokenSymbol env msg) = _tokenSymbol }.

  (* DSL representation of constructor, generated from solidity *)
  Definition ctor_dsl : Stmt :=
    (@balances[msg.sender] = initialAmount ;
     @totalSupply = initialAmount ;
     @name = tokenName ;
     @decimals = decimalUnits ;
     @symbol = tokenSymbol ;
     @ctor
    ).

  Close Scope dsl_scope.
End dsl_constructor.
