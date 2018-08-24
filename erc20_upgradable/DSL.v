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

Require Import Arith.
Require Import Nat.
Require Import String.
Require Import Bool.
Open Scope string_scope.

Require Import Maps.
Require Import Types.

Set Printing Depth 120.

(* XXX: shall Model.event and .state be generated from solidity? *)
Require Import Model.

(* All notations are defined in dsl_scope. *)
Delimit Scope dsl_scope with dsl.

Delimit Scope a2v_scope with a2v.
Delimit Scope aa2v_scope with aa2v.
Delimit Scope a2b_scope with a2b.

Open Scope a2b.
Open Scope aa2v_scope.
Open Scope a2v_scope.

(* *************** *)
(* DSL definitions *)
(* *************** *)

(* Definition of DSL expressions *)

(* An expression may attempt to access storage variables of another
   contract. If that contract does not exist, or the variables do not
   exist in that contract, the access will end with a revert. Such
   cases can be modeled by Invalid of the following type. *)
Inductive ExprVal (T: Type) : Type :=
| Valid (v: T)
| Invalid.
Arguments Valid [T].
Arguments Invalid [T].

Definition Expr (T: Type) : Type :=
  address -> state -> env -> message -> ExprVal T.

(* Definition of the primitive DSL statements *)
Inductive PrimitiveStmt :=
| DSL_require (cond: Expr bool)
| DSL_emit (evt: Expr event)
| DSL_balances_upd (addr: Expr address)
                   (expr: Expr uint256)
| DSL_allowed_upd (from: Expr address)
                  (to: Expr address)
                  (expr: Expr uint256)
| DSL_totalSupply_upd (expr: Expr uint256)
| DSL_name_upd (expr: Expr string)
| DSL_decimals_upd (expr: Expr uint8)
| DSL_symbol_upd (expr: Expr string)
| DSL_owner_upd (expr: Expr address)
| DSL_oldToken_upd (expr: Expr address)
| DSL_migratedBalances_upd (addr: Expr address)
                           (expr: Expr bool)
| DSL_return (T: Type) (expr: Expr T)
| DSL_ctor
| DSL_nop
.
Arguments DSL_return [T].

(* Definition of DSL statements *)
Inductive Stmt :=
| DSL_prim (stmt: PrimitiveStmt)
| DSL_if (cond: Expr bool) (then_stmt: Stmt) (else_stmt: Stmt)
| DSL_seq (stmt: Stmt) (stmt': Stmt).

(* Result of statement execution *)
Record Result: Type :=
  mk_result {
      ret_st: state;        (* ending state *)
      ret_evts: eventlist;  (* generated events *)
      ret_stopped: bool;    (* does the execution have to stop? *)
    }.
(* Shortcut definition of Result that the execution can continue *)
Definition Next (st: state) (evts: eventlist) : Result :=
  mk_result st evts false.
(* Shortcut definition of Result that the execution has to stop *)
Definition Stop (st: state) (evts: eventlist) : Result :=
  mk_result st evts true.

(* Semantics of the primitive DSL statements *)
Fixpoint dsl_exec_prim
         (stmt: PrimitiveStmt)
         (st0: state)
         (st: state)
         (env: env) (msg: message) (this: address)
         (evts: eventlist): Result :=
  match stmt with
  | DSL_require cond =>
    match cond this st env msg with
    | Invalid     => Stop st0 (ev_revert this :: nil)
    | Valid _cond => if _cond then
                       Next st evts
                     else
                       Stop st0 (ev_revert this :: nil)
    end

  | DSL_emit evt =>
    match evt this st env msg with
    | Invalid    => Stop st0 (ev_revert this :: nil)
    | Valid _evt => Next st (evts ++ (_evt :: nil))
    end

  | DSL_return expr =>
    match expr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _expr => Stop st (evts ++ (ev_return _ _expr :: nil))
    end

  | DSL_balances_upd addr expr =>
    match addr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _addr =>
      match expr this st env msg with
      | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
      | Valid _expr => Next (mk_st (st_symbol st)
                                   (st_name st)
                                   (st_decimals st)
                                   (st_totalSupply st)
                                   (st_balances st $ { _addr <~ _expr })
                                   (st_allowed st)
                                   (st_owner st)
                                   (st_migratedBalances st)
                                   (st_oldToken st))
                            evts
      end
    end

  | DSL_allowed_upd from to expr =>
    match from this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _from =>
      match to this st env msg with
      | Invalid   => Stop st0 (evts ++ (ev_revert this :: nil))
      | Valid _to =>
        match expr this st env msg with
        | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
        | Valid _expr => Next (mk_st (st_symbol st)
                                     (st_name st)
                                     (st_decimals st)
                                     (st_totalSupply st)
                                     (st_balances st)
                                     (st_allowed st $ { _from, _to <~ _expr })
                                     (st_owner st)
                                     (st_migratedBalances st)
                                     (st_oldToken st))
                              evts
        end
      end
    end

  | DSL_totalSupply_upd expr =>
    match expr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _expr => Next (mk_st (st_symbol st)
                                 (st_name st)
                                 (st_decimals st)
                                 _expr
                                 (st_balances st)
                                 (st_allowed st)
                                 (st_owner st)
                                 (st_migratedBalances st)
                                 (st_oldToken st))
                          evts
    end

  | DSL_name_upd expr =>
    match expr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _expr => Next (mk_st (st_symbol st)
                                 _expr
                                 (st_decimals st)
                                 (st_totalSupply st)
                                 (st_balances st)
                                 (st_allowed st)
                                 (st_owner st)
                                 (st_migratedBalances st)
                                 (st_oldToken st))
                          evts
    end

  | DSL_decimals_upd expr =>
    match expr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _expr => Next (mk_st (st_symbol st)
                                 (st_name st)
                                 _expr
                                 (st_totalSupply st)
                                 (st_balances st)
                                 (st_allowed st)
                                 (st_owner st)
                                 (st_migratedBalances st)
                                 (st_oldToken st))
                          evts
    end

  | DSL_symbol_upd expr =>
    match expr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _expr => Next (mk_st _expr
                                 (st_name st)
                                 (st_decimals st)
                                 (st_totalSupply st)
                                 (st_balances st)
                                 (st_allowed st)
                                 (st_owner st)
                                 (st_migratedBalances st)
                                 (st_oldToken st))
                          evts
    end

  | DSL_owner_upd expr =>
    match expr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _expr => Next (mk_st (st_symbol st)
                                 (st_name st)
                                 (st_decimals st)
                                 (st_totalSupply st)
                                 (st_balances st)
                                 (st_allowed st)
                                 _expr
                                 (st_migratedBalances st)
                                 (st_oldToken st))
                          evts
    end

  | DSL_oldToken_upd expr =>
    match expr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _expr => Next (mk_st (st_symbol st)
                                 (st_name st)
                                 (st_decimals st)
                                 (st_totalSupply st)
                                 (st_balances st)
                                 (st_allowed st)
                                 (st_owner st)
                                 (st_migratedBalances st)
                                 _expr)
                          evts
    end

  | DSL_migratedBalances_upd addr expr =>
    match addr this st env msg with
    | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _addr =>
      match expr this st env msg with
      | Invalid     => Stop st0 (evts ++ (ev_revert this :: nil))
      | Valid _expr => Next (mk_st (st_symbol st)
                                   (st_name st)
                                   (st_decimals st)
                                   (st_totalSupply st)
                                   (st_balances st)
                                   (st_allowed st)
                                   (st_owner st)
                                   (st_migratedBalances st $ { _addr <~ _expr })%a2b
                                   (st_oldToken st))
                            evts
      end
    end

  | DSL_ctor =>
    Next st
         (evts ++ (ev_constructor (m_sender msg) (st_oldToken st) :: nil))

  | DSL_nop =>
    Next st evts
  end.

(* Semantics of DSL statements *)
Fixpoint dsl_exec
         (stmt: Stmt)
         (st0: state)
         (st: state)
         (env: env) (msg: message) (this: address)
         (evts: eventlist) {struct stmt}: Result :=
  match stmt with
  | DSL_prim stmt' =>
    dsl_exec_prim stmt' st0 st env msg this evts

  | DSL_if cond then_stmt else_stmt =>
    match cond this st env msg with
    | Invalid => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _cond =>
      if _cond then
        dsl_exec then_stmt st0 st env msg this evts
      else
        dsl_exec else_stmt st0 st env msg this evts
    end

  | DSL_seq stmt stmt' =>
    match dsl_exec stmt st0 st env msg this evts with
    | mk_result st'' evts'' stopped  =>
      if stopped then
        mk_result st'' evts'' stopped
      else
        dsl_exec stmt' st0 st'' env msg this evts''
    end
  end.

(* ************************************************************** *)
(* Optional notations that makes the DSL syntax close to Solidity *)
(* ************************************************************** *)

(* Notations for state variables (XXX: shall they be generated from solidity?) *)
Notation "'symbol'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid (st_symbol st))
    (only parsing) : dsl_scope.

Notation "'name'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid (st_name st))
    (only parsing) : dsl_scope.

Notation "'decimals'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid (st_decimals st))
    (only parsing) : dsl_scope.

Notation "'totalSupply'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid (st_totalSupply st))
    (only parsing) : dsl_scope.

Notation "'balances'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => st_balances st)
    (only parsing) : dsl_scope.

Definition dsl_balances_access (addr: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match addr this st env msg with
    | Invalid => Invalid
    | Valid _addr => Valid ((balances%dsl this st env msg) $ _addr)
    end.
Notation "'balances' '[' addr ']'" :=
  (dsl_balances_access addr) (only parsing) : dsl_scope.

Notation "'allowed'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => st_allowed st)
    (only parsing) : dsl_scope.

Definition dsl_allowed_access (from to: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match from this st env msg with
    | Invalid => Invalid
    | Valid _from =>
      match to this st env msg with
      | Invalid => Invalid
      | Valid _to => Valid ((allowed%dsl this st env msg) $ [_from, _to])
      end
    end.
Notation "'allowed' '[' from ']' '[' to ']'" :=
  (dsl_allowed_access from to) (only parsing) : dsl_scope.

Notation "'owner'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) =>  Valid (st_owner st))
    (only parsing) : dsl_scope.

Notation "'oldToken'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid (st_oldToken st))
    (only parsing) : dsl_scope.

Notation "'totalSupply'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid (st_totalSupply st))
    (only parsing) : dsl_scope.

Notation  "'migratedBalances'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => st_migratedBalances st)
    (only parsing) : dsl_scope.

Definition dsl_migratedBalances_access (addr: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match addr this st env msg with
    | Invalid => Invalid
    | Valid _addr => Valid ((migratedBalances%dsl this st env msg) $ _addr)%a2b
    end.
Notation "'migratedBalances' '[' addr ']'" :=
  (dsl_migratedBalances_access addr) (only parsing) : dsl_scope.

Definition dsl_remote_symbol_access (caddr: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match caddr this st env msg with
    | Invalid => Invalid
    | Valid _caddr =>
      match env_contract env _caddr with
      | None => Invalid
      | Some cst => Valid (ost_symbol cst)
      end
    end.
Notation "caddr '.symbol()'" :=
  (dsl_remote_symbol_access caddr)
    (at level 190, only parsing): dsl_scope.

Definition dsl_remote_name_access (caddr: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match caddr this st env msg with
    | Invalid => Invalid
    | Valid _caddr =>
      match env_contract env _caddr with
      | None => Invalid
      | Some cst => Valid (ost_name cst)
      end
    end.
Notation "caddr '.name()'" :=
  (dsl_remote_name_access caddr) (at level 190, only parsing): dsl_scope.

Definition dsl_remote_decimals_access (caddr: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match caddr this st env msg with
    | Invalid => Invalid
    | Valid _caddr =>
      match env_contract env _caddr with
      | None => Invalid
      | Some cst => Valid (ost_decimals cst)
      end
    end.
Notation "caddr '.decimals()'" :=
  (dsl_remote_decimals_access caddr) (at level 190, only parsing): dsl_scope.

Definition dsl_remote_balances_access (caddr: Expr address) (addr: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match caddr this st env msg with
    | Invalid => Invalid
    | Valid _caddr =>
      match env_contract env _caddr with
      | None => Invalid
      | Some cst =>
        match addr this st env msg with
        | Invalid => Invalid
        | Valid _addr => Valid (ost_balances cst $ _addr)
        end
      end
    end.
Notation "caddr '.balanceOf' '(' addr ')' " :=
  (dsl_remote_balances_access caddr addr) (at level 190, only parsing) : dsl_scope.

Definition dsl_remote_totalSupply_access (caddr: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match caddr this st env msg with
    | Invalid => Invalid
    | Valid _caddr =>
      match env_contract env _caddr with
      | None => Invalid
      | Some cst => Valid (ost_totalSupply cst)
      end
    end.
Notation "caddr '.totalSupply()'" :=
  (dsl_remote_totalSupply_access caddr) (at level 190, only parsing) : dsl_scope.

Definition dsl_remote_stopped_access (caddr: Expr address) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match caddr this st env msg with
    | Invalid => Invalid
    | Valid _caddr =>
      match env_contract env _caddr with
      | None => Invalid
      | Some cst => Valid (ost_stopped cst)
      end
    end.
Notation "caddr '.stopped()'" :=
  (dsl_remote_stopped_access caddr) (at level 190, only parsing): dsl_scope.

(* Notations for events (XXX: shall they be generated from solidity?) *)
Notation "'Transfer' '(' from ',' to ',' value ')'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) =>
     match from this st env msg with
     | Invalid => Invalid
     | Valid _from =>
       match to this st env msg with
       | Invalid => Invalid
       | Valid _to =>
         match value this st env msg with
         | Invalid => Invalid
         | Valid _value => Valid (ev_Transfer this _from _to _value)
         end
       end
     end)
    (at level 210, only parsing): dsl_scope.

Notation "'Approval' '(' sender ',' spender ',' value ')'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) =>
     match sender this st env msg with
     | Invalid => Invalid
     | Valid _sender =>
       match spender this st env msg with
       | Invalid => Invalid
       | Valid _spender =>
         match value this st env msg with
         | Invalid => Invalid
         | Valid _value => Valid (ev_Approval this _sender _spender _value)
         end
       end
     end)
    (at level 210, only parsing): dsl_scope.

Notation "'Migrate' '(' acct ',' value ')'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) =>
     match acct this st env msg with
     | Invalid => Invalid
     | Valid _acct =>
       match value this st env msg with
       | Invalid => Invalid
       | Valid _value => Valid (ev_Migrate (st_oldToken st) this _acct _value)
       end
     end)
    (at level 210, only parsing): dsl_scope.

Notation "'OwnershipTransferred' '(' old ',' new ')'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) =>
     match old this st env msg with
     | Invalid => Invalid
     | Valid _old =>
       match new this st env msg with
       | Invalid => Invalid
       | Valid _new => Valid (ev_OwnershipTransferred this _old _new)
       end
     end)
    (at level 210, only parsing): dsl_scope.

(* Notations for solidity expressions *)
Definition dsl_ge (x y: Expr value) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (negb (ltb _x _y))
      end
    end.
Infix ">=" := dsl_ge (only parsing) : dsl_scope.

Definition dsl_lt (x y: Expr value) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (ltb _x _y)
      end
    end.
Infix "<" := dsl_lt (only parsing) : dsl_scope.

Definition dsl_le (x y: Expr value) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (Nat.leb _x _y)
      end
    end.
Infix "<=" := dsl_le (only parsing) : dsl_scope.

Definition dsl_eq (x y: Expr value) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (Nat.eqb _x _y)
      end
    end.
Infix "==" := dsl_eq (at level 70, only parsing): dsl_scope.

Definition dsl_neq (x y: Expr value) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (negb (Nat.eqb _x _y))
      end
    end.
Infix "!=" := dsl_neq (at level 70, only parsing): dsl_scope.

Definition dsl_not (x: Expr bool) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x => Valid (negb _x)
    end.
Notation "'!' x" := (dsl_not x) (at level 75, right associativity, only parsing) : dsl_scope.

Definition dsl_add (x y: Expr value) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (plus_with_overflow _x _y)
      end
    end.
Infix "+" := dsl_add (only parsing) : dsl_scope.

Definition dsl_sub (x y: Expr value) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (minus_with_underflow _x _y)
      end
    end.
Infix "-" := dsl_sub (only parsing) : dsl_scope.

Definition dsl_or (x y: Expr bool) :=
  fun (this: address) (st: state) (env: env) (msg: message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (orb _x _y)
      end
    end.
Infix "||" := dsl_or (only parsing) : dsl_scope.

Notation "'msg.sender'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) =>
     Valid (m_sender msg))
    (only parsing): dsl_scope.

Definition zero :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid 0).

Definition otrue := true.
Definition ofalse := false.

Notation "'true'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid true)
    (only parsing) : dsl_scope.
Notation "'false'" :=
  (fun (this: address) (st: state) (env: env) (msg: message) => Valid false)
    (only parsing) : dsl_scope.

Notation "'require' '(' cond ')'" :=
  (DSL_require cond) (at level 200, only parsing) : dsl_scope.

Notation "'emit' evt" :=
  (DSL_emit evt) (at level 200, only parsing) : dsl_scope.

Notation "'balances' '[' addr ']' '=' expr" :=
  (DSL_balances_upd addr expr) (at level 0, only parsing) : dsl_scope.

Notation "'balances' '[' addr ']' '+=' expr" :=
  (DSL_balances_upd addr
                    (dsl_add (dsl_balances_access addr) expr))
    (at level 0, only parsing) : dsl_scope.

Notation "'balances' '[' addr ']' '-=' expr" :=
  (DSL_balances_upd addr
                    (dsl_sub (dsl_balances_access addr) expr))
    (at level 0, only parsing) : dsl_scope.

Notation "'allowed' '[' from ']' '[' to ']' '=' expr" :=
  (DSL_allowed_upd from to expr) (at level 0, only parsing) : dsl_scope.

Notation "'allowed' '[' from ']' '[' to ']' '+=' expr" :=
  (DSL_allowed_upd from to
                   (dsl_add (dsl_allowed_access from to) expr))
    (at level 0, only parsing) : dsl_scope.

Notation "'allowed' '[' from ']' '[' to ']' '-=' expr" :=
  (DSL_allowed_upd from to
                   (dsl_sub (dsl_allowed_access from to) expr))
    (at level 0, only parsing) : dsl_scope.

Notation "'migratedBalances' '[' addr ']' '=' expr" :=
  (DSL_migratedBalances_upd addr expr) (at level 0, only parsing) : dsl_scope.

Notation "'totalSupply' '=' expr" :=
  (DSL_totalSupply_upd expr) (at level 0, only parsing) : dsl_scope.

Notation "'totalSupply' '+=' expr" :=
  (DSL_totalSupply_upd (dsl_add totalSupply%dsl expr))
    (at level 0, only parsing) : dsl_scope.

Notation "'totalSupply' '-=' expr" :=
  (DSL_totalSupply_upd (dsl_sub totalSupply%dsl expr))
    (at level 0, only parsing) : dsl_scope.

Notation "'symbol' '=' expr" :=
  (DSL_symbol_upd expr) (at level 0, only parsing) : dsl_scope.

Notation "'name' '=' expr" :=
  (DSL_name_upd expr) (at level 0, only parsing) : dsl_scope.

Notation "'decimals' '=' expr" :=
  (DSL_decimals_upd expr) (at level 0, only parsing) : dsl_scope.

Notation "'owner' '=' expr" :=
  (DSL_owner_upd expr) (at level 0, only parsing) : dsl_scope.

Notation "'oldToken' '=' expr" :=
  (DSL_oldToken_upd expr) (at level 0, only parsing) : dsl_scope.

Notation "'return' expr" :=
  (DSL_return expr) (at level 200, only parsing) : dsl_scope.

Notation "'nop'" :=
  (DSL_nop) (at level 200, only parsing) : dsl_scope.

Notation "'ctor'" :=
  DSL_ctor (at level 200, only parsing) : dsl_scope.

Notation "@ stmt_prim" :=
  (DSL_prim stmt_prim) (at level 200, only parsing) : dsl_scope.

Notation "'@if' ( cond ) { stmt0 } 'else' { stmt1 }" :=
  (DSL_if cond stmt0 stmt1) (at level 210, only parsing) : dsl_scope.

Notation "stmt0 ';' stmt1" :=
  (DSL_seq stmt0 stmt1) (at level 220, only parsing) : dsl_scope.

Notation "'@uint256' x = expr ; stmt" :=
  (let x: Expr uint256 := expr in stmt)
    (at level 230, x ident, only parsing) : dsl_scope.

Notation "'@address' x = expr ; stmt" :=
  (let x: Expr address := expr in stmt)
    (at level 230, x ident, only parsing) : dsl_scope.

Notation "'@uint8' x = expr ; stmt" :=
  (let x: Expr uint8 := expr in stmt)
    (at level 230, x ident, only parsing) : dsl_scope.

Notation "'@string' x = expr ; stmt" :=
  (let x: Expr string := expr in stmt)
    (at level 230, x ident, only parsing) : dsl_scope.


(* *************************************************************** *)
(* Each section below represents a ERC20 function in DSL and prove *)
(* the DSL representation does implement the specification.        *)
(* *************************************************************** *)

Require Import Spec.

Hint Rewrite
     Nat.ltb_antisym
     Nat.leb_le
     Nat.leb_refl
  : dsl_proof.

Section dsl_constructor.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ oldTokenAddr: Expr address }.
  Context `{ _oldTokenAddr: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ oldTokenAddr_immutable:
               forall this st env msg, oldTokenAddr this st env msg = Valid _oldTokenAddr }.

  Hint Rewrite
       oldTokenAddr_immutable
    : dsl_proof.

  (* DSL representation of constructor, generated from solidity *)
  Definition ctor_dsl : Stmt :=
    (@require(oldTokenAddr.stopped()) ;
     @oldToken = oldTokenAddr ;
     @name = (oldToken.name()) ;
     @symbol = (oldToken.symbol()) ;
     @decimals = (oldToken.decimals()) ;
     @totalSupply = (oldToken.totalSupply()) ;
     @owner = msg.sender ;
     @ctor
    ).

  (* Manually proved *)
  Lemma ctor_dsl_sat_spec:
    forall st env msg this,
      spec_require (funcspec_constructor _oldTokenAddr this env msg) st ->
        forall st0 result,
          dsl_exec ctor_dsl st0 st env msg this nil = result ->
          INV (ret_st result) env msg
          /\ spec_trans (funcspec_constructor _oldTokenAddr this env msg) st (ret_st result)
          /\ spec_events (funcspec_constructor _oldTokenAddr this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.

    simpl in Hreq.
    destruct Hreq as
        [Hinit_blncs [Hinit_allwd [Hinit_mblncs
                                     [ost [Hreq_ost [Hreq_stopped [Hreq_sum [Hreq_total_lo Hreq_total_hi]]]]]]]].

    simpl in Hexec.
    unfold
      dsl_remote_stopped_access,
      dsl_remote_name_access,
      dsl_remote_symbol_access,
      dsl_remote_decimals_access,
      dsl_remote_totalSupply_access
      in Hexec.

    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hreq_ost in Hexec);
            try (rewrite Hreq_stopped in Hexec);
            simpl in Hexec
           ).

    rewrite <- Hexec; clear Hexec.
    rewrite Hinit_blncs in *.
    rewrite Hinit_allwd in *.
    rewrite Hinit_mblncs in *.
    repeat (split; simpl; A2V.msimpl; AA2V.msimpl;
            auto with arith).

    - exists ost.
      do 2 (split; auto).
      unfold INV_sum_blncs; simpl.
      rewrite A2V.sum_filter_true.
      omega.

    - exists ost.
      repeat (split; auto).
  Qed.

  Close Scope dsl_scope.
End dsl_constructor.

Definition dsl_sat_spec (fcall: mcall)
                        (fdsl: Stmt)
                        (fspec: address -> env -> message -> Spec) : Prop :=
  forall st env msg this,
    m_func msg = fcall
    -> spec_require (fspec this env msg) st
    -> forall st0 result,
        dsl_exec fdsl st0 st env msg this nil = result
        -> INV st env msg
        -> INV (ret_st result) env msg
           /\ spec_trans (fspec this env msg) st (ret_st result)
           /\ spec_events (fspec this env msg) st (ret_evts result).

Section Aux.
  Lemma transfer_nomig_inv_sum_blncs:
    forall st st' ost from to value,
      ((st_migratedBalances st $ from)%a2b = ofalse ->
       INV_sum_blncs st ost ->
       A2V.equal (st_balances st') (st_balances st
                                                $ { from <+~ ost_balances ost $ from }
                                                $ { from <-~ value }
                                                $ { to <+~ value }) ->
       A2B.equal (st_migratedBalances st') ((st_migratedBalances st $ { from <~ otrue })%a2b) ->
       (st_balances st $ from) + (ost_balances ost $ from) >= value ->
       INV_sum_blncs st' ost)%nat.
  Proof.
    intros st st' ost from to value Hmig_from Hsum_blncs Hblncs Hmig Hblncs_lo.
    unfold INV_sum_blncs in *.

    pose (f := (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))).
    assert (Hf: forall v, f (from, v) = otrue).
    {
      unfold f; simpl.
      rewrite Hmig_from; auto.
    }

    pose (g := (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st') (fst e)))).
    assert (Hg: forall v, g (from, v) = ofalse).
    {
      unfold g; simpl.
      rewrite Hmig; A2B.msimpl.
    }

    assert (Hfg: forall k v, from <> k -> f (k, v) = g (k, v)).
    {
      intros.
      unfold f, g; simpl.
      rewrite Hmig; A2B.msimpl.
    }

    generalize (A2V.sum_filter_one_bit from f g Hf Hg Hfg (ost_balances ost)).
    unfold f, g; intros Hsum_filter_eq.

    assert (Hfrom_max: ((st_balances st $ from) + (ost_balances ost $ from) <= MAX_UINT256)%nat).
    {
      generalize (A2V.sum_upper (st_balances st) from); intros.
      generalize (A2V.sum_upper (ost_balances ost) from); intros.
      omega.
    }

    rewrite (A2V.sum_equal Hblncs).

    rewrite (A2V.sum_upd_inc
               (A2V.upd_dec (A2V.upd_inc (st_balances st) from (A2V.get (ost_balances ost) from)) from value)
               (A2V.sum (A2V.upd_dec (A2V.upd_inc (st_balances st) from (A2V.get (ost_balances ost) from)) from value)));
      A2V.msimpl; auto.
    rewrite (A2V.sum_upd_dec
               (A2V.upd_inc (st_balances st) from (A2V.get (ost_balances ost) from))
               (A2V.sum (A2V.upd_inc (st_balances st) from (A2V.get (ost_balances ost) from))));
      A2V.msimpl; auto.
    rewrite (A2V.sum_upd_inc
               (st_balances st)
               (A2V.sum (st_balances st)));
      A2V.msimpl; auto.

    generalize (A2V.sum_upper (st_balances st) from); intros Hfrom_le.
    omega.

    generalize (A2V.sum_upper (ost_balances ost) from); intros Host_from_le.
    omega.

    rewrite (plus_safe_lt _ _); omega.

    destruct (Nat.eq_dec to from); A2V.msimpl.
    - rewrite (plus_safe_lt _ _); [> | omega].
      rewrite (minus_safe _ _); omega.

    - generalize (A2V.sum_sum_filter_true_le
                    f from Hf (st_balances st) (ost_balances ost) to n);
        unfold f; intros.
      omega.
  Qed.

  Lemma transfer_mig_inv_sum_blncs:
    forall st st' ost from to value,
      ((st_migratedBalances st $ from)%a2b = otrue ->
       INV_sum_blncs st ost ->
       A2V.equal (st_balances st') (st_balances st
                                                $ { from <-~ value }
                                                $ { to <+~ value }) ->
       A2B.equal (st_migratedBalances st') (st_migratedBalances st) ->
       st_balances st $ from >= value ->
       value <= MAX_UINT256 ->
       INV_sum_blncs st' ost)%nat.
  Proof.
    intros st st' ost from to value Hmig_from Hsum_blncs Hblncs Hmig Hblncs_lo Hvalue_le.
    unfold INV_sum_blncs in *.

    pose (f := (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st') (fst e)))).
    pose (g := (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))).
    assert (Hfg: forall e, f e = g e).
    {
      intros.
      unfold f, g; simpl.
      rewrite Hmig; reflexivity.
    }

    generalize (A2V.sum_upper (st_balances st) from); intros Hfrom_le.

    generalize (A2V.sum_filter_f_eq Hfg (ost_balances ost));
      unfold f, g; intros Hsum_filter_eq.
    rewrite Hsum_filter_eq; clear Hsum_filter_eq.

    rewrite (A2V.sum_equal Hblncs).
    rewrite (A2V.sum_upd_inc (A2V.upd_dec (st_balances st) from value)
                             (A2V.sum (A2V.upd_dec (st_balances st) from value)));
      A2V.msimpl; auto.
    rewrite (A2V.sum_upd_dec (st_balances st) (A2V.sum (st_balances st)));
      A2V.msimpl; auto.
    omega.

    unfold A2V.upd_dec.
    rewrite (minus_safe _ _); [> | omega].
    destruct (Nat.eq_dec to from); A2V.msimpl.
    - subst to. omega.
    - generalize (A2V.sum_descend to from n (st_balances st)); intros.
      omega.
  Qed.
End Aux.

Section dsl_transferFrom.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ from: Expr address }.
  Context `{ _from: address }.
  Context `{ to: Expr address }.
  Context `{ _to: address }.
  Context `{ value: Expr uint256 }.
  Context `{ _value: uint256 }.

  Context `{ max_uint256: Expr uint256 }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ from_immutable:
               forall this st env msg, from this st env msg = Valid _from }.
  Context `{ to_immutable:
               forall this st env msg, to this st env msg = Valid _to }.
  Context `{ value_immutable:
               forall this st env msg, value this st env msg = Valid _value }.
  Context `{ max_uint256_immutable:
               forall this st env msg, max_uint256 this st env msg = Valid MAX_UINT256 }.

  Hint Rewrite
       from_immutable
       to_immutable
       value_immutable
       max_uint256_immutable
    : dsl_proof.

  (* DSL representation of transferFrom(), generated from solidity *)
  Definition transferFrom_dsl : Stmt :=
    (@uint256 allowance = allowed[from][msg.sender] ;
     @if (!migratedBalances[from]) {
         (@uint256 oldValue = oldToken.balanceOf(from);
          @balances[from] += oldValue;
          @migratedBalances[from] = true;
          (@emit Migrate(from, oldValue)))
     }  else {
         (@nop)
     } ;
     @require(balances[from] >= value) ;
     @require(allowance >= value) ;
     @balances[from] -= value ;
     @balances[to] += value;
     @if (allowance < max_uint256) {
         (@allowed[from][msg.sender] -= value)
     } else {
         (@nop)
     } ;
     (@emit Transfer(from, to, value)) ;
     (@return true)).

  (* Manually proved *)
  Lemma transferFrom_dsl_sat_spec_1:
    dsl_sat_spec (mc_transferFrom _from _to _value)
                 transferFrom_dsl
                 (funcspec_transferFrom_1 _from _to _value).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hallwd [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.

    simpl in Hreq.
    destruct Hreq as [Hmig [[Hallwd_lo Hallwd_hi] [ost' [Hcontract' Hsum]]]].
    rewrite Hcontract in Hcontract'; inversion Hcontract'; subst ost'; clear Hcontract'.

    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge, dsl_allowed_access, dsl_eq, dsl_or, dsl_lt in Hexec.

    assert (Hfilter_from:
              negb (A2B.get (st_migratedBalances st) (fst (_from, A2V.get (ost_balances ost) _from))) = otrue).
    {
      simpl. rewrite Hmig. auto.
    }

    assert (Hfrom_le:
              ((st_balances st $ _from) + (ost_balances ost $ _from) <=
               A2V.sum (st_balances st) +
               A2V.sum_filter (ost_balances ost)
                              (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e))))%nat).
    {
      generalize (sum_upper (st_balances st) _from); intros.
      generalize (sum_filter_true_upper
                    (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))
                    _from (ost_balances ost) Hfilter_from); intros.
      omega.
    }

    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hmig in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite (proj2 (Nat.leb_le _ _) Hsum_from_hi) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hsum) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hallwd_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_gt _ _) Hallwd_hi) in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
    rewrite <- Hexec; clear Hexec.

    repeat (split; simpl; try omega; auto).

    - (* INV *)
      assert (Hallwd' :(AA2V.get (st_allowed st) (_from, m_sender msg) - 0 >= _value)%nat).
      { omega. }
      apply (proj2 (AA2V.upd_dec_in_range
                       (st_allowed st) 0 MAX_UINT256 Hallwd
                       (_from, m_sender msg) _value Hallwd' _));
        auto.

    - (* INV *)
      exists ost.
      do 2 (split; auto).
      apply transfer_nomig_inv_sum_blncs
        with (st := st) (from := _from) (to := _to) (value := _value); auto.
      unfold A2V.upd_inc, A2V.upd_dec.
      A2V.msimpl.
      rewrite (plus_safe_lt (A2V.get (st_balances st) _from)
                            (A2V.get (ost_balances ost) _from));
        [> idtac | omega ].
      rewrite (minus_safe (A2V.get (st_balances st) _from + A2V.get (ost_balances ost) _from)%nat
                          _value);
        [> idtac | omega ].
      auto.

    - exists ost.
      split; auto.
      unfold A2V.upd_inc, A2V.upd_dec.
      rewrite (plus_safe_lt (A2V.get (st_balances st) _from)
                            (A2V.get (ost_balances ost) _from));
        [> idtac | omega ].
      A2V.msimpl.
      rewrite (minus_safe (A2V.get (st_balances st) _from + A2V.get (ost_balances ost) _from)%nat
                          _value);
        [> idtac | omega ].
      auto.

    - unfold AA2V.upd_dec.
      rewrite (minus_safe _ _); [> idtac | omega ].
      auto.

    - exists ost.
      repeat (split; auto).
  Qed.

  Lemma transferFrom_dsl_sat_spec_2:
    dsl_sat_spec (mc_transferFrom _from _to _value)
                 transferFrom_dsl
                 (funcspec_transferFrom_2 _from _to _value).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hallwd [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs.

    simpl in Hreq.
    destruct Hreq as [Hmig_from [[Hallwd_lo Hallwd_hi] Hblncs_lo]].

    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge, dsl_allowed_access, dsl_eq, dsl_or, dsl_lt in Hexec.

    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hmig_from in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hblncs_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hallwd_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_gt _ _) Hallwd_hi) in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
    rewrite <- Hexec; clear Hexec.

    repeat (split; simpl; try omega; auto).

    - (* INV *)
      rewrite (minus_safe _ _); [> | omega].
      assert (Hallwd' :(AA2V.get (st_allowed st) (_from, m_sender msg) - 0 >= _value)%nat).
      { omega. }
      apply (proj2 (AA2V.upd_dec_in_range
                       (st_allowed st) 0 MAX_UINT256 Hallwd
                       (_from, m_sender msg) _value Hallwd' _));
        auto.

    - (* INV *)
      exists ost.
      do 2 (split; auto).

      generalize (transferFrom_value_inrange _ _ _ _ Hfunc);
        intros [_ Hvalue_hi].

      apply transfer_mig_inv_sum_blncs
        with (st := st) (from := _from) (to := _to) (value := _value);
        simpl; auto.

    - exists ost.
      repeat (split; auto).
  Qed.

  Lemma transferFrom_dsl_sat_spec_3:
    dsl_sat_spec (mc_transferFrom _from _to _value)
                 transferFrom_dsl
                 (funcspec_transferFrom_3 _from _to _value).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hallwd_all [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.

    simpl in Hreq.
    destruct Hreq as [Hmig_from [Hallwd[ost' [Hcontract' Hblncs_lo]]]].
    rewrite Hcontract in Hcontract'; inversion Hcontract'; subst ost'; clear Hcontract'.

    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge, dsl_allowed_access, dsl_eq, dsl_or, dsl_lt in Hexec.

    assert (Hfilter_from:
              negb (A2B.get (st_migratedBalances st) (fst (_from, A2V.get (ost_balances ost) _from))) = otrue).
    {
      simpl. rewrite Hmig_from. auto.
    }

    assert (Hfrom_le:
              ((st_balances st $ _from) + (ost_balances ost $ _from) <=
               A2V.sum (st_balances st) +
               A2V.sum_filter (ost_balances ost)
                              (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e))))%nat).
    {
      generalize (sum_upper (st_balances st) _from); intros.
      generalize (sum_filter_true_upper
                    (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))
                    _from (ost_balances ost) Hfilter_from); intros.
      omega.
    }

    generalize (transferFrom_value_inrange _ _ _ _ Hfunc);
      intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].

    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hmig_from in Hexec);
            try (rewrite Hallwd in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite (proj2 (Nat.leb_le _ _) Hsum_from_hi) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hblncs_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_hi) in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
    rewrite <- Hexec; clear Hexec.

    repeat (split; simpl; auto).

    - (* INV *)
      exists ost.
      do 2 (split; auto).
      apply transfer_nomig_inv_sum_blncs
        with (st := st) (from := _from) (to := _to) (value := _value);
        simpl; auto.
      unfold A2V.upd_inc, A2V.upd_dec.
      A2V.msimpl.
      rewrite (plus_safe_lt (A2V.get (st_balances st) _from)
                            (A2V.get (ost_balances ost) _from));
        [> idtac | omega ].
      rewrite (minus_safe (A2V.get (st_balances st) _from + A2V.get (ost_balances ost) _from)%nat
                          _value);
        [> idtac | omega ].
      auto.

    - exists ost.
      split; auto.
      unfold A2V.upd_inc, A2V.upd_dec.
      rewrite (plus_safe_lt (A2V.get (st_balances st) _from)
                            (A2V.get (ost_balances ost) _from));
        [> idtac | omega ].
      A2V.msimpl.
      rewrite (minus_safe (A2V.get (st_balances st) _from + A2V.get (ost_balances ost) _from)%nat
                          _value);
        [> idtac | omega ].
      auto.

    - exists ost.
      repeat (split; auto).
  Qed.

  Lemma transferFrom_dsl_sat_spec_4:
    dsl_sat_spec (mc_transferFrom _from _to _value)
                 transferFrom_dsl
                 (funcspec_transferFrom_4 _from _to _value).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hallwd_all [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.

    simpl in Hreq.
    destruct Hreq as [Hmig_from [Hallwd Hblncs_lo]].

        simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge, dsl_allowed_access, dsl_eq, dsl_or, dsl_lt in Hexec.

    generalize (transferFrom_value_inrange _ _ _ _ Hfunc);
      intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].

    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hmig_from in Hexec);
            try (rewrite Hallwd in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hblncs_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_hi) in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
    rewrite <- Hexec; clear Hexec.

    repeat (split; simpl; auto).

    - (* INV *)
      exists ost.
      do 2 (split; auto).
      apply transfer_mig_inv_sum_blncs
        with (st := st) (from := _from) (to := _to) (value := _value);
        simpl; auto.

    - exists ost.
      repeat (split; auto).
  Qed.

  (* If transferFrom is executed without the satisfaction of any requirements,
     then it must revert to the state before the function call *)
  Lemma transferFrom_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transferFrom _from _to _value ->
      INV st env msg ->
      ~ spec_require (funcspec_transferFrom_1 _from _to _value this env msg) st ->
      ~ spec_require (funcspec_transferFrom_2 _from _to _value this env msg) st ->
      ~ spec_require (funcspec_transferFrom_3 _from _to _value this env msg) st ->
      ~ spec_require (funcspec_transferFrom_4 _from _to _value this env msg) st ->
      forall result,
        dsl_exec transferFrom_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv
           Hreq1_neg Hreq2_neg Hreq3_neg Hreq4_neg
           result Hexec.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hallwd [ost [Hcontract [Hstopped Hinv]]]]].
    unfold INV_sum_blncs in Hinv.

    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge, dsl_allowed_access, dsl_eq, dsl_or, dsl_lt in Hexec.

    autorewrite with dsl_proof in Hexec.
    case_eq (A2B.get (st_migratedBalances st) _from);
      intros Hmig_from;
      rewrite Hmig_from in Hexec;
      simpl in Hexec;
      autorewrite with dsl_proof in Hexec.

    - destruct (Nat.le_decidable _value (A2V.get (st_balances st) _from)).
      + rewrite (proj2 (Nat.leb_le _ _) H) in Hexec;
          simpl in Hexec;
          autorewrite with dsl_proof in Hexec.
        destruct (Nat.le_decidable _value (AA2V.get (st_allowed st) (_from, m_sender msg))).

        * rewrite (proj2 (Nat.leb_le _ _) H0) in Hexec;
            repeat (autorewrite with dsl_proof in Hexec;
                    simpl in Hexec).
          { destruct (Nat.le_decidable MAX_UINT256 (AA2V.get (st_allowed st) (_from, m_sender msg))).
            - clear Hexec.
              substH Hallwd with (Hallwd (_from, m_sender msg)).
              destruct Hallwd as [_ Hallwd_hi].
              assert (AA2V.get (st_allowed st) (_from, m_sender msg) = MAX_UINT256);
                [> omega | ].
              unfold funcspec_transferFrom_4 in Hreq4_neg; simpl in Hreq4_neg.
              assert (Hfalse: False);
                [> apply Hreq4_neg; auto | inversion Hfalse].

            - clear Hexec.
              assert (AA2V.get (st_allowed st) (_from, m_sender msg) < MAX_UINT256)%nat;
                [> omega | ].
              unfold funcspec_transferFrom_2 in Hreq2_neg; simpl in Hreq2_neg.
              assert (Hfalse: False);
                [> apply Hreq2_neg; auto | inversion Hfalse].
          }

        * rewrite (proj2 (Nat.leb_nle _ _) H0) in Hexec; simpl in Hexec.
          rewrite <- Hexec.
          unfold Stop; unfold INV; simpl.
          repeat (split; auto).
          exists ost; repeat (split; auto).

      + rewrite (proj2 (Nat.leb_nle _ _) H) in Hexec; simpl in Hexec.
        rewrite <- Hexec.
        unfold Stop; unfold INV; simpl.
        repeat (split; auto).
        exists ost; repeat (split; auto).

    - repeat (try (autorewrite with dsl_proof in Hexec);
              try (rewrite Hcontract in Hexec);
              simpl in Hexec).

      generalize (A2V.sum_upper (st_balances st) _from);
        intros.

      assert (Hftrue:
                (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))
                  (_from, (ost_balances ost $ _from)) = otrue).
      { simpl. rewrite Hmig_from. auto. }

      generalize (A2V.sum_filter_true_upper
                    (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))
                    _from (ost_balances ost) Hftrue);
        intros.

        rewrite (plus_safe_lt _ _) in Hexec; [> | omega].
        A2V.msimpl_in Hexec.

        destruct (Nat.le_decidable
                    _value
                    (A2V.get (st_balances st) _from + A2V.get (ost_balances ost) _from)).

      + rewrite (proj2 (Nat.leb_le _ _) H1) in Hexec;
          repeat (simpl in Hexec; autorewrite with dsl_proof in Hexec).
        destruct (Nat.le_decidable
                    _value (AA2V.get (st_allowed st) (_from, m_sender msg))).

        * rewrite (proj2 (Nat.leb_le _ _) H2) in Hexec;
            repeat (simpl in Hexec; autorewrite with dsl_proof in Hexec).
          clear Hexec.
          { destruct (Nat.le_decidable
                        MAX_UINT256 (AA2V.get (st_allowed st) (_from, m_sender msg))).
            - substH Hallwd with (Hallwd (_from, m_sender msg)).
              assert (AA2V.get (st_allowed st) (_from, m_sender msg) = MAX_UINT256)%nat;
                [> omega | ].
              unfold funcspec_transferFrom_3 in Hreq3_neg;
                simpl in Hreq3_neg.
              assert (Hfalse: False);
                [> apply Hreq3_neg; repeat (split; auto) | inversion Hfalse].
              exists ost; repeat (split; auto).

            - apply (proj2 (Nat.leb_nle _ _)) in H3.
              apply (proj1 (Nat.leb_gt _ _)) in H3.
              unfold funcspec_transferFrom_1 in Hreq1_neg;
                simpl in Hreq1_neg.
              assert (Hfalse: False);
                [> apply Hreq1_neg; repeat (split; auto) | inversion Hfalse].
              exists ost; repeat (split; auto).
          }

        * rewrite (proj2 (Nat.leb_nle _ _) H2) in Hexec;
            simpl in Hexec.
          rewrite <- Hexec.
          unfold Stop, INV; simpl.
          repeat (split; auto).
          exists ost; repeat (split; auto).

      + rewrite (proj2 (Nat.leb_nle _ _) H1) in Hexec;
          simpl in Hexec.
        rewrite <- Hexec.
        unfold Stop, INV; simpl.
        repeat (split; auto).
        exists ost; repeat (split; auto).
  Qed.

  Close Scope dsl_scope.
End dsl_transferFrom.

Section dsl_transfer.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ to: Expr address }.
  Context `{ _to: address }.
  Context `{ value: Expr uint256 }.
  Context `{ _value: uint256 }.
  Context `{ max_uint256: Expr uint256 }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ to_immutable:
               forall this st env msg, to this st env msg = Valid _to }.
  Context `{ value_immutable:
               forall this st env msg, value this st env msg = Valid _value }.
  Context `{ max_uint256_immutable:
               forall this st env msg, max_uint256 this st env msg = Valid MAX_UINT256 }.

  Hint Rewrite
       to_immutable
       value_immutable
       max_uint256_immutable
    : dsl_proof.

  (* DSL representation of transfer(), generated from solidity *)
  Definition transfer_dsl : Stmt :=
    (@if (!migratedBalances[msg.sender]) {
         (@uint256 oldValue = oldToken.balanceOf(msg.sender);
         @balances[msg.sender] += oldValue;
         @migratedBalances[msg.sender] = true;
         (@emit Migrate(msg.sender, oldValue)))
     }  else {
         (@nop)
     } ;
     @require(balances[msg.sender] >= value) ;
     @balances[msg.sender] -= value ;
     @balances[to] += value ;
     (@emit Transfer(msg.sender, to, value)) ;
     (@return true)
    ).

  (* Manually proved *)
  Lemma transfer_dsl_sat_spec_1:
    dsl_sat_spec (mc_transfer _to _value)
                 transfer_dsl
                 (funcspec_transfer_1 _to _value).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.
    
    simpl in Hreq.
    destruct Hreq as [Hmig_sender [ost' [Hcontract' Hblncs_lo]]].
    rewrite Hcontract in Hcontract'; inversion Hcontract'; subst ost'; clear Hcontract'.

    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt in Hexec.

    assert (Hfilter_sender:
              negb (A2B.get (st_migratedBalances st) (fst ((m_sender msg), A2V.get (ost_balances ost) (m_sender msg)))) = otrue).
    {
      simpl. rewrite Hmig_sender. auto.
    }

     assert (Hsender_le:
              ((st_balances st $ (m_sender msg)) + (ost_balances ost $ (m_sender msg)) <=
               A2V.sum (st_balances st) +
               A2V.sum_filter (ost_balances ost)
                              (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e))))%nat).
    {
      generalize (sum_upper (st_balances st) (m_sender msg)); intros.
      generalize (sum_filter_true_upper
                    (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))
                    (m_sender msg) (ost_balances ost) Hfilter_sender); intros.
      omega.
    }

    generalize (transfer_value_inrange _ _ _ Hfunc);
      intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].


     repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hmig_sender in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite (proj2 (Nat.leb_le _ _) Hblncs_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_hi) in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
     rewrite <- Hexec; clear Hexec.     

     repeat (split; simpl; auto).

    - (* INV *)
      exists ost.
      do 2 (split; auto).
      apply transfer_nomig_inv_sum_blncs
        with (st := st) (from := (m_sender msg)) (to := _to) (value := _value);
        simpl; auto.
      unfold A2V.upd_inc, A2V.upd_dec.
      A2V.msimpl.
      rewrite (plus_safe_lt (A2V.get (st_balances st) (m_sender msg))
                            (A2V.get (ost_balances ost) (m_sender msg)));
        [> idtac | omega ].
      rewrite (minus_safe (A2V.get (st_balances st) (m_sender msg) + A2V.get (ost_balances ost) (m_sender msg))%nat
                          _value);
        [> idtac | omega ].
      auto.

    - exists ost.
      split; auto.
      unfold A2V.upd_inc, A2V.upd_dec.
      rewrite (plus_safe_lt (A2V.get (st_balances st) (m_sender msg))
                            (A2V.get (ost_balances ost) (m_sender msg)));
        [> idtac | omega ].
      A2V.msimpl.
      rewrite (minus_safe (A2V.get (st_balances st) (m_sender msg) + A2V.get (ost_balances ost) (m_sender msg))%nat
                          _value);
        [> idtac | omega ].
      auto.

    - exists ost.
      repeat (split; auto).
Qed.

  
  Lemma transfer_dsl_sat_spec_2:
    dsl_sat_spec (mc_transfer _to _value)
                 transfer_dsl
                 (funcspec_transfer_2 _to _value).
  Proof.
        intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.
    
    simpl in Hreq.
    destruct Hreq as [Hmig_sender Hblncs_lo].
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt in Hexec.

    generalize (transfer_value_inrange _ _ _ Hfunc);
      intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].


     repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hmig_sender in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite (proj2 (Nat.leb_le _ _) Hblncs_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_hi) in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
     rewrite <- Hexec; clear Hexec.     

     repeat (split; simpl; auto).

    - (* INV *)
      exists ost.
      do 2 (split; auto).
      apply transfer_mig_inv_sum_blncs
        with (st := st) (from := (m_sender msg)) (to := _to) (value := _value);
        simpl; auto.
      unfold A2V.upd_inc, A2V.upd_dec.
      A2V.msimpl.
      rewrite (minus_safe (A2V.get (st_balances st) (m_sender msg))%nat
                          _value);
        [> idtac | omega ].
      A2V.msimpl. auto.

    - unfold A2V.upd_inc, A2V.upd_dec.
      rewrite (minus_safe (A2V.get (st_balances st) (m_sender msg))%nat
                          _value);
        [> idtac | omega ].
      A2V.msimpl. auto.
    - exists ost.
      repeat (split; auto).
Qed.

  Lemma transfer_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transfer _to _value ->
      INV st env msg ->
      ~ spec_require (funcspec_transfer_1 _to _value this env msg) st ->
      ~ spec_require (funcspec_transfer_2 _to _value this env msg) st ->
      forall result,
        dsl_exec transfer_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq1_neg Hreq2_neg result Hexec.
    unfold INV in Hinv.
    destruct Hinv as [Htotal [Hallwd [ost [Hcontract [Hstopped Hinv]]]]].
    unfold INV_sum_blncs in Hinv.

    unfold funcspec_transfer_1 in Hreq1_neg. simpl in Hreq1_neg.
    unfold funcspec_transfer_2 in Hreq2_neg. simpl in Hreq2_neg.

    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge, dsl_eq, dsl_or, dsl_lt in Hexec.

    autorewrite with dsl_proof in Hexec.
     case_eq (A2B.get (st_migratedBalances st) (m_sender msg));
      intros Hmig_sender;
      rewrite Hmig_sender in Hexec;
      simpl in Hexec;
      autorewrite with dsl_proof in Hexec.

    - (* A2B.get (st_migratedBalances st) (m_sender msg) = true *)
      destruct (Nat.le_decidable _value (A2V.get (st_balances st) (m_sender msg))).
      + (* _value <= A2V.get (st_balances st) (m_sender msg) *)
        assert (Hfalse: False);
           [> apply Hreq2_neg; auto | inversion Hfalse].
      + (* _value > A2V.get (st_balances st) (m_sender msg) *)
        rewrite (proj2 (Nat.leb_nle _ _) H) in Hexec;
          simpl in Hexec;
          autorewrite with dsl_proof in Hexec.
          rewrite <- Hexec.
          unfold Stop; unfold INV; simpl.
          repeat (split; auto).
          exists ost; repeat (split; auto).

     - (* A2B.get (st_migratedBalances st) (m_sender msg) = false *)
       destruct (Nat.le_decidable _value (A2V.get (st_balances st) (m_sender msg) +
                   A2V.get (ost_balances ost) (m_sender msg))).
       + (* _value <= A2V.get (st_balances st) (m_sender msg) + +
                   A2V.get (ost_balances OS) (m_sender msg)*)
          assert (Hfalse: False);
            [> apply Hreq1_neg; auto | inversion Hfalse].
           repeat (split; auto).
          exists ost.  repeat (split; auto).
       + (* _value > A2V.get (st_balances st) (m_sender msg) + +
                   A2V.get (ost_balances OS) (m_sender msg)*)
         
         repeat (try (autorewrite with dsl_proof in Hexec);
              try (rewrite Hcontract in Hexec);
              simpl in Hexec; A2V.msimpl_in Hexec).

        generalize (A2V.sum_upper (st_balances st) (m_sender msg));
          intros.
        
         assert (Hftrue:
                (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))
                  ((m_sender msg), (ost_balances ost $ (m_sender msg))) = otrue).
         { simpl. rewrite Hmig_sender. auto. }

         generalize (A2V.sum_filter_true_upper
                    (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))
                   (m_sender msg) (ost_balances ost) Hftrue);
        intros.
      
         rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega ].
         simpl in Hexec; A2V.msimpl_in Hexec.

         rewrite (proj2 (Nat.leb_nle _ _) H) in Hexec;
          simpl in Hexec;
          autorewrite with dsl_proof in Hexec.
          rewrite <- Hexec.
          unfold Stop; unfold INV; simpl.
          repeat (split; auto).
          exists ost; repeat (split; auto).   
  Qed.

  Close Scope dsl_scope.
End dsl_transfer.

Section dsl_balanceOf.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ addr: Expr address }.
  Context `{ _addr: address }.
  Context `{ max_uint256: Expr uint256 }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ addr_immutable:
               forall this st env msg, addr this st env msg = Valid _addr }.
  Context `{ max_uint256_immutable:
               forall this st env msg, max_uint256 this st env msg = Valid MAX_UINT256 }.

  Hint Rewrite
       addr_immutable
       max_uint256_immutable
    : dsl_proof.

  (* DSL representation of transfer(), generated from solidity *)
  Definition balanceOf_dsl : Stmt :=
    (@if (!migratedBalances[addr]) {
         (@uint256 oldValue = oldToken.balanceOf(addr);
         @balances[addr] += oldValue;
         @migratedBalances[addr] = true;
         (@emit Migrate(addr, oldValue)))
     }  else {
         (@nop)
     } ;
       @return balances[addr]).

     Lemma balance_nomig_inv_sum_blncs:
    forall st st' ost _addr,
      ((st_migratedBalances st $ _addr)%a2b = ofalse ->
       INV_sum_blncs st ost ->
       A2V.equal (st_balances st') (st_balances st
                                                $ { _addr <+~ ost_balances ost $ _addr })  ->
       A2B.equal (st_migratedBalances st') ((st_migratedBalances st $ { _addr <~ otrue })%a2b) ->
       INV_sum_blncs st' ost)%nat.
  Proof.
    intros st st' ost addr0 Hmig_addr HINV  Hblncs Hmig.
    unfold INV_sum_blncs in *.

    pose (f := (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st) (fst e)))).
    assert (Hf: forall v, f (addr0, v) = otrue).
    {
      unfold f; simpl.
      rewrite Hmig_addr; auto.
    }

    pose (g := (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances st') (fst e)))).
    assert (Hg: forall v, g (addr0, v) = ofalse).
    {
      unfold g; simpl.
      rewrite Hmig; A2B.msimpl.
    }

    assert (Hfg: forall k v, addr0 <> k -> f (k, v) = g (k, v)).
    {
      intros.
      unfold f, g; simpl.
      rewrite Hmig; A2B.msimpl.
    }

    generalize (A2V.sum_filter_one_bit addr0 f g Hf Hg Hfg (ost_balances ost)).
    unfold f, g; intros Hsum_filter_eq.

    assert (Hfrom_max: ((st_balances st $ addr0) + (ost_balances ost $ addr0) <= MAX_UINT256)%nat).
    {
      generalize (A2V.sum_upper (st_balances st) addr0); intros.
      generalize (A2V.sum_upper (ost_balances ost) addr0); intros.
      omega.
    }

    rewrite (A2V.sum_equal Hblncs).

        rewrite (A2V.sum_upd_inc
               (st_balances st)
               (A2V.sum (st_balances st)));
      A2V.msimpl; auto.


    generalize (A2V.sum_upper (st_balances st) addr0); intros Hfrom_le.
    omega.

    generalize (A2V.sum_upper (ost_balances ost) addr0); intros Host_from_le.
    omega.
  Qed.

  (* Manually proved *)
  Lemma balanceOf_dsl_sat_spec_1:
    dsl_sat_spec (mc_balanceOf _addr)
                 balanceOf_dsl
                 (funcspec_balanceOf_1 _addr).
  Proof.
    intros state env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.
    
    simpl in Hreq.
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt in Hexec.

    assert (Hfilter_addr:
              negb (A2B.get (st_migratedBalances state) (fst (_addr, A2V.get (ost_balances ost) _addr))) = otrue).
    {
      simpl. rewrite Hreq. auto.
    }

    assert (Haddr_le:
              ((st_balances state $ _addr) + (ost_balances ost $ _addr) <=
               A2V.sum (st_balances state) +
               A2V.sum_filter (ost_balances ost)
                              (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances state) (fst e))))%nat).
    {
      generalize (sum_upper (st_balances state) _addr); intros.
      generalize (sum_filter_true_upper
                    (fun e : nat * Types.value => negb (A2B.get (st_migratedBalances state) (fst e)))
                    _addr (ost_balances ost) Hfilter_addr); intros.
      omega.
    }

         repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Hreq in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite  addr_immutable in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hblncs_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_hi) in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
     rewrite <- Hexec; clear Hexec.     

     repeat (split; simpl; auto).
     
   - (* Inv *)
      exists ost.
      do 2 (split; auto).
      apply balance_nomig_inv_sum_blncs with state _addr.
      + auto.
      + auto.
      + unfold A2V.upd_inc, A2V.upd_dec.
        rewrite (plus_safe_lt (A2V.get (st_balances state) _addr)
                            (A2V.get (ost_balances ost) _addr)).
        A2V.msimpl. auto.
        omega.
      + auto.
   - exists ost.
     split; auto.
     unfold A2V.upd_inc.
     rewrite (plus_safe_lt (A2V.get (st_balances state) _addr)
                           (A2V.get (ost_balances ost) _addr)); [> idtac | omega].
     auto.     
   - exists ost.
     do 2 (split; auto).
  Qed.

Lemma balanceOf_dsl_sat_spec_2:
    dsl_sat_spec (mc_balanceOf _addr)
                 balanceOf_dsl
                 (funcspec_balanceOf_2 _addr).
Proof.
  intros state env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.
    
    simpl in Hreq.
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt in Hexec.


         repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Hreq in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite  addr_immutable in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hblncs_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_lo) in Hexec);
            try (rewrite (proj2 (Nat.leb_le _ _) Hvalue_hi) in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
     rewrite <- Hexec; clear Hexec.     

     repeat (split; simpl; auto).
     
   - (* Inv *)
      exists ost.
      do 2 (split; auto).
Qed.    

  Lemma balanceOf_dsl_revert:
    forall st env msg this,
      m_func msg = mc_balanceOf _addr ->
      INV st env msg ->
      ~ spec_require (funcspec_balanceOf_1 _addr this env msg) st ->
      ~ spec_require (funcspec_balanceOf_2 _addr this env msg) st ->
      forall result,
        dsl_exec balanceOf_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq1_neg Hreq2_neg result Hexec.

     unfold INV in Hinv.
    destruct Hinv as [Htotal [Hallwd [ost [Hcontract [Hstopped Hinv]]]]].
    unfold INV_sum_blncs in Hinv.

    unfold funcspec_balanceOf_1 in Hreq1_neg. simpl in Hreq1_neg.
    unfold funcspec_balanceOf_2 in Hreq2_neg. simpl in Hreq2_neg.

    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge, dsl_eq, dsl_or, dsl_lt in Hexec.

    autorewrite with dsl_proof in Hexec.
     case_eq (A2B.get (st_migratedBalances st) (_addr));
      simpl in Hexec;
      autorewrite with dsl_proof in Hexec.

    + (* A2B.get (st_migratedBalances st) _addr = true *)
      intros.
      assert (Hfalse: False);
        [> apply Hreq2_neg; auto | inversion Hfalse].
    + (* A2B.get (st_migratedBalances st) _addr = false *)
      intros.
      assert (Hfalse: False);
        [> apply Hreq1_neg; auto | inversion Hfalse].
  Qed.

  Close Scope dsl_scope.
End dsl_balanceOf.

Section dsl_approve.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ spender: Expr address }.
  Context `{ _spender: address }.
  Context `{ value: Expr uint256 }.
  Context `{ _value: uint256 }.
  Context `{ max_uint256: Expr uint256 }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ spender_immutable:
               forall this st env msg, spender this st env msg = Valid _spender }.
  Context `{ value_immutable:
               forall this st env msg, value this st env msg = Valid _value }.
  Context `{ max_uint256_immutable:
               forall this st env msg, max_uint256 this st env msg = Valid MAX_UINT256 }.

  Hint Rewrite
       spender_immutable
       value_immutable
       max_uint256_immutable
    : proof.

  (* DSL representation of approve(), generated from solidity *)
  Definition approve_dsl : Stmt :=
    (@allowed[msg.sender][spender] = value ;
     (@emit Approval(msg.sender, spender, value)) ;
     (@return true)
    ).

  (* Manually proved *)
  Lemma approve_dsl_sat_spec:
    dsl_sat_spec (mc_approve _spender _value)
                 approve_dsl
                 (funcspec_approve _spender _value).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.

    generalize (approve_value_inrange _ _ _value  Hfunc);
      intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].
    
    simpl in Hreq.
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt in Hexec.

    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite (spender_immutable _ _ _ _) in Hexec);
            try (rewrite (value_immutable _ _ _ _) in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
     rewrite <- Hexec; clear Hexec.     

     repeat (split; simpl; auto).     
    - (* Inv *)
      exists ost.
      do 2 (split; auto).    
  Qed.

  Lemma approve_dsl_revert:
    forall st env msg this,
      m_func msg = mc_approve _spender _value ->
      INV st env msg ->
      ~ spec_require (funcspec_approve _spender _value this env msg) st ->
      forall result,
        dsl_exec approve_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.

    unfold INV in Hinv.
    destruct Hinv as [Htotal [Hallwd [ost [Hcontract [Hstopped Hinv]]]]].
    unfold INV_sum_blncs in Hinv.

    unfold funcspec_approve in Hreq_neg. simpl in Hreq_neg.
    unfold not in Hreq_neg.
    
    assert (Hfalse: False);
        [> apply Hreq_neg; auto | inversion Hfalse].
  Qed.

  Close Scope dsl_scope.
End dsl_approve.

Section dsl_allowance.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ addr: Expr address }.
  Context `{ _addr: address }.
  Context `{ spender: Expr address }.
  Context `{ _spender: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ addr_immutable:
               forall this st env msg, addr this st env msg = Valid _addr }.
  Context `{ spender_immutable:
               forall this st env msg, spender this st env msg = Valid _spender }.

  (* DSL representation of transfer(), generated from solidity *)
  Definition allowance_dsl : Stmt :=
    (@return allowed[addr][spender]).

  (* Manually proved *)
  Lemma allowance_dsl_sat_spec:
    dsl_sat_spec (mc_allowance _addr _spender)
                 allowance_dsl
                 (funcspec_allowance _addr _spender).
  Proof.
     intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.
    
    simpl in Hreq.
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt,dsl_allowed_access in Hexec.

    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite (spender_immutable _ _ _ _) in Hexec);
            try (rewrite (addr_immutable _ _ _ _) in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
     rewrite <- Hexec; clear Hexec.     

     repeat (split; simpl; auto).     
   - (* Inv *)
      exists ost.
      do 2 (split; auto).    
  Qed.
  
  Lemma allowance_dsl_revert:
    forall st env msg this,
      m_func msg = mc_allowance _addr _spender ->
      INV st env msg ->
      ~ spec_require (funcspec_allowance _addr _spender this env msg) st ->
      forall result,
        dsl_exec allowance_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
     intros st env msg this Hfunc Hinv Hreq_neg result Hexec.

    unfold INV in Hinv.
    destruct Hinv as [Htotal [Hallwd [ost [Hcontract [Hstopped Hinv]]]]].
    unfold INV_sum_blncs in Hinv.

    unfold funcspec_approve in Hreq_neg. simpl in Hreq_neg.
    unfold not in Hreq_neg.
    
    assert (Hfalse: False);
      [> apply Hreq_neg; auto | inversion Hfalse].
  Qed.

  Close Scope dsl_scope.
End dsl_allowance.

Section dsl_increaseApproval.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ spender: Expr address }.
  Context `{ _spender: address }.
  Context `{ addValue: Expr uint256 }.
  Context `{ _addValue: uint256 }.
  Context `{ max_uint256: Expr uint256}.

  (* Arguments are immutable, generated from solidity *)
  Context `{ spender_immutable:
               forall this st env msg, spender this st env msg = Valid _spender }.
  Context `{ addValue_immutable:
               forall this st env msg, addValue this st env msg = Valid _addValue }.
  Context `{ max_uint256_immutable:
               forall this st env msg, max_uint256 this st env msg = Valid MAX_UINT256}.

  (* DSL representation of approve(), generated from solidity *)
  Definition increaseApproval_dsl : Stmt :=
    (@require(allowed[msg.sender][spender] <= max_uint256 - addValue) ;
     @allowed[msg.sender][spender] += addValue ;
     (@emit Approval(msg.sender, spender, allowed[msg.sender][spender])) ;
     (@return true)
    ).

  (* Manually proved *)
  Lemma increaseApproval_dsl_sat_spec:
    dsl_sat_spec (mc_increaseApproval _spender _addValue)
                 increaseApproval_dsl
                 (funcspec_increaseApproval _spender _addValue).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.
    
    simpl in Hreq.
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt, dsl_allowed_access in Hexec.

     generalize (increaseApproval_value_inrange _ _ _ Hfunc);
       intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].

     apply Nat.leb_le in Hreq.
     
    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite (spender_immutable _ _ _ _) in Hexec);
            try (rewrite (addValue_immutable _ _ _ _) in Hexec);
            try (rewrite (max_uint256_immutable _ _ _ _) in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hreq in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
    
    rewrite <- Hexec; clear Hexec.
    apply Nat.leb_le in Hreq.

    repeat (split; simpl; auto).
    - rewrite (plus_safe_lt _ _).
      destruct (aa_eqdec k (m_sender msg, _spender)).
      + (* (m_sender msg, _spender) = k*)
        rewrite (AA2V.get_upd_eq); auto. omega. 
      + (* (m_sender msg, _spender) <> k*)
        rewrite (AA2V.get_upd_neq); auto. apply Hk.
      + auto.
    - rewrite (plus_safe_lt _ _).
      destruct (aa_eqdec k (m_sender msg, _spender)).
       + (* (m_sender msg, _spender) = k*)
        rewrite (AA2V.get_upd_eq); auto. omega. 
      + (* (m_sender msg, _spender) <> k*)
        rewrite (AA2V.get_upd_neq); auto. apply Hk.
      + auto.
    - (* Inv *)
     exists ost.
     rewrite (plus_safe_lt _ _); [> idtac | omega].  
     do 2 (split; auto).
   - rewrite (plus_safe_lt _ _); [> idtac | omega].
     rewrite (AA2V.get_upd_eq); auto. 
   Qed.

  Lemma Increaseapproval_dsl_revert:
    forall st env msg this,
      m_func msg = mc_increaseApproval _spender _addValue ->
      INV st env msg ->
      ~ spec_require (funcspec_increaseApproval _spender _addValue this env msg) st ->
      forall result,
        dsl_exec increaseApproval_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.

    unfold INV in Hinv.
    destruct Hinv as [Htotal [Hallwd [ost [Hcontract [Hstopped Hinv]]]]].
    unfold INV_sum_blncs in Hinv.

    unfold funcspec_increaseApproval in Hreq_neg. simpl in Hreq_neg.
     apply Nat.leb_nle in Hreq_neg. 

    generalize (increaseApproval_value_inrange _ _ _ Hfunc);
       intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].
    
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt, dsl_allowed_access in Hexec.

   repeat( try (autorewrite with dsl_proof in Hexec);
    try (rewrite (spender_immutable _ _ _ _) in Hexec);
    try (rewrite (max_uint256_immutable _ _ _ _) in Hexec);
    try (rewrite (addValue_immutable _ _ _ _) in Hexec);
    try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]));
    try (rewrite Hreq_neg in Hexec);
    try (simpl in Hexec).

   rewrite <-Hexec. simpl.
   unfold Stop.
   split. auto.
   unfold INV.
   repeat (split; auto).
   exists ost. 
   repeat (split; auto).
  Qed.

  Close Scope dsl_scope.
End dsl_increaseApproval.

Section dsl_decreaseApproval.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ spender: Expr address }.
  Context `{ _spender: address }.
  Context `{ subValue: Expr uint256 }.
  Context `{ _subValue: uint256 }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ spender_immutable:
               forall this st env msg, spender this st env msg = Valid _spender }.
  Context `{ subValue_immutable:
               forall this st env msg, subValue this st env msg = Valid _subValue }.

  (* DSL representation of approve(), generated from solidity *)
  Definition decreaseApproval_dsl : Stmt :=
    (@uint256 oldValue = allowed[msg.sender][spender] ;
     @if (oldValue < subValue) {
         (@allowed[msg.sender][spender] = zero)
     } else {
         (@allowed[msg.sender][spender] -= subValue)
     } ;
     (@emit Approval(msg.sender, spender, allowed[msg.sender][spender])) ;
     (@return true)
    ).

  (* Manually proved *)
  Lemma decreaseApproval_dsl_sat_spec_1:
    dsl_sat_spec (mc_decreaseApproval _spender _subValue)
                 decreaseApproval_dsl
                 (funcspec_decreaseApproval_1 _spender _subValue).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.
    
    simpl in Hreq.
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt, dsl_allowed_access in Hexec.

     apply Nat.ltb_lt in Hreq.
     
    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite (spender_immutable _ _ _ _) in Hexec);
            try (rewrite (subValue_immutable _ _ _ _) in Hexec);
            try (rewrite (max_uint256_immutable _ _ _ _) in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hreq in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
    
    rewrite <- Hexec; clear Hexec.
    
    repeat (split; simpl; auto).
   - destruct (aa_eqdec k (m_sender msg, _spender)).
      + (* (m_sender msg, _spender) = k*)
        rewrite (AA2V.get_upd_eq); auto.  
      + (* (m_sender msg, _spender) <> k*)
        rewrite (AA2V.get_upd_neq); auto. apply Hk.
   - destruct (aa_eqdec k (m_sender msg, _spender)).
      + (* (m_sender msg, _spender) = k*)
        rewrite (AA2V.get_upd_eq); auto.   omega.
      + (* (m_sender msg, _spender) <> k*)
        rewrite (AA2V.get_upd_neq); auto. apply Hk.
   - (* Inv *)
     exists ost. 
     do 2 (split; auto).
   - rewrite (AA2V.get_upd_eq); auto. 
   Qed.

  Lemma decreaseApproval_dsl_sat_spec_2:
    dsl_sat_spec (mc_decreaseApproval _spender _subValue)
                 decreaseApproval_dsl
                 (funcspec_decreaseApproval_2 _spender _subValue).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.

    generalize (decreaseApproval_value_inrange _ _ _ Hfunc);
      intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].
    
    simpl in Hreq.
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt, dsl_allowed_access in Hexec.

     apply Nat.leb_le in Hreq.
     
    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite (spender_immutable _ _ _ _) in Hexec);
            try (rewrite (subValue_immutable _ _ _ _) in Hexec);
            try (rewrite (max_uint256_immutable _ _ _ _) in Hexec);
            try (rewrite (minus_safe _ _) in Hexec; [> idtac | omega]);
            try (rewrite (plus_safe_lt _ _) in Hexec; [> idtac | omega]);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (rewrite Hreq in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).
    
    rewrite <- Hexec; clear Hexec.
    apply Nat.leb_le in Hreq.

    repeat (split; simpl; auto).
   - destruct (aa_eqdec k (m_sender msg, _spender)).
     + (* (m_sender msg, _spender) = k*)
       rewrite (minus_safe _ _); [> idtac | omega].
        rewrite (AA2V.get_upd_eq); auto.  omega.
      + (* (m_sender msg, _spender) <> k*)
        rewrite (AA2V.get_upd_neq); auto. apply Hk.
   - destruct (aa_eqdec k (m_sender msg, _spender)).
     + (* (m_sender msg, _spender) = k*)
       rewrite (minus_safe _ _); [> idtac | omega].
       rewrite (AA2V.get_upd_eq); auto.
       generalize (Hk (m_sender msg, _spender)).
       intros Hvalue'; destruct Hvalue' as [Hvalue'_lo Hvalue'_hi].
       omega.
      + (* (m_sender msg, _spender) <> k*)
        rewrite (AA2V.get_upd_neq); auto. apply Hk.
   - (* Inv *)
     exists ost. 
     do 2 (split; auto).
   - rewrite (minus_safe _ _); [> idtac | omega].
     rewrite (AA2V.get_upd_eq); auto. 
   Qed.

  Lemma decreaseApproval_dsl_revert:
    forall st env msg this,
      m_func msg = mc_decreaseApproval _spender _subValue ->
      INV st env msg ->
      ~ spec_require (funcspec_decreaseApproval_1 _spender _subValue this env msg) st ->
      ~ spec_require (funcspec_decreaseApproval_2 _spender _subValue this env msg) st ->
      forall result,
        dsl_exec decreaseApproval_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq1_neg Hreq2_neg result Hexec.

    unfold INV in Hinv.
    destruct Hinv as [Htotal [Hallwd [ost [Hcontract [Hstopped Hinv]]]]].
    unfold INV_sum_blncs in Hinv.

    unfold funcspec_decreaseApproval_1 in Hreq1_neg. simpl in Hreq1_neg.
    (* apply Nat.ltb_nlt in Hreq1_neg. *)
    unfold funcspec_decreaseApproval_2 in Hreq2_neg. simpl in Hreq2_neg.
    (* apply Nat.leb_nle in Hreq2_neg. *)

    generalize (decreaseApproval_value_inrange _ _ _ Hfunc);
       intros Hvalue; destruct Hvalue as [Hvalue_lo Hvalue_hi].
    
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt, dsl_allowed_access in Hexec.

    repeat( try (autorewrite with dsl_proof in Hexec);
          try (rewrite (subValue_immutable _ _ _ _) in Hexec);
          try (rewrite (spender_immutable _ _ _ _) in Hexec)).
    
    destruct (Nat.le_decidable _subValue (AA2V.get (st_allowed st) (m_sender msg, _spender))).
    - (* _subValue <= AA2V.get (st_allowed st) (m_sender msg, _spender) *)
       assert (Hfalse: False);
         [> apply Hreq2_neg; auto | inversion Hfalse].
   - (* _subValue > AA2V.get (st_allowed st) (m_sender msg, _spender) *)
       assert (Hfalse: False);
         [> apply Hreq1_neg; auto | inversion Hfalse].
      omega.
  Qed.

  Close Scope dsl_scope.
End dsl_decreaseApproval.

Section dsl_transferOwnership.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ newOwner : Expr address }.
  Context `{ _newOwner: address }.

   (* Arguments are immutable, generated from solidity *)
  Context `{ newOwner_immutable:
               forall this st env msg, newOwner this st env msg = Valid _newOwner }.

  Definition transferOwnership_dsl: Stmt :=
    (@require(msg.sender == owner);
     @owner = newOwner;
     (@emit OwnershipTransferred(msg.sender, newOwner));
     (@return true)
    ).

  (* Manually proved *)
  Lemma transferOwnership_dsl_sat_spec:
    dsl_sat_spec (mc_transferOwnership _newOwner)
                 transferOwnership_dsl
                 (funcspec_transferOwnership _newOwner).
  Proof.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

     unfold INV in Hinv.
    destruct Hinv as [[Htotal_lo Htotal_hi] [Hk [ost [Hcontract [Host_stopped Hsum_blncs]]]]].
    unfold INV_sum_blncs in Hsum_blncs.
    
    simpl in Hreq.
   
    simpl in Hexec.
    unfold dsl_remote_stopped_access, dsl_not, dsl_migratedBalances_access, dsl_le, dsl_balances_access, dsl_sub, dsl_remote_balances_access, dsl_add, dsl_ge,  dsl_eq, dsl_or, dsl_lt, dsl_allowed_access in Hexec.

    apply Nat.eqb_eq in Hreq.
    
    repeat (try (autorewrite with dsl_proof in Hexec);
            try (rewrite (newOwner_immutable _ _ _ _) in Hexec);
            try (rewrite Hreq in Hexec);
            try (rewrite Hcontract in Hexec);
            try (rewrite Host_stopped in Hexec);
            try (unfold dsl_neq in Hexec);
            A2V.msimpl_in Hexec;
            simpl in Hexec).

    
     rewrite <- Hexec; clear Hexec.     

     repeat (split; simpl; auto).     
   - (* Inv *)
      exists ost.
      do 2 (split; auto).    
   - apply Nat.eqb_eq in Hreq. 
     rewrite Hreq. auto.
  Qed.

  Lemma transferOwnership_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transferOwnership _newOwner ->
      INV st env msg ->
      ~ spec_require (funcspec_transferOwnership _newOwner this env msg) st ->
      forall result,
        dsl_exec transferOwnership_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
         intros st env msg this Hfunc Hinv Hreq_neg result Hexec.

    unfold INV in Hinv.
    destruct Hinv as [Htotal [Hallwd [ost [Hcontract [Hstopped Hinv]]]]].
    unfold INV_sum_blncs in Hinv.

    unfold funcspec_approve in Hreq_neg. simpl in Hreq_neg.

    simpl in Hexec.
    apply Nat.eqb_neq in Hreq_neg. rewrite Hreq_neg in Hexec.
    simpl in Hexec.
    rewrite <- Hexec.
    split. auto.
    unfold INV.
    repeat (split; auto).
    exists ost. repeat (split; auto).
  Qed.
  
  Close Scope dsl_scope.
End dsl_transferOwnership.
