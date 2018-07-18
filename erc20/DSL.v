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
Open Scope string_scope.

(* XXX: shall Model.event and .state be generated from solidity? *)
Require Import Model.

(* All notations are defined in dsl_scope. *)
Delimit Scope dsl_scope with dsl.

(* *************** *)
(* DSL definitions *)
(* *************** *)

(* Definition of the primitive DSL statements *)
Inductive PrimitiveStmt :=
| DSL_require (cond: state -> env -> message -> bool)
| DSL_emit (evt: state -> env -> message -> event)
| DSL_balances_upd (addr: state -> env -> message -> address)
                   (expr: state -> env -> message -> uint256)
| DSL_allowed_upd (from: state -> env -> message -> address)
                  (to: state -> env -> message -> address)
                  (expr: state -> env -> message -> uint256)
| DSL_totalSupply_upd (expr: state -> env -> message -> uint256)
| DSL_name_upd (expr: state -> env -> message -> string)
| DSL_decimals_upd (expr: state -> env -> message -> uint8)
| DSL_symbol_upd (expr: state -> env -> message -> string)
| DSL_return (T: Type) (expr: state -> env -> message -> T)
| DSL_ctor
| DSL_nop.
Arguments DSL_return [T].

(* Definition of DSL statements *)
Inductive Stmt :=
| DSL_prim (stmt: PrimitiveStmt)
| DSL_if (cond: state -> env -> message -> bool) (then_stmt: Stmt) (else_stmt: Stmt)
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
    if cond st env msg then
      Next st evts
    else
      Stop st0 (ev_revert this :: nil)

  | DSL_emit evt =>
    Next st (evts ++ (evt st env msg :: nil))

  | DSL_return expr =>
    Stop st (evts ++ (ev_return _ (expr st env msg) :: nil))

  | DSL_balances_upd addr expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st $+ { (addr st env msg) <- (expr st env msg) })
                (st_allowed st))
         evts

  | DSL_allowed_upd from to expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (aa2v_upd_2 (st_allowed st) (from st env msg) (to st env msg) (expr st env msg)))
         evts

  | DSL_totalSupply_upd expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (expr st env msg)
                (st_balances st)
                (st_allowed st))
         evts

  | DSL_name_upd expr =>
    Next (mk_st (st_symbol st)
                (expr st env msg)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (st_allowed st))
         evts

  | DSL_decimals_upd expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (expr st env msg)
                (st_totalSupply st)
                (st_balances st)
                (st_allowed st))
         evts

  | DSL_symbol_upd expr =>
    Next (mk_st (expr st env msg)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (st_allowed st))
         evts

  | DSL_ctor =>
    Next st
         (evts ++ (ev_EIP20 (m_sender msg)
                            (st_totalSupply st)
                            (st_name st)
                            (st_decimals st)
                            (st_symbol st) :: nil))

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
    if cond st env msg then
      dsl_exec then_stmt st0 st env msg this evts
    else
      dsl_exec else_stmt st0 st env msg this evts

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
  (fun (st: state) (env: env) (msg: message) => st_symbol st) : dsl_scope.

Notation "'name'" :=
  (fun (st: state) (env: env) (msg: message) => st_name st) : dsl_scope.

Notation "'decimals'" :=
  (fun (st: state) (env: env) (msg: message) => st_decimals st) : dsl_scope.

Notation "'totalSupply'" :=
  (fun (st: state) (env: env) (msg: message) => st_totalSupply st) : dsl_scope.

Notation "'balances'" :=
  (fun (st: state) (env: env) (msg: message) => st_balances st) : dsl_scope.

Definition dsl_balances_access (addr: state -> env -> message -> address) :=
  fun (st: state) (env: env) (msg: message) =>
    (balances%dsl st env msg) (addr st env msg).
Notation "'balances' '[' addr ']'" :=
  (dsl_balances_access addr): dsl_scope.

Notation "'allowed'" :=
  (fun (st: state) (env: env) (msg: message) => st_allowed st) : dsl_scope.

Definition dsl_allowed_access (from to: state -> env -> message -> address) :=
  fun (st: state) (env: env) (msg: message) =>
    (allowed%dsl st env msg) ((from st env msg), (to st env msg)).
Notation "'allowed' '[' from ']' '[' to ']'" :=
  (dsl_allowed_access from to): dsl_scope.

(* Notations for events (XXX: shall they be generated from solidity?) *)
Notation "'Transfer' '(' from ',' to ',' value ')'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_Transfer (m_sender msg) (from st env msg) (to st env msg) (value st env msg))
    (at level 210): dsl_scope.

Notation "'Approval' '(' owner ',' spender ',' value ')'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_Approval (m_sender msg) (owner st env msg) (spender st env msg) (value st env msg))
    (at level 210): dsl_scope.

(* Notations for solidity expressions *)
Definition dsl_ge :=
  fun x y (st: state) (env: env) (msg: message) =>
    (negb (ltb (x st env msg) (y st env msg))).
Infix ">=" := dsl_ge : dsl_scope.

Definition dsl_lt :=
  fun x y (st: state) (env: env) (msg: message) =>
    ltb (x st env msg) (y st env msg).
Infix "<" := dsl_lt : dsl_scope.

Definition dsl_le :=
  fun x y (st: state) (env: env) (msg: message) =>
    Nat.leb (x st env msg) (y st env msg).
Infix "<=" := dsl_le : dsl_scope.

Definition dsl_eq :=
  fun x y (st: state) (env: env) (msg: message) =>
    (Nat.eqb (x st env msg) (y st env msg)).
Infix "==" := dsl_eq (at level 70): dsl_scope.

Definition dsl_add  :=
  fun x y (st: state) (env: env) (msg: message) =>
    plus_with_overflow (x st env msg) (y st env msg).
Infix "+" := dsl_add : dsl_scope.

Definition dsl_sub :=
  fun x y (st: state) (env: env) (msg: message) =>
    minus_with_underflow (x st env msg) (y st env msg).
Infix "-" := dsl_sub : dsl_scope.

Definition dsl_or :=
  fun x y (st: state) (env: env) (msg: message) =>
    (orb (x st env msg) (y st env msg)).
Infix "||" := dsl_or : dsl_scope.

Notation "'msg.sender'" :=
  (fun (st: state) (env: env) (msg: message) =>
     m_sender msg) : dsl_scope.

Definition otrue := true.
Definition ofalse := false.

Notation "'true'" :=
  (fun (st: state) (env: env) (msg: message) => True) : dsl_scope.
Notation "'false'" :=
  (fun (st: state) (env: env) (msg: message) => False) : dsl_scope.

Notation "'require' '(' cond ')'" :=
  (DSL_require cond) (at level 200) : dsl_scope.
Notation "'emit' evt" :=
  (DSL_emit evt) (at level 200) : dsl_scope.
Notation "'balances' '[' addr ']' '=' expr" :=
  (DSL_balances_upd addr expr) (at level 0) : dsl_scope.
Notation "'balances' '[' addr ']' '+=' expr" :=
  (DSL_balances_upd addr
                    (dsl_add (dsl_balances_access addr) expr))
    (at level 0) : dsl_scope.
Notation "'balances' '[' addr ']' '-=' expr" :=
  (DSL_balances_upd addr
                    (dsl_sub (dsl_balances_access addr) expr))
    (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '=' expr" :=
  (DSL_allowed_upd from to expr) (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '+=' expr" :=
  (DSL_allowed_upd from to
                   (dsl_add (dsl_allowed_access from to) expr))
    (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '-=' expr" :=
  (DSL_allowed_upd from to
                   (dsl_sub (dsl_allowed_access from to) expr))
    (at level 0) : dsl_scope.
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
  (DSL_prim stmt_prim) (at level 200) : dsl_scope.

Notation "'@if' ( cond ) { stmt0 } 'else' { stmt1 }" :=
  (DSL_if cond stmt0 stmt1) (at level 210) : dsl_scope.

Notation "stmt0 ';' stmt1" :=
  (DSL_seq stmt0 stmt1) (at level 220) : dsl_scope.

Notation "'@uint256' x = expr ; stmt" :=
  (let x: state -> env -> message -> uint256 := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@address' x = expr ; stmt" :=
  (let x: state -> env -> message -> address := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@uint8' x = expr ; stmt" :=
  (let x: state -> env -> message -> uint8 := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@string' x = expr ; stmt" :=
  (let x: state -> env -> message -> string := expr in stmt)
    (at level 230, x ident) : dsl_scope.


(* *************************************************************** *)
(* Each section below represents a ERC20 function in DSL and prove *)
(* the DSL representation does implement the specification.        *)
(* *************************************************************** *)

Require Import Spec.

Definition dsl_sat_spec (fcall: mcall)
                        (fdsl: Stmt)
                        (fspec: address -> env -> message -> Spec) : Prop :=
  forall st env msg this,
    m_func msg = fcall
    -> spec_require (fspec this env msg) st
    -> forall st0 result,
      dsl_exec fdsl st0 st env msg this nil = result
      -> spec_trans (fspec this env msg) st (ret_st result)
         /\ spec_events (fspec this env msg) (ret_st result) (ret_evts result).

Section dsl_transfer_from.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{from: state -> env -> message -> address}.
  Context `{_from: address}.
  Context `{to: state -> env -> message -> address}.
  Context `{_to: address}.
  Context `{value: state -> env -> message -> uint256}.
  Context `{_value: uint256}.

  Context `{max_uint256: state -> env -> message -> uint256}.

  (* Arguments are immutable, generated from solidity *)
  Context `{from_immutable: forall st env msg, from st env msg = _from}.
  Context `{to_immutable: forall st env msg, to st env msg = _to}.
  Context `{value_immutable: forall st env msg, value st env msg = _value}.
  Context `{max_uint256_immutable: forall st env msg, max_uint256 st env msg = MAX_UINT256}.

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
    forall (m: state -> a2v) st env msg,
      m_func msg = mc_transferFrom _from _to _value ->
      (_from = _to \/ (_from <> _to /\ (m st _to <= MAX_UINT256 - _value)))%nat ->
      ((from == to) ||
       ((fun st env msg => m st (to st env msg)) <= max_uint256 - value))%dsl st env msg = otrue.
  Proof.
    intros m st env msg Hmcall Hnat.

    apply transferFrom_value_inrange in Hmcall.
    destruct Hmcall as [_ Hvalue].

    unfold "=="%dsl, "<="%dsl, "||"%dsl, "||"%bool, "-"%dsl.
    rewrite (from_immutable st env msg),
            (to_immutable st env msg),
            (value_immutable st env msg),
            (max_uint256_immutable st env msg).
    destruct Hnat.
    - rewrite H. rewrite (Nat.eqb_refl _). reflexivity.
    - destruct H as [Hneq Hle].
      apply Nat.eqb_neq in Hneq. rewrite Hneq.
      apply Nat.leb_le.
      rewrite (minus_safe _ _ Hvalue); auto.
  Qed.

  Lemma transferFrom_cond_dec:
    forall st,
      Decidable.decidable
        (_from = _to \/ _from <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat).
  Proof.
    intros.
    apply Decidable.dec_or.
    - apply Nat.eq_decidable.
    - apply Decidable.dec_and.
      + apply neq_decidable.
      + apply Nat.le_decidable.
  Qed.

  Lemma transferFrom_cond_impl:
    forall st env msg,
      m_func msg = mc_transferFrom _from _to _value ->
      ~ (_from = _to \/ _from <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat) ->
      (((from == to)
        || ((fun (st : state) (env : Model.env) (msg : message) =>
               st_balances st (to st env msg)) <= max_uint256 - value)) st env msg) = ofalse.
  Proof.
    intros st env msg Hfunc Hneg.

    apply transferFrom_value_inrange in Hfunc.
    destruct Hfunc as [_ Hvalue].

    unfold "=="%dsl, "||"%dsl, "||"%bool, "<="%dsl, "-"%dsl.
    rewrite (from_immutable _ _ _).
    rewrite (to_immutable _ _ _).
    rewrite (value_immutable _ _ _).
    rewrite (max_uint256_immutable _ _ _).

    apply (Decidable.not_or _ _) in Hneg.
    destruct Hneg as [Hneq Hneg].

    apply Nat.eqb_neq in Hneq.
    rewrite Hneq; simpl.

    assert (Hvalue': (MAX_UINT256 >= _value)%nat);
      auto.
    rewrite (minus_safe _ _ Hvalue').

    apply (Decidable.not_and _ _ (neq_decidable _ _)) in Hneg.
    destruct Hneg.
    - apply Nat.eqb_neq in Hneq. apply H in Hneq. inversion Hneq.
    - apply not_le in H.
      apply Nat.leb_gt.
      auto.
  Qed.

  (* Manually proved *)
  Lemma transferFrom_dsl_sat_spec_1:
    dsl_sat_spec (mc_transferFrom _from _to _value)
                 transferFrom_dsl
                 (funcspec_transferFrom_1 _from _to _value).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec.

    simpl in Hreq.
    destruct Hreq as [Hreq_blncs_lo [Hreq_blncs_hi [Hreq_allwd_lo Hreq_allwd_hi]]].
    apply Nat.leb_le in Hreq_blncs_lo.
    generalize (nat_nooverflow_dsl_nooverflow _ st env msg Hfunc Hreq_blncs_hi).
    clear Hreq_blncs_hi. intros Hreq_blncs_hi.
    apply Nat.leb_le in Hreq_allwd_lo.
    apply Nat.ltb_lt in Hreq_allwd_hi.

    simpl in Hexec.
    unfold ">="%dsl, dsl_balances_access in Hexec.
    rewrite (Nat.ltb_antisym _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (from_immutable _ _ _) in Hexec.
    rewrite Hreq_blncs_lo in Hexec.
    simpl in Hexec.

    rewrite Hreq_blncs_hi in Hexec.
    simpl in Hexec.

    unfold dsl_allowed_access in Hexec.
    rewrite (Nat.ltb_antisym _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (from_immutable _ _ _) in Hexec.
    rewrite Hreq_allwd_lo in Hexec.
    simpl in Hexec.

    unfold "<"%dsl in Hexec; simpl in Hexec.
    rewrite (max_uint256_immutable _ _ _) in Hexec.
    rewrite (from_immutable _ _ _) in Hexec.
    rewrite Hreq_allwd_hi in Hexec.
    simpl in Hexec.

    unfold funcspec_transferFrom_1.
    rewrite <- Hexec; clear Hexec.
    unfold "+"%dsl, "-"%dsl.
    repeat rewrite (value_immutable _ _ _).
    repeat rewrite (from_immutable _ _ _).
    repeat rewrite (to_immutable _ _ _).
    repeat (split; simpl; auto).
  Qed.

  Lemma transferFrom_dsl_sat_spec_2:
    dsl_sat_spec (mc_transferFrom _from _to _value)
                 transferFrom_dsl
                 (funcspec_transferFrom_2 _from _to _value).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec.

    simpl in Hreq. destruct Hreq as [Hreq_blncs_lo [Hreq_blncs_hi [Hreq_allwd_lo Hreq_allwd_hi]]].
    generalize (nat_nooverflow_dsl_nooverflow _ st env msg Hfunc Hreq_blncs_hi).
    clear Hreq_blncs_hi. intros Hreq_blncs_hi.
    apply Nat.leb_le in Hreq_blncs_lo.
    apply Nat.leb_le in Hreq_allwd_lo.

    simpl in Hexec.
    unfold ">="%dsl, dsl_balances_access in Hexec.
    rewrite (Nat.ltb_antisym _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (from_immutable _ _ _) in Hexec.
    rewrite Hreq_blncs_lo in Hexec.
    simpl in Hexec.

    rewrite Hreq_blncs_hi in Hexec.
    simpl in Hexec.

    unfold dsl_allowed_access in Hexec.
    rewrite (Nat.ltb_antisym _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (from_immutable _ _ _) in Hexec.
    rewrite Hreq_allwd_lo in Hexec.
    simpl in Hexec.

    unfold "<"%dsl in Hexec; simpl in Hexec.
    rewrite (max_uint256_immutable _ _ _) in Hexec.
    rewrite (from_immutable _ _ _) in Hexec.
    rewrite Hreq_allwd_hi in Hexec.
    rewrite (Nat.ltb_irrefl _) in Hexec.
    simpl in Hexec.

    unfold funcspec_transferFrom_2.
    rewrite <- Hexec.
    unfold "+"%dsl, "-"%dsl.
    repeat rewrite (value_immutable _ _ _).
    repeat rewrite (from_immutable _ _ _).
    repeat rewrite (to_immutable _ _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, transferFrom() must revert to the initial state *)
  Lemma transferFrom_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transferFrom _from _to _value ->
      ~ spec_require (funcspec_transferFrom_1 _from _to _value this env msg) st ->
      ~ spec_require (funcspec_transferFrom_2 _from _to _value this env msg) st ->
      (forall addr0 addr1, (st_allowed st (addr0, addr1) <= MAX_UINT256)%nat) ->
      forall st0 result,
        dsl_exec transferFrom_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    unfold funcspec_transferFrom_1, funcspec_transferFrom_2, ">="%nat.
    intros st env msg this Hfunc Hreq1_neg Hreq2_neg Hallwd_inv st0 result Hexec;
      simpl in Hreq1_neg, Hreq2_neg.

    assert (Hreq1_impl:
              (_value <= st_balances st _from)%nat ->
              (_from = _to \/ _from <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat) ->
              ~(_value <= st_allowed st (_from, m_sender msg) < MAX_UINT256)).
    {
      intros Hvalue.
      apply (Decidable.or_not_l_iff_1 _ _ (transferFrom_cond_dec _)).
      generalize Hvalue; clear Hvalue.
      apply (Decidable.or_not_l_iff_1 _ _ (Nat.le_decidable _ _)).

      apply (Decidable.not_and _ _ (Nat.le_decidable _ _)) in Hreq1_neg.
      destruct Hreq1_neg.
      - left; auto.
      - apply (Decidable.not_and _ _ (transferFrom_cond_dec _)) in H.
        right; auto.
    }
    clear Hreq1_neg.

    assert (Hreq2_impl:
              (_value <= st_balances st _from)%nat ->
              (_from = _to \/ _from <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat) ->
              ~((_value <= st_allowed st (_from, m_sender msg))%nat /\
                st_allowed st (_from, m_sender msg) = MAX_UINT256)).
    {
      intros Hvalue.
      apply (Decidable.or_not_l_iff_1 _ _ (transferFrom_cond_dec _)).
      generalize Hvalue; clear Hvalue.
      apply (Decidable.or_not_l_iff_1 _ _ (Nat.le_decidable _ _)).

      apply (Decidable.not_and _ _ (Nat.le_decidable _ _)) in Hreq2_neg.
      destruct Hreq2_neg.
      - left; auto.
      - apply (Decidable.not_and _ _ (transferFrom_cond_dec _)) in H.
        right; auto.
    }
    clear Hreq2_neg.

    simpl in Hexec.

    destruct (le_dec _value (st_balances st _from)).
    - (* balances[from] >= value *)
      generalize (Hreq1_impl l); clear Hreq1_impl; intros Hreq1_impl.
      generalize (Hreq2_impl l); clear Hreq2_impl; intros Hreq2_impl.

      apply Nat.leb_le in l.

      simpl in Hexec.
      unfold ">="%dsl, dsl_balances_access in Hexec.
      rewrite (Nat.ltb_antisym _ _) in Hexec.
      rewrite (from_immutable _ _ _) in Hexec.
      rewrite (value_immutable _ _ _) in Hexec.
      rewrite l in Hexec; simpl in Hexec.

      destruct (transferFrom_cond_dec st).
      + (* from = to \/ balances[to] < MAX_UINT256 - value *)
        generalize (Hreq1_impl H); clear Hreq1_impl; intros Hreq1_impl.
        apply (Decidable.not_and _ _ (Nat.le_decidable _ _)) in Hreq1_impl.
        assert (Himpl: (_value <= st_allowed st (_from, m_sender msg))%nat ->
                       ~ (st_allowed st (_from, m_sender msg) < MAX_UINT256)%nat).
        {
          apply Decidable.or_not_l_iff_1.
          - apply Nat.le_decidable.
          - auto.
        }
        clear Hreq1_impl; rename Himpl into Hreq1_impl.

        generalize (Hreq2_impl H); clear Hreq2_impl; intros Hreq2_impl.
        apply (Decidable.not_and _ _ (Nat.le_decidable _ _)) in Hreq2_impl.
        assert(Himpl: (_value <= st_allowed st (_from, m_sender msg))%nat ->
                      st_allowed st (_from, m_sender msg) <> MAX_UINT256).
        {
          apply Decidable.or_not_l_iff_1.
          - apply Nat.le_decidable.
          - auto.
        }
        clear Hreq2_impl; rename Himpl into Hreq2_impl.

        generalize (nat_nooverflow_dsl_nooverflow _ _ env msg Hfunc H); intros Hcond.
        unfold dsl_allowed_access in Hexec.
        rewrite Hcond in Hexec; simpl in Hexec; clear Hcond.

        rewrite (from_immutable _ _ _) in Hexec.
        rewrite (value_immutable _ _ _) in Hexec.

        destruct (le_dec _value (st_allowed st (_from, m_sender msg))).
        * (* allowed[from][msg.sender] >= value *)
          generalize (Hreq1_impl l0); clear Hreq1_impl; intros Hreq1_impl.
          generalize (Hreq2_impl l0); clear Hreq2_impl; intros Hreq2_impl.

          apply not_lt in Hreq1_impl.
          apply Nat.lt_gt_cases in Hreq2_impl.
          destruct Hreq2_impl.
          {
            unfold ">="%nat in Hreq1_impl. auto.
            apply (Nat.lt_le_trans _ _ _ H0) in Hreq1_impl.
            apply Nat.lt_irrefl in Hreq1_impl.
            inversion Hreq1_impl.
          }
          {
            generalize (Hallwd_inv _from (m_sender msg)).
            intros Hle.
            apply (Nat.le_lt_trans _ _ _ Hle) in H0.
            apply Nat.lt_irrefl in H0.
            inversion H0.
          }

        * (* allowed[from][msg.sender] < value *)
          apply not_le in n.
          apply Nat.ltb_lt in n.
          rewrite n in Hexec; simpl in Hexec.

          rewrite <- Hexec.
          split; auto.

      + (* from <> to /\ balances[to] >= MAX_UINT256 + value *)
        apply (transferFrom_cond_impl st env msg Hfunc) in H.
        rewrite H in Hexec; simpl in Hexec.

        rewrite <- Hexec.
        split; auto.

    - (* balances[from] < value *)
      apply Nat.leb_nle in n.

      simpl in Hexec.
      unfold ">="%dsl, dsl_balances_access in Hexec.
      rewrite (Nat.ltb_antisym _ _) in Hexec.
      rewrite (from_immutable _ _ _) in Hexec.
      rewrite (value_immutable _ _ _) in Hexec.
      rewrite n in Hexec; simpl in Hexec.

      rewrite <- Hexec.
      split; auto.
  Qed.

  Close Scope dsl_scope.
End dsl_transfer_from.

Section dsl_transfer.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{to: state -> env -> message -> address}.
  Context `{_to: address}.
  Context `{value: state -> env -> message -> uint256}.
  Context `{_value: uint256}.
  Context `{max_uint256: state -> env -> message -> uint256}.

  (* Arguments are immutable, generated from solidity *)
  Context `{to_immutable: forall st env msg, to st env msg = _to}.
  Context `{value_immutable: forall st env msg, value st env msg = _value}.
  Context `{max_uint256_immutable: forall st env msg, max_uint256 st env msg = MAX_UINT256}.

  (* DSL representation of transfer(), generated from solidity *)
  Definition transfer_dsl : Stmt :=
    (@require(balances[msg.sender] >= value) ;
     @require((msg.sender == to) || (balances[to] <= max_uint256 - value)) ;
     @balances[msg.sender] -= value ;
     @balances[to] += value ;
     (@emit Transfer(msg.sender, to, value)) ;
     (@return true)
    ).

  (* Auxiliary lemmas *)
  Lemma nat_nooverflow_dsl_nooverflow':
    forall (m: state -> a2v) st env msg,
      m_func msg = mc_transfer _to _value ->
      (m_sender msg = _to \/ (m_sender msg <> _to /\ (m st _to <= MAX_UINT256 - _value)))%nat ->
      ((msg.sender == to) ||
       ((fun st env msg => m st (to st env msg)) <= max_uint256 - value))%dsl st env msg = otrue.
  Proof.
    intros m st env msg Hfunc Hnat.

    apply transfer_value_inrange in Hfunc.
    destruct Hfunc as [_ Hvalue].

    unfold "||"%dsl, "||"%bool, "=="%dsl, "<="%dsl, "-"%dsl.
    rewrite (to_immutable st env msg),
            (max_uint256_immutable st env msg),
            (value_immutable st env msg).
    destruct Hnat.
    - rewrite H. rewrite (Nat.eqb_refl _). reflexivity.
    - destruct H as [Hneq Hle].
      apply Nat.eqb_neq in Hneq. rewrite Hneq.
      assert (Hlo: (MAX_UINT256 >= _value)%nat);
        auto.
      rewrite (minus_safe _ _ Hlo).
      apply Nat.leb_le in Hle. exact Hle.
  Qed.

  Lemma transfer_cond_impl:
    forall st env msg,
      m_func msg = mc_transfer _to _value ->
      m_sender msg <> _to /\
      ~ (m_sender msg <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat) ->
      (((fun (_ : state) (_ : Model.env) (msg : message) => m_sender msg) == to)
       || ((fun (st : state) (env : Model.env) (msg : message) =>
              st_balances st (to st env msg)) <= max_uint256 - value)) st env msg = ofalse.
  Proof.
    intros st env msg Hfunc Hcond.

    apply transfer_value_inrange in Hfunc.
    destruct Hfunc as [_ Hvalue].

    unfold "=="%dsl, "||"%dsl, "||"%bool, "<="%dsl, "-"%dsl.
    rewrite (value_immutable _ _ _).
    rewrite (to_immutable _ _ _).
    rewrite (max_uint256_immutable _ _ _).
    rewrite (minus_safe _ _ Hvalue).

    destruct Hcond as [Hneq Heq].
    apply Nat.eqb_neq in Hneq; rewrite Hneq; simpl.

    apply (Decidable.not_and _ _ (neq_decidable _ _)) in Heq.
    destruct Heq.

    - apply Nat.eqb_neq in Hneq.
      apply H in Hneq; inversion Hneq.

    - apply not_le in H.
      apply Nat.leb_gt.
      auto.
  Qed.

  (* Manually proved *)
  Lemma transfer_dsl_sat_spec:
    dsl_sat_spec (mc_transfer _to _value)
                 transfer_dsl
                 (funcspec_transfer _to _value).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec.

    unfold funcspec_transfer in Hreq; simpl in Hreq.
    destruct Hreq as [Hreq_blncs_lo Hreq_blncs_hi].
    unfold ">="%nat in Hreq_blncs_lo. apply Nat.leb_le in Hreq_blncs_lo.
    generalize(nat_nooverflow_dsl_nooverflow' _ st env msg Hfunc Hreq_blncs_hi).
    clear Hreq_blncs_hi. intros Hreq_blncs_hi.

    unfold transfer_dsl in Hexec; simpl in Hexec.
    unfold ">="%dsl, dsl_balances_access in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (Nat.ltb_antisym _ _) in Hexec.
    rewrite Hreq_blncs_lo in Hexec; simpl in Hexec.

    rewrite Hreq_blncs_hi in Hexec. simpl in Hexec.

    unfold funcspec_transfer.
    rewrite <- Hexec.
    unfold "+"%dsl, "-"%dsl.
    repeat rewrite (value_immutable _ _ _).
    repeat rewrite (to_immutable _ _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, transfer() must revert to the initial state *)
  Lemma transfer_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transfer _to _value ->
      ~ spec_require (funcspec_transfer _to _value this env msg) st ->
      forall st0 result,
        dsl_exec transfer_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.

    simpl in Hreq_neg.

    assert (Hreq_impl:
              (_value <= st_balances st (m_sender msg))%nat ->
              ~(m_sender msg = _to \/
                m_sender msg <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat)).
    {
      apply (Decidable.or_not_l_iff_1 _ _ (Nat.le_decidable _ _)).
      apply (Decidable.not_and _ _ (Nat.le_decidable _ _)) in Hreq_neg.
      auto.
    }
    clear Hreq_neg.

    simpl in Hexec.
    destruct (le_dec _value (st_balances st (m_sender msg))).
    - (* balances[msg.sender] >= value *)
      generalize (Hreq_impl l); clear Hreq_impl; intros Hreq.
      apply Decidable.not_or in Hreq.

      apply Nat.leb_le in l.

      simpl in Hexec.
      unfold ">="%dsl, dsl_balances_access in Hexec.
      rewrite (value_immutable _ _ _) in Hexec.
      rewrite (Nat.ltb_antisym _ _) in Hexec.
      rewrite l in Hexec; simpl in Hexec.

      apply (transfer_cond_impl st env msg Hfunc) in Hreq.
      rewrite Hreq in Hexec; clear Hreq; simpl in Hexec.

      rewrite <- Hexec.
      split; auto.

    - (* balances[msg.sender] < value *)
      apply not_le in n.
      apply Nat.leb_gt in n.

      simpl in Hexec.
      unfold ">="%dsl, dsl_balances_access in Hexec.
      rewrite (value_immutable _ _ _) in Hexec.
      rewrite (Nat.ltb_antisym _ _) in Hexec.
      rewrite n in Hexec; simpl in Hexec.

      rewrite <- Hexec.
      split; auto.
  Qed.

  Close Scope dsl_scope.
End dsl_transfer.

Section dsl_balanceOf.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ owner: state -> env -> message -> address }.
  Context `{ _owner: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ owner_immutable: forall st env msg, owner st env msg = _owner }.

  (* DSL representation of transfer(), generated from solidity *)
  Definition balanceOf_dsl : Stmt :=
    (@return balances[owner]).

  (* Manually proved *)
  Lemma balanceOf_dsl_sat_spec:
    dsl_sat_spec (mc_balanceOf _owner)
                 balanceOf_dsl
                 (funcspec_balanceOf _owner).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this _ Hreq st0 result Hexec.

    simpl in Hexec.
    unfold funcspec_balanceOf.
    rewrite <- Hexec.
    unfold dsl_balances_access.
    rewrite (owner_immutable _ _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, balanceOf() must revert to the initial state *)
  Lemma balanceOf_dsl_revert:
    forall st env msg this,
      m_func msg = mc_balanceOf _owner ->
      ~ spec_require (funcspec_balanceOf _owner this env msg) st ->
      forall st0 result,
        dsl_exec balanceOf_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this _ Hreq_neg st0 result Hexec.
    simpl in Hreq_neg.
    apply (proj1 Decidable.not_true_iff) in Hreq_neg.
    inversion Hreq_neg.
  Qed.

  Close Scope dsl_scope.
End dsl_balanceOf.

Section dsl_approve.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ spender: state -> env -> message -> address }.
  Context `{ _spender: address }.
  Context `{ value: state -> env -> message -> uint256 }.
  Context `{ _value: uint256 }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ spender_immutable: forall st env msg, spender st env msg = _spender }.
  Context `{ value_immutable: forall st env msg, value st env msg = _value }.

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
    unfold dsl_sat_spec.
    intros st env msg this _ Hreq st0 result Hexec.

    simpl in Hreq.
    simpl in Hexec.
    unfold funcspec_approve.
    rewrite <- Hexec.
    repeat rewrite (spender_immutable _ _ _).
    repeat rewrite (value_immutable _ _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, approve() must revert to the initial state *)
  Lemma approve_dsl_revert:
    forall st env msg this,
      m_func msg = mc_approve _spender _value ->
      ~ spec_require (funcspec_approve _spender _value this env msg) st ->
      forall st0 result,
        dsl_exec approve_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this _ Hreq_neg st0 result Hexec.
    simpl in Hreq_neg.
    apply (proj1 Decidable.not_true_iff) in Hreq_neg.
    inversion Hreq_neg.
  Qed.

  Close Scope dsl_scope.
End dsl_approve.

Section dsl_allowance.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ owner: state -> env -> message -> address }.
  Context `{ _owner: address }.
  Context `{ spender: state -> env -> message -> address }.
  Context `{ _spender: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ owner_immutable: forall st env msg, owner st env msg = _owner }.
  Context `{ spender_immutable: forall st env msg, spender st env msg = _spender }.

  (* DSL representation of transfer(), generated from solidity *)
  Definition allowance_dsl : Stmt :=
    (@return allowed[owner][spender]).

  (* Manually proved *)
  Lemma allowance_dsl_sat_spec:
    dsl_sat_spec (mc_allowance _owner _spender)
                 allowance_dsl
                 (funcspec_allowance _owner _spender).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this _ Hreq st0 result Hexec.

    simpl in Hexec.
    unfold funcspec_allowance.
    rewrite <- Hexec.
    unfold dsl_allowed_access.
    rewrite (owner_immutable _ _ _).
    rewrite (spender_immutable _ _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, allowance() must revert to the initial state *)
  Lemma allowance_dsl_revert:
    forall st env msg this,
      m_func msg = mc_allowance _owner _spender ->
      ~ spec_require (funcspec_allowance _owner _spender this env msg) st ->
      forall st0 result,
        dsl_exec allowance_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this _ Hreq_neg st0 result Hexec.
    simpl in Hreq_neg.
    apply (proj1 Decidable.not_true_iff) in Hreq_neg.
    inversion Hreq_neg.
  Qed.

  Close Scope dsl_scope.
End dsl_allowance.

Section dsl_constructor.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ initialAmount : state -> env -> message -> uint256 }.
  Context `{ _initialAmount: uint256 }.
  Context `{ decimalUnits : state -> env -> message -> uint8 }.
  Context `{ _decimalUnits: uint8 }.
  Context `{ tokenName: state -> env -> message -> string }.
  Context `{ _tokenName: string }.
  Context `{ tokenSymbol: state -> env -> message -> string }.
  Context `{ _tokenSymbol: string }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ initialAmount_immutable: forall st env msg, initialAmount st env msg = _initialAmount }.
  Context `{ decimalUnits_immutable: forall st env msg, decimalUnits st env msg = _decimalUnits }.
  Context `{ tokenName_immutable: forall st env msg, tokenName st env msg = _tokenName }.
  Context `{ tokenSymbol_immutable: forall st env msg, tokenSymbol st env msg = _tokenSymbol }.

  (* DSL representation of constructor, generated from solidity *)
  Definition ctor_dsl : Stmt :=
    (@balances[msg.sender] = initialAmount ;
     @totalSupply = initialAmount ;
     @name = tokenName ;
     @decimals = decimalUnits ;
     @symbol = tokenSymbol ;
     @ctor
    ).

  (* Manually proved *)
  Lemma ctor_dsl_sat_spec:
    forall st,
      st_balances st = $0 ->
      st_allowed st = $0 ->
      forall env msg this,
        m_func msg = mc_EIP20 _initialAmount _tokenName _decimalUnits _tokenSymbol ->
        spec_require (funcspec_EIP20 _initialAmount _tokenName _decimalUnits _tokenSymbol this env msg) st ->
        forall st0 result,
          dsl_exec ctor_dsl st0 st env msg this nil = result ->
          spec_trans (funcspec_EIP20 _initialAmount _tokenName _decimalUnits _tokenSymbol this env msg) st (ret_st result) /\
          spec_events (funcspec_EIP20 _initialAmount _tokenName _decimalUnits _tokenSymbol this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st Hblns_init Hallwd_init env msg this _ Hreq st0 result Hexec.

    simpl in Hexec.
    simpl.
    rewrite <- Hexec.
    repeat rewrite (initialAmount_immutable _ _ _).
    repeat rewrite (decimalUnits_immutable _ _ _).
    repeat rewrite (tokenName_immutable _ _ _).
    repeat rewrite (tokenSymbol_immutable _ _ _).
    rewrite Hblns_init.
    rewrite Hallwd_init.
    repeat (split; auto).
  Qed.

  Close Scope dsl_scope.
End dsl_constructor.