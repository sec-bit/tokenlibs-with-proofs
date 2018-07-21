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

Definition dsl_lt  := dsl_op Nat.ltb.
Definition dsl_ge x y e m := negb <$> dsl_lt x y e m.
Definition dsl_le  := dsl_op Nat.leb.
Definition dsl_eq  := dsl_op Nat.eqb.
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

Definition get_evl (sevl : eventlist + eventlist) : eventlist :=
  match sevl with
  | inr evl => evl
  | inl evl => evl
  end.

Definition dsl_sat_spec (fcall: mcall)
                        (fdsl: Stmt)
                        (fspec: address -> env -> message -> Spec) : Prop :=
  forall st env msg this,
    m_func msg = fcall
    -> spec_require (fspec this env msg) st
    -> forall st0 result,
      dsl_exec fdsl st0 env msg this nil = result
      -> spec_trans (fspec this env msg) st (execState result st)
        /\ spec_events (fspec this env msg) (execState result st)
                      (get_evl (evalState result st)).

Ltac simpl_rewrite':=
  match goal with
  | H: ?x = Datatypes.true |- context[?x] =>
    repeat rewrite H; simpl
  | H: ?x = Datatypes.false |- context[?x] =>
    repeat rewrite H; simpl
  | H: ?x <=? ?y = _ |- context[negb (?y <? ?x)] =>
    rewrite Nat.leb_antisym in H; repeat rewrite H; simpl
  | H: ?x = ?y |- context[?x <? ?y] =>
    assert(x <? y = Datatypes.false) as ?H' by (rewrite H; apply Nat.ltb_irrefl);
    repeat rewrite H'; simpl
  end.

Ltac simpl_rewrite := repeat simpl_rewrite'.

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
  Context `{from_immutable: forall env msg, from env msg = ret _from}.
  Context `{to_immutable: forall env msg, to env msg = ret _to}.
  Context `{value_immutable: forall env msg, value env msg = ret _value}.
  Context `{max_uint256_immutable: forall env msg, max_uint256 env msg = ret MAX_UINT256}.

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
      m_func msg = mc_transferFrom _from _to _value ->
      (_from = _to \/ (_from <> _to /\ (evalState m st _to <= MAX_UINT256 - _value)))%nat ->
      evalState (((from == to) ||
                  ((fun env msg => m <*> to env msg) <= max_uint256 - value))%dsl env msg) st
      = evalState otrue st.
  Proof.
    intros until msg; intros Hmcall Hnat. 
    apply transferFrom_value_inrange in Hmcall.
    destruct Hmcall as [_ Hvalue].
    unfold "=="%dsl, "<="%dsl, "||"%dsl, "||"%bool, "-"%dsl, dsl_op, evalState in *; simpl.
    rewrite (from_immutable env msg),
            (to_immutable env msg),
            (value_immutable env msg),
            (max_uint256_immutable env msg); simpl.
    destruct Hnat.
    - rewrite H, Nat.eqb_refl; simpl.
      match goal with |- context[match ?x with _ => _ end] => destruct x end; auto.
    - destruct H as [Hneq Hle].
      apply Nat.eqb_neq in Hneq. rewrite Hneq.
      destruct runState eqn:RUN; simpl in *.
      apply Nat.leb_le; auto.
  Qed.

  Lemma transferFrom_cond_dec:
    forall st,
      Decidable.decidable
        (_from = _to \/ _from <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat).
  Proof.
    intros. apply Decidable.dec_or.
    - apply Nat.eq_decidable.
    - apply Decidable.dec_and; auto using neq_decidable, Nat.le_decidable.
  Qed.

  Lemma transferFrom_cond_impl:
    forall st env msg,
      m_func msg = mc_transferFrom _from _to _value ->
      ~ (_from = _to \/ _from <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat) ->
      evalState (((from == to) ||
                  ((fun env msg => balances env msg <*> to env msg) <= max_uint256 - value))%dsl env msg) st
      = evalState ofalse st.
  Proof.
    intros st env msg Hfunc Hneg.
    apply transferFrom_value_inrange in Hfunc.
    destruct Hfunc as [_ Hvalue].
    unfold "=="%dsl, "||"%dsl, "||"%bool, "<="%dsl, "-"%dsl, dsl_op.
    rewrite (from_immutable _ _).
    rewrite (to_immutable _ _).
    rewrite (value_immutable _ _).
    rewrite (max_uint256_immutable _ _).
    simpl.
    apply (Decidable.not_or _ _) in Hneg.
    destruct Hneg as [Hneq Hneg].

    apply Nat.eqb_neq in Hneq.
    destruct beq_nat eqn:EQ. discriminate.

    assert (Hvalue': (MAX_UINT256 >= _value)%nat) by auto.

    apply (Decidable.not_and _ _ (neq_decidable _ _)) in Hneg.
    cbn. destruct Hneg.
    - apply Nat.eqb_neq in EQ. contradiction.
    - apply Nat.leb_nle. auto.
  Qed.
  

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
    generalize (nat_nooverflow_dsl_nooverflow (ret (st_balances st)) st env msg Hfunc Hreq_blncs_hi).
    clear Hreq_blncs_hi. intros Hreq_blncs_hi.
    apply Nat.leb_le in Hreq_allwd_lo.
    apply Nat.ltb_lt in Hreq_allwd_hi.

    unfold execState, evalState in *. simpl in *.
    repeat rewrite from_immutable in *.
    repeat rewrite to_immutable in *.
    repeat rewrite value_immutable in *.
    repeat rewrite max_uint256_immutable in *.
    simpl in Hexec, Hreq_blncs_hi.
    subst result; simpl.
    
    simpl_rewrite.
    repeat (split; auto).
  Qed.

  Lemma transferFrom_dsl_sat_spec_2:
    dsl_sat_spec (mc_transferFrom _from _to _value)
                 transferFrom_dsl
                 (funcspec_transferFrom_2 _from _to _value).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec.

    simpl in Hreq. destruct Hreq as [Hreq_blncs_lo [Hreq_blncs_hi [Hreq_allwd_lo Hreq_allwd_hi]]].
    generalize (nat_nooverflow_dsl_nooverflow (ret (st_balances st)) st env msg Hfunc Hreq_blncs_hi).
    clear Hreq_blncs_hi. intros Hreq_blncs_hi.
    apply Nat.leb_le in Hreq_blncs_lo.
    apply Nat.leb_le in Hreq_allwd_lo.

    unfold execState, evalState in *. simpl in *.
    repeat rewrite from_immutable in *.
    repeat rewrite to_immutable in *.
    repeat rewrite value_immutable in *.
    repeat rewrite max_uint256_immutable in *.
    subst result; simpl in *.
    
    simpl_rewrite. 
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
        dsl_exec transferFrom_dsl st0 env msg this nil = result ->
        runState result st = (inl (ev_revert this :: nil), st0).
  Proof.
    unfold funcspec_transferFrom_1, funcspec_transferFrom_2, ">="%nat.
    intros st env msg this Hfunc Hreq1_neg Hreq2_neg Hallwd_inv st0 result Hexec;
      simpl in Hreq1_neg, Hreq2_neg.

    subst. simpl.
    repeat rewrite from_immutable in *.
    repeat rewrite to_immutable in *.
    repeat rewrite value_immutable in *.
    repeat rewrite max_uint256_immutable in *.
    simpl.

    destruct (negb (st_balances st _from <? _value)) eqn: Hx1; simpl; auto.
    destruct ( (_ =? _) || (_ <=? _))%bool eqn: Hx2; simpl; auto.
    destruct (negb (st_allowed st _ <? _)) eqn: Hx3; simpl; auto.
    destruct (st_allowed st (_from, m_sender msg) <? MAX_UINT256) eqn: Hx4; simpl; auto.
    
    exfalso. apply Hreq1_neg.
    apply orb_true_iff in Hx2.
    split. apply Nat.ltb_ge. apply negb_true_iff. auto.
    split. destruct (Nat.eq_dec _from _to); auto.
      destruct Hx2; [left|right]. apply Nat.eqb_eq; auto.
      split; auto. apply Nat.leb_le. auto.
    split. apply Nat.ltb_ge. apply negb_true_iff. auto.
    apply Nat.ltb_lt. auto.

    exfalso. apply Hreq2_neg.
    split. apply Nat.ltb_ge. apply negb_true_iff. auto.
    split. apply orb_true_iff in Hx2.
      destruct (Nat.eq_dec _from _to); auto.
      destruct Hx2; [left|right]. apply Nat.eqb_eq; auto. 
      split; auto. apply Nat.leb_le; auto.
    split. apply Nat.ltb_ge. apply negb_true_iff. auto.
    apply Nat.ltb_ge in Hx4. apply Nat.le_antisymm; auto.
  Qed.
  
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
  Context `{to_immutable: forall env msg, (to env msg) = ret _to}.
  Context `{value_immutable: forall env msg, (value env msg) = ret _value}.
  Context `{max_uint256_immutable: forall env msg, (max_uint256 env msg) = ret MAX_UINT256}.

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
    forall (m: State a2v) st env msg,
      m_func msg = mc_transfer _to _value ->
      (m_sender msg = _to \/ (m_sender msg <> _to /\ (evalState m st _to <= MAX_UINT256 - _value)))%nat ->
      evalState (((msg.sender == to) ||
                  ((fun env msg => m <*> to env msg) <= max_uint256 - value))%dsl env msg) st
      = evalState otrue st.
  Proof.
    intros m st env msg Hfunc Hnat.

    apply transfer_value_inrange in Hfunc.
    destruct Hfunc as [_ Hvalue].

    unfold "||"%dsl, "||"%bool, "=="%dsl, "<="%dsl, "-"%dsl, dsl_op, evalState in *.
    rewrite (to_immutable env msg),
            (max_uint256_immutable env msg),
            (value_immutable env msg).
    destruct Hnat; simpl.
    - rewrite H, Nat.eqb_refl; simpl.
      match goal with |- context[match ?x with _ => _ end] => destruct x end; auto.
    - destruct H as [Hneq Hle].
      apply Nat.eqb_neq in Hneq. rewrite Hneq.
      destruct runState eqn:RUN; simpl in *.
      apply Nat.leb_le; auto.
  Qed.

  Lemma transfer_cond_impl:
    forall st env msg,
      m_func msg = mc_transfer _to _value ->
      m_sender msg <> _to /\
      ~ (m_sender msg <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat) ->
      evalState ((((fun env msg => ret (m_sender msg)) == to) ||
                  (balances [to] <= max_uint256 - value))%dsl env msg) st
      = evalState ofalse st.
  Proof.
    intros st env msg Hfunc Hcond.

    apply transfer_value_inrange in Hfunc.
    destruct Hfunc as [_ Hvalue].
    destruct Hcond as [Hneq Heq].

    unfold "=="%dsl, "||"%dsl, "||"%bool, "<="%dsl, "-"%dsl, dsl_op, evalState.
    rewrite (to_immutable _ _).
    rewrite (value_immutable _ _).
    rewrite (max_uint256_immutable _ _).
    simpl.
    apply Nat.eqb_neq in Hneq. rewrite Hneq. apply Nat.eqb_neq in Hneq.
    apply (Decidable.not_and _ _ (neq_decidable _ _)) in Heq.
    destruct Heq; [contradiction|apply Nat.leb_nle; auto].
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
    generalize(nat_nooverflow_dsl_nooverflow' (ret (st_balances st)) st env msg Hfunc Hreq_blncs_hi).
    clear Hreq_blncs_hi. intros Hreq_blncs_hi.

    subst; simpl. unfold evalState, runState, execState in *; simpl in *.
    repeat rewrite value_immutable in *.
    repeat rewrite to_immutable in *.
    repeat rewrite max_uint256_immutable in *.
    simpl in *.
    simpl_rewrite.
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, transfer() must revert to the initial state *)
  Lemma transfer_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transfer _to _value ->
      ~ spec_require (funcspec_transfer _to _value this env msg) st ->
      forall st0 result,
        dsl_exec transfer_dsl st0 env msg this nil = result ->
        runState result st = (inl (ev_revert this :: nil), st0).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.
    subst. unfold runState; simpl in *.
    repeat rewrite to_immutable in *.
    repeat rewrite value_immutable in *.
    repeat rewrite max_uint256_immutable in *.
    simpl.

    destruct (negb (st_balances st _ <? _)) eqn: Hx1; simpl; auto.
    destruct ((_ =? _) || (_ <=? _))%bool eqn: Hx2; simpl; auto.
    
    exfalso. apply Hreq_neg.
    apply orb_true_iff in Hx2.
    split. apply Nat.ltb_ge. apply negb_true_iff. auto.
    destruct (Nat.eq_dec (m_sender msg) _to); auto.
    destruct Hx2; [left|right]. apply Nat.eqb_eq; auto.
    split; auto. apply Nat.leb_le; auto.
  Qed.
  
  Close Scope dsl_scope.
End dsl_transfer.

Section dsl_balanceOf.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ owner: env -> message -> State address }.
  Context `{ _owner: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ owner_immutable: forall env msg, owner env msg = ret _owner }.

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
    subst; simpl.
    unfold execState, evalState, runState; simpl.
    rewrite (owner_immutable _ _ ). simpl. auto.
  Qed.

  (* If no require can be satisfied, balanceOf() must revert to the initial state *)
  Lemma balanceOf_dsl_revert:
    forall st env msg this,
      m_func msg = mc_balanceOf _owner ->
      ~ spec_require (funcspec_balanceOf _owner this env msg) st ->
      forall st0 result,
        dsl_exec balanceOf_dsl st0 env msg this nil = result ->
        runState result st = (inl (ev_revert this :: nil), st0).
  Proof.
    intros st env msg this _ Hreq_neg st0 result Hexec.
    simpl in Hreq_neg. contradiction.
  Qed.
  
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
  Context `{ spender_immutable: forall env msg, spender env msg = ret _spender }.
  Context `{ value_immutable: forall env msg, value env msg = ret _value }.

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
    subst; simpl.
    repeat rewrite (spender_immutable _ _).
    repeat rewrite (value_immutable _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, approve() must revert to the initial state *)
  Lemma approve_dsl_revert:
    forall st env msg this,
      m_func msg = mc_approve _spender _value ->
      ~ spec_require (funcspec_approve _spender _value this env msg) st ->
      forall st0 result,
        dsl_exec approve_dsl st0 env msg this nil = result ->
        runState result st = (inl (ev_revert this :: nil), st0).
  Proof.
    intros st env msg this _ Hreq_neg st0 result Hexec.
    simpl in Hreq_neg. contradiction.
  Qed.

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
  Context `{ owner_immutable: forall env msg, (owner env msg) = ret _owner }.
  Context `{ spender_immutable: forall env msg, (spender env msg) = ret _spender }.

  (* DSL representation of transfer(), generated from solidity *)
  Definition allowance_dsl : Stmt :=
    (@return allowed[owner][spender]).

  Lemma allowance_dsl_sat_spec:
    dsl_sat_spec (mc_allowance _owner _spender)
                 allowance_dsl
                 (funcspec_allowance _owner _spender).
  Proof.
    intros st env msg this _ Hreq st0 result Hexec. subst; simpl.
    unfold execState, evalState, runState; simpl.
    rewrite owner_immutable, spender_immutable; auto.
  Qed.

  (* If no require can be satisfied, allowance() must revert to the initial state *)
  Lemma allowance_dsl_revert:
    forall st env msg this,
      m_func msg = mc_allowance _owner _spender ->
      ~ spec_require (funcspec_allowance _owner _spender this env msg) st ->
      forall st0 result,
        dsl_exec allowance_dsl st0 env msg this nil = result ->
        runState result st = (inl (ev_revert this :: nil), st0).
  Proof.
    intros st env msg this _ Hreq_neg st0 result Hexec.
    simpl in Hreq_neg. contradiction.
  Qed.

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
  Context `{ initialAmount_immutable: forall env msg, initialAmount env msg = ret _initialAmount }.
  Context `{ decimalUnits_immutable: forall env msg, decimalUnits env msg = ret _decimalUnits }.
  Context `{ tokenName_immutable: forall env msg, tokenName env msg = ret _tokenName }.
  Context `{ tokenSymbol_immutable: forall env msg, tokenSymbol env msg = ret _tokenSymbol }.

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
          dsl_exec ctor_dsl st0 env msg this nil = result ->
          spec_trans (funcspec_EIP20 _initialAmount _tokenName _decimalUnits _tokenSymbol this env msg) st (execState result st) /\
          spec_events (funcspec_EIP20 _initialAmount _tokenName _decimalUnits _tokenSymbol this env msg) (execState result st) (get_evl (evalState result st)).
  Proof.
    intros st Hblns_init Hallwd_init env msg this _ Hreq st0 result Hexec.
    subst. simpl in *.
    repeat rewrite initialAmount_immutable.
    repeat rewrite decimalUnits_immutable.
    repeat rewrite tokenName_immutable.
    repeat rewrite tokenSymbol_immutable.
    simpl. repeat (split; auto).
    rewrite Hblns_init. auto.
  Qed.

  Close Scope dsl_scope.
End dsl_constructor.
