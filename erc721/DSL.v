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
        Arith
        Bool
        Nat
        Omega.

Require Import
        Maps
        Model
        Spec
        Types.

Delimit Scope dsl_scope with dsl. 


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
  address -> State -> Env -> Message -> ExprVal T.

(* Definition of the primitive DSL statements *)
Inductive PrimitiveStmt :=
| DSL_require (cond: Expr bool)
| DSL_emit (evt: Expr Event)
| DSL_tokenOwner_upd (token: Expr uint256)
                     (owner: Expr address)
| DSL_tokenApprovals_upd (token: Expr uint256)
                         (approved: Expr address)
| DSL_ownedTokensCount_upd (owner: Expr address)
                          (count: Expr uint256)
| DSL_operatorApprovals_upd (owner: Expr address)
                            (opeartor: Expr address)
                            (approved: Expr bool)
| DSL_return {T: Type} (expr: Expr T)
| DSL_ctor
| DSL_nop
.

(* Definition of DSL statements *)
Inductive Stmt :=
| DSL_prim (stmt: PrimitiveStmt)
| DSL_if (cond: Expr bool) (then_stmt: Stmt) (else_stmt: Stmt)
| DSL_seq (stmt: Stmt) (stmt': Stmt)
.

(* Result of statement execution *)
Record Result: Type :=
  mk_result {
      ret_st: State;        (* ending state *)
      ret_evts: EventList;  (* generated events *)
      ret_stopped: bool;    (* does the execution have to stop? *)
    }.
(* Shortcut definition of Result that the execution can continue *)
Definition Next (st: State) (evts: EventList) : Result :=
  mk_result st evts false.
(* Shortcut definition of Result that the execution has to stop *)
Definition Stop (st: State) (evts: EventList) : Result :=
  mk_result st evts true.

(* Semantics of the primitive DSL statements *)
Fixpoint dsl_exec_prim
         (stmt: PrimitiveStmt)
         (st0: State)
         (st: State)
         (env: Env) (msg: Message) (this: address)
         (evts: EventList): Result :=
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
    | Valid _expr => Stop st (evts ++ (ev_return _expr :: nil))
    end

  | DSL_nop =>
    Next st evts

  | DSL_ctor =>
    Next st
         (evts ++ (ev_constructor (m_sender msg) :: nil))

  | DSL_tokenOwner_upd token owner =>
    match token this st env msg with
    | Invalid      => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _token =>
      match owner this st env msg with
      | Invalid      => Stop st0 (evts ++ (ev_revert this :: nil))
      | Valid _owner => Next (mk_st (st_tokenOwner st $ { _token <~ _owner })%v2a
                                    (st_tokenApprovals st)
                                    (st_ownedTokensCount st)
                                    (st_operatorApprovals st))
                             evts
      end
    end

  | DSL_tokenApprovals_upd token approved =>
    match token this st env msg with
    | Invalid      => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _token =>
      match approved this st env msg with
      | Invalid         => Stop st0 (evts ++ (ev_revert this :: nil))
      | Valid _approved => Next (mk_st (st_tokenOwner st)
                                       (st_tokenApprovals st $ { _token <~ _approved })%v2a
                                       (st_ownedTokensCount st)
                                       (st_operatorApprovals st))
                                evts
      end
    end

  | DSL_ownedTokensCount_upd owner count =>
    match owner this st env msg with
    | Invalid      => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _owner =>
      match count this st env msg with
      | Invalid      => Stop st0 (evts ++ (ev_revert this :: nil))
      | Valid _count => Next (mk_st (st_tokenOwner st)
                                    (st_tokenApprovals st)
                                    (st_ownedTokensCount st $ { _owner <~ _count })%a2v
                                    (st_operatorApprovals st))
                              evts
      end
    end

  | DSL_operatorApprovals_upd owner operator approved =>
    match owner this st env msg with
    | Invalid      => Stop st0 (evts ++ (ev_revert this :: nil))
    | Valid _owner =>
      match operator this st env msg with
      | Invalid         => Stop st0 (evts ++ (ev_revert this :: nil))
      | Valid _operator =>
        match approved this st env msg with
        | Invalid         => Stop st0 (evts ++ (ev_revert this :: nil))
        | Valid _approved => Next (mk_st (st_tokenOwner st)
                                         (st_tokenApprovals st)
                                         (st_ownedTokensCount st)
                                         (st_operatorApprovals st $ { _owner, _operator <~ _approved }))
                                  evts
        end
      end
    end
  end.

(* Semantics of DSL statements *)
Fixpoint dsl_exec
         (stmt: Stmt)
         (st0: State)
         (st: State)
         (env: Env) (msg: Message) (this: address)
         (evts: EventList) {struct stmt} : Result :=
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

(* ************************************************************* *)
(* Optional notations that make the DSL syntax close to Solidity *)
(* ************************************************************* *)

(* Notations for expressions accessing storage variables *)

Definition dsl_tokenOwner_access (token: Expr uint256) :=
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
    match token this st env msg with
    | Invalid      => Invalid
    | Valid _token => Valid (st_tokenOwner st $ _token)
    end.
Notation "'tokenOwner' '[' token ']'" :=
  (dsl_tokenOwner_access token) (only parsing) : dsl_scope.

Definition dsl_tokenApprovals_access (token: Expr uint256) :=
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
    match token this st env msg with
    | Invalid      => Invalid
    | Valid _token => Valid (st_tokenApprovals st $ _token)
    end.
Notation "'tokenApprovals' '[' token ']'" :=
  (dsl_tokenApprovals_access token) (only parsing) : dsl_scope.

Definition dsl_ownedTokensCount_access (owner: Expr address) :=
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
    match owner this st env msg with
    | Invalid      => Invalid
    | Valid _owner => Valid (st_ownedTokensCount st $ _owner)%a2v
    end.
Notation "'ownedTokensCount' '[' owner ']'" :=
  (dsl_ownedTokensCount_access owner) (only parsing) : dsl_scope.

Definition dsl_operatorApprovals_access (owner operator: Expr address) :=
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
    match owner this st env msg with
    | Invalid      => Invalid
    | Valid _owner =>
      match operator this st env msg with
      | Invalid         => Invalid
      | Valid _operator => Valid (st_operatorApprovals st $ [_owner, _operator])
      end
    end.
Notation "'operatorApprovals' '[' owner ']' '[' operator ']'" :=
  (dsl_operatorApprovals_access owner operator) (only parsing) : dsl_scope.

(* Notations for events *)

Notation "'Transfer' '(' from ',' to ',' token ')'" :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) =>
     match from this st env msg with
     | Invalid     => Invalid
     | Valid _from =>
       match to this st env msg with
       | Invalid   => Invalid
       | Valid _to =>
         match token this st env msg with
         | Invalid      => Invalid
         | Valid _token => Valid (ev_Transfer this _from _to _token)
         end
       end
     end)
    (at level 210, only parsing): dsl_scope.

Notation "'Approval' '(' _owner ',' _approved ',' _token ')'" :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) =>
     match _owner this st env msg with
     | Invalid       => Invalid
     | Valid __owner =>
       match _approved this st env msg with
       | Invalid          => Invalid
       | Valid __approved =>
         match _token this st env msg with
         | Invalid       => Invalid
         | Valid __token => Valid (ev_Approval this __owner __approved __token)
         end
       end
     end)
    (at level 210, only parsing): dsl_scope.

Notation "'ApprovalForAll' '(' _owner ',' _operator ',' _approved ')'" :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) =>
     match _owner this st env msg with
     | Invalid       => Invalid
     | Valid __owner =>
       match _operator this st env msg with
       | Invalid          => Invalid
       | Valid __operator =>
         match _approved this st env msg with
         | Invalid          => Invalid
         | Valid __approved => Valid (ev_ApprovalForAll this __owner __operator __approved)
         end
       end
     end)
    (at level 210, only parsing): dsl_scope.

(* Notations for other solidity expressions *)
Definition dsl_ge (x y: Expr value) :=
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
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
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
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
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
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
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
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
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
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
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x => Valid (negb _x)
    end.
Notation "'!' x" := (dsl_not x) (at level 75, right associativity, only parsing) : dsl_scope.

Definition dsl_add (x y: Expr value) :=
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
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
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
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
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (orb _x _y)
      end
    end.
Infix "||" := dsl_or (only parsing) : dsl_scope.

Definition dsl_and (x y: Expr bool) :=
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
    match x this st env msg with
    | Invalid => Invalid
    | Valid _x =>
      match y this st env msg with
      | Invalid => Invalid
      | Valid _y => Valid (andb _x _y)
      end
    end.
Infix "&&" := dsl_and (only parsing) : dsl_scope.

Notation "'msg.sender'" :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) =>
     Valid (m_sender msg))
    (only parsing): dsl_scope.

Notation "'isContract' '(' account ')'" :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) =>
     match account this st env msg with
     | Invalid        => Invalid
     | Valid _account =>
       match env_contract env _account with
       | Some _ => Valid true
       | _      => Valid false
       end
     end)
    (only parsing) : dsl_scope.

Definition dsl_remote_onERC721Received_call
           (caddr from to: Expr address) (token: Expr uint256) (data: option (Expr bytes)) :=
  fun (this: address) (st: State) (env: Env) (msg: Message) =>
    match caddr this st env msg with
    | Invalid      => Invalid
    | Valid _caddr =>
      match env_contract env _caddr with
      | None   => Invalid
      | Some _ =>
        match from this st env msg with
        | Invalid     => Invalid
        | Valid _from =>
          match to this st env msg with
          | Invalid   => Invalid
          | Valid _to =>
            match token this st env msg with
            | Invalid      => Invalid
            | Valid _token =>
              match data with
              | None =>
                match onERC721Received_oracle _from _to _token None with
                | None     => Invalid
                | Some ret => Valid ret
                end
              | Some _data =>
                match _data this st env msg with
                | Invalid      => Invalid
                | Valid __data =>
                  match onERC721Received_oracle _from _to _token (Some __data) with
                  | None     => Invalid
                  | Some ret => Valid ret
                  end
                end
              end
            end
          end
        end
      end
    end.
Notation "caddr '.onERC721Received' '(' from ',' to ',' token ',' data ')'" :=
  (dsl_remote_onERC721Received_call caddr from to token (Some data))
    (at level 190, only parsing): dsl_scope.
Notation "caddr '.onERC721Received' '(' from ',' to ',' token ')'" :=
  (dsl_remote_onERC721Received_call caddr from to token None)
    (at level 190, only parsing): dsl_scope.

Definition zero :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) => Valid 0).

Definition one :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) => Valid 1).


Definition otrue := true.
Definition ofalse := false.

Notation "'true'" :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) => Valid true)
    (only parsing) : dsl_scope.
Notation "'false'" :=
  (fun (this: address) (st: State) (env: Env) (msg: Message) => Valid false)
    (only parsing) : dsl_scope.

(* Notations for statements *)
Notation "'require' '(' cond ')'" :=
  (DSL_require cond) (at level 200, only parsing) : dsl_scope.

Notation "'emit' evt" :=
  (DSL_emit evt) (at level 200, only parsing) : dsl_scope.

Notation "'return' expr" :=
  (DSL_return expr) (at level 200, only parsing) : dsl_scope.

Notation "'nop'" :=
  (DSL_nop) (at level 200, only parsing) : dsl_scope.

Notation "'ctor'" :=
  DSL_ctor (at level 200, only parsing) : dsl_scope.

Notation "'tokenOwner' '[' _token ']' '=' _owner" :=
  (DSL_tokenOwner_upd _token _owner)
    (at level 0, only parsing) : dsl_scope.

Notation "'tokenApprovals' '[' _token ']' '=' _owner" :=
  (DSL_tokenApprovals_upd _token _owner)
    (at level 0, only parsing) : dsl_scope.

Notation "'ownedTokensCount' '[' _owner ']' '=' _count" :=
  (DSL_ownedTokensCount_upd _owner _count)
    (at level 0, only parsing) : dsl_scope.

Notation "'ownedTokensCount' '[' _owner ']' '+=' _count" :=
  (DSL_ownedTokensCount_upd _owner
                            (dsl_add (dsl_ownedTokensCount_access _owner) _count))
    (at level 0, only parsing) : dsl_scope.

Notation "'ownedTokensCount' '[' _owner ']' '-=' _count" :=
  (DSL_ownedTokensCount_upd _owner
                            (dsl_sub (dsl_ownedTokensCount_access _owner) _count))
    (at level 0, only parsing) : dsl_scope.

Notation "'operatorApprovals' '[' _owner ']' '[' _operator ']' '=' _approved" :=
  (DSL_operatorApprovals_upd _owner _operator _approved)
    (at level 0, only parsing) : dsl_scope.

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

Axiom max_uint256_lt_1:  MAX_UINT256 >= 1.

  
Lemma upd_inc_dec_lt_1:  forall m k,    
   A2V.get m k >= 1 -> A2V.get m k <= MAX_UINT256->  A2V.equal m  (A2V.upd_inc (A2V.upd_dec m k 1) k 1).
Proof.
  intros m k H1 H2.
  unfold A2V.upd_inc.
  A2V.msimpl.
  
  rewrite (minus_safe _ _); [> | auto ].
  rewrite (plus_safe_lt _ _); [> | omega ].
  assert ((A2V.get m k - 1 + 1) = A2V.get m k). omega.
  rewrite H.

  unfold A2V.equal. intros.
  destruct (Nat.eq_dec k k0).
  - (* k = k0 *)
    subst k.
    rewrite A2V.get_upd_eq;  auto.
  - rewrite A2V.get_upd_neq; auto.
    A2V.msimpl.
Qed.

(* *************************************************************** *)
(* Each section below represents a ERC20 function in DSL and prove *)
(* the DSL representation does implement the specification.        *)
(* *************************************************************** *)

Parameter max_uint256: Expr uint256.

Axiom max_uint256_immutable:
  forall this st env msg, max_uint256 this st env msg = Valid MAX_UINT256.

Hint Rewrite
     Nat.ltb_antisym
     Nat.leb_le
     Nat.leb_refl
     max_uint256_immutable
  : dsl_proof.

Section dsl_constructor.
  (* DSL representation of constructor, generated from solidity *)
  Definition ctor_dsl : Stmt :=
    (@ctor
    )%dsl.

  (* Manually proved *)
  Lemma ctor_dsl_sat_spec:
    forall st env msg this,
      spec_require (funcspec_constructor this env msg) st ->
        forall st0 result,
          dsl_exec ctor_dsl st0 st env msg this nil = result ->
          INV (ret_st result) env msg
          /\ spec_trans (funcspec_constructor this env msg) st (ret_st result)
          /\ spec_events (funcspec_constructor this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    unfold funcspec_constructor in *.
    simpl in *.
    rewrite <- Hexec. simpl.
    split.
    + (* INV (ret_st result) env msg *)
      unfold INV. intros owner Howner.
      destruct Hreq as [Hreq_tokenOwner [Hreq_tokenApproval [Hreq_tokenCount Hreq_operatorApproval]]].
      
      rewrite Hreq_tokenCount.
      
      assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))
              = length (V2A.map_filter ( V2A.empty) (fun e : nat * address => snd e =? owner))).
      apply V2A.filter_length_equal. auto.

      rewrite H.

      rewrite V2A.filter_empty.
      A2V.msimpl.
      
    + split; auto.
  Qed.

End dsl_constructor.

Definition dsl_sat_spec (fcall: Mcall)
                        (fdsl: Stmt)
                        (fspec: address -> Env -> Message -> Spec) : Prop :=
  forall st env msg this,
    m_func msg = fcall
    -> spec_require (fspec this env msg) st
    -> forall st0 result,
        dsl_exec fdsl st0 st env msg this nil = result
        -> INV st env msg
        -> INV (ret_st result) env msg
           /\ spec_trans (fspec this env msg) st (ret_st result)
           /\ spec_events (fspec this env msg) st (ret_evts result).

Section dsl_balanceOf.
  Context `{ _owner: Expr address }.
  Context `{ __owner: address }.
  Context `{ owner_immutable:
               forall this st env msg, _owner this st env msg = Valid __owner }.

  Hint Rewrite
       owner_immutable
    : dsl_proof.

  Definition balanceOf_dsl : Stmt :=
    (@require(_owner != zero);
     (@return ownedTokensCount[_owner])
    )%dsl.

    Lemma balanceOf_dsl_sat_spec:
      dsl_sat_spec (mc_balanceOf __owner)
                   balanceOf_dsl
                   (funcspec_balanceOf __owner).
    Proof.
      unfold dsl_sat_spec.
      intros st env msg this Hfunc Hreq st0 result Hexec Hinv. 
      unfold funcspec_balanceOf in *.
      simpl in Hreq.
      apply Nat.eqb_neq in Hreq.

     repeat (
         try(unfold balanceOf_dsl in Hexec);
         try(unfold dsl_neq in Hexec);
         try(autorewrite with dsl_proof in Hexec);
         try(rewrite Hreq in Hexec);
         try(unfold dsl_ownedTokensCount_access in Hexec);
         try(autorewrite with dsl_proof in Hexec);
         try(simpl in Hexec)
       ).
      unfold Stop in Hexec.
      
      rewrite <- Hexec.
      simpl in *.
      split; auto.
    Qed.

  Lemma balanceOf_dsl_revert:
    forall st env msg this,
      m_func msg = mc_balanceOf __owner ->
      INV st env msg ->
      ~ spec_require (funcspec_balanceOf __owner this env msg) st ->
      forall result,
        dsl_exec balanceOf_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    unfold funcspec_balanceOf in *.
    simpl in Hreq_neg.
    apply Nat.eq_dne in Hreq_neg.

     repeat (
         try(unfold balanceOf_dsl in Hexec);
         try(unfold dsl_neq in Hexec);
         try(autorewrite with dsl_proof in Hexec);
         try(rewrite Hreq_neg in Hexec);
         try(autorewrite with dsl_proof in Hexec);
         try(simpl in Hexec)
       ).
    
    rewrite <- Hexec.
    simpl in *.
    unfold Stop. 
    split; auto.     
  Qed.  
End dsl_balanceOf.

Section dsl_ownerOf.
  Context `{ _token: Expr uint256 }.
  Context `{ __token: uint256 }.
  Context `{ token_immutable:
               forall this st env msg, _token this st env msg = Valid __token }.

  Hint Rewrite
       token_immutable
    : dsl_proof.

  Definition ownerOf_dsl : Stmt :=
    ( @require(tokenOwner[_token] != zero);
      @address owner = tokenOwner[_token];
     (@return owner)
    )%dsl.

  Lemma ownerOf_dsl_sat_spec:
      dsl_sat_spec (mc_ownerOf __token)
                   ownerOf_dsl
                   (funcspec_ownerOf __token).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.
    unfold funcspec_ownerOf in Hreq.
    simpl in Hreq.
    apply Nat.eqb_neq in Hreq.
                      
     repeat (
         try(unfold ownerOf_dsl in Hexec);
         try(unfold dsl_neq in Hexec);
         try(autorewrite with dsl_proof in Hexec);
         try(rewrite Hreq in Hexec);
         try(autorewrite with dsl_proof in Hexec);
         try(unfold dsl_tokenOwner_access in Hexec);
         try(simpl in Hexec)
       ).
     unfold Stop in Hexec.
     rewrite <- Hexec.
     simpl in *.
     repeat (split; auto).
  Qed.

  Lemma ownerOf_dsl_revert:
    forall st env msg this,
      m_func msg = mc_ownerOf __token ->
      INV st env msg ->
      ~ spec_require (funcspec_ownerOf __token this env msg) st ->
      forall result,
        dsl_exec ownerOf_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfun Hinv Hreq_neg result Hexec.
    unfold funcspec_ownerOf in Hreq_neg.
    simpl in Hreq_neg.
    apply Nat.eq_dne in Hreq_neg.

     repeat (
         try(unfold balanceOf_dsl in Hexec);
         try(unfold dsl_neq in Hexec);
         try(autorewrite with dsl_proof in Hexec);
         try(rewrite Hreq_neg in Hexec);
         try(autorewrite with dsl_proof in Hexec);
         try(unfold dsl_tokenOwner_access in Hexec);
         try(simpl in Hexec)
       ).
    
    rewrite <- Hexec.
    simpl in *.
    unfold Stop. 
    split; auto.         
  Qed.
  
End dsl_ownerOf.

Section dsl_safeTransferFrom_w_data.
  Context `{ _from: Expr address }.
  Context `{ __from: address }.
  Context `{ from_immutable:
               forall this st env msg, _from this st env msg = Valid __from }.

  Context `{ _to: Expr address }.
  Context `{ __to: address }.
  Context `{ to_immutable:
               forall this st env msg, _to this st env msg = Valid __to }.

  Context `{ _token: Expr uint256 }.
  Context `{ __token: uint256 }.
  Context `{ token_immutable:
               forall this st env msg, _token this st env msg = Valid __token }.

  Context `{ _data: Expr bytes }.
  Context `{ __data: bytes }.
  Context `{ data_immutable:
               forall this st env msg, _data this st env msg = Valid __data }.

  Context `{ ERC721_RECEIVED: Expr bytes4 }.
  Context `{ ERC721_RECEIVED_immutable:
               forall this st env msg, ERC721_RECEIVED this st env msg = Valid onERC721Received_succ_ret }.

  Hint Rewrite
       from_immutable
       to_immutable
       token_immutable
       data_immutable
       ERC721_RECEIVED_immutable
    : dsl_proof.

  Definition safeTransferFrom_w_data_dsl : Stmt :=
    (@require(_to != zero);
     @address owner = tokenOwner[_token];
     @require((owner != zero) && (owner == _from));
     @address sender = msg.sender;
     @require((sender == owner) || (sender == tokenApprovals[_token]) || operatorApprovals[owner][sender]);
     @tokenApprovals[_token] = zero;
     @tokenOwner[_token] = _to;
     @if (_from != _to) {
        (@require(ownedTokensCount[_to] <= max_uint256 - one);
         @ownedTokensCount[_from] -= one;
         @ownedTokensCount[_to] += one)
     } else {
        (@nop)
     } ;
     (@emit Transfer(_from, _to, _token));
     @if (isContract(_to)) {
        (@require(_to.onERC721Received(_from, _to, _token, _data) == ERC721_RECEIVED))
     } else {
        (@nop)
     }
    )%dsl.

  Lemma safeTransferFrom_w_data_dsl_sat_spec:
      dsl_sat_spec (mc_safeTransferFrom __from __to __token (Some __data))
                   safeTransferFrom_w_data_dsl
                   (funcspec_safeTransferFrom __from __to __token (Some __data)).
  Proof.
    unfold  dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.
    generalize max_uint256_lt_1. intros max.
    unfold funcspec_safeTransferFrom in *.
    simpl in *.
    destruct Hreq as [Htoken [Htokenfrom [Hsender [Hto [Hcontract Hcount]]]]].
    apply Nat.eqb_neq in Hto.
    apply Nat.eqb_neq in Htoken.
    apply Nat.eqb_eq in Htokenfrom.

    unfold dsl_neq, dsl_and, dsl_eq ,dsl_or, dsl_le,dsl_add,  dsl_sub, dsl_tokenOwner_access,dsl_ownedTokensCount_access, dsl_tokenApprovals_access, dsl_operatorApprovals_access, dsl_remote_onERC721Received_call in Hexec.    

    assert ((m_sender msg =? V2A.get (st_tokenOwner st) __token)
                      || (m_sender msg =? V2A.get (st_tokenApprovals st) __token)
                      || AA2B.get (st_operatorApprovals st)
                                  (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue).
    unfold otrue. unfold orb.
    inversion Hsender.
    apply Nat.eqb_eq in H. rewrite H. auto.
    inversion H.
    destruct H0. apply Nat.eqb_neq in H0. rewrite H0.
    apply Nat.eqb_eq in H1. rewrite H1. auto.
    destruct H0. apply Nat.eqb_neq in H0. rewrite H0.
    destruct H1. apply Nat.eqb_neq in H1. rewrite H1. 
    auto.

    repeat (
        try(unfold zero in Hexec);
     
        try(rewrite Hto in Hexec);
        try(rewrite Htoken in Hexec);
        try(rewrite Htokenfrom in Hexec);
        try(rewrite H in Hexec);
        try(simpl in Hexec);
        try(unfold Next in Hexec);
        try(autorewrite with dsl_proof in Hexec);
        try(V2A.msimpl_in Hexec)
      ).

    destruct (Nat.eq_dec __from __to).
    - (* from = to *)
      subst __from.
      rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      destruct (env_contract env __to).
      + (* Some r *)
        destruct (Hcontract). inversion H0.
        {
          destruct H0. destruct H0.
          rewrite H1 in Hexec.
          rewrite (Nat.eqb_refl _) in Hexec.
          simpl in Hexec.
          rewrite <- Hexec.
          simpl.
          split.
          unfold INV in *.
          intros owner Howner.
          apply Nat.eqb_eq in Htokenfrom.
          
          destruct (Nat.eq_dec __to owner).
          - (* to = owner *)
            subst __to.
            simpl.
            assert (length
    (V2A.map_filter (V2A.upd (st_tokenOwner st) __token (V2A.get (st_tokenOwner st) __token))
                    (fun e0 : nat * address => snd e0 =? owner)) = length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
            apply V2A.filter_length_f_equal.
            intros k. simpl.
            destruct (Nat.eq_dec __token k).
            + (* __token = k *)
              subst __token.
              simpl. V2A.msimpl.
            + (* __token <> k *)
              V2A.msimpl.
            + rewrite H2. apply Hinv. auto.
          - (* to <> owner *)
            simpl.
            
            assert ((length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                            (fun e : nat * address => snd e =? owner))) =
                    length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
            apply V2A.filter_length_f_equal.
            simpl. intros k.
            destruct (Nat.eq_dec __token k).
            + subst __token. V2A.msimpl.
            + V2A.msimpl.
            + rewrite H2. apply Hinv. auto.
          -
            repeat (split; auto).
            apply upd_inc_dec_lt_1.
            unfold INV in *.
              apply Nat.eqb_neq in Htoken.
              apply Nat.eqb_eq in Htokenfrom.
              rewrite Htokenfrom in Htoken.
              rewrite <- Hinv.
              simpl.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __to)) > 0).
              apply V2A.filter_length_exist_nonzero. simpl.
              exists __token. apply Nat.eqb_eq. auto.
              omega. auto.
              simpl in Hcount.
              generalize (ownedTokensCount_in_range __to st). omega.
        }
      + (* None *)
        simpl in Hexec.
        rewrite <- Hexec.
        simpl. split.
        {
          unfold INV in *. intros owner Howner.
          apply Nat.eqb_eq in Htokenfrom.
          
          destruct (Nat.eq_dec __to owner).
          - (* to = owner *)
            subst __to.
            simpl.
            assert (V2A.equal (st_tokenOwner st) (V2A.upd (st_tokenOwner st) __token (V2A.get (st_tokenOwner st) __token))).
            apply V2A.upd_get_equal. auto. auto.

            assert (length
    (V2A.map_filter (V2A.upd (st_tokenOwner st) __token (V2A.get (st_tokenOwner st) __token))
       (fun e0 : nat * address => snd e0 =? owner))  =
                    length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
            apply V2A.filter_length_equal. auto.
            rewrite H1. apply Hinv. auto.
          - (* to <> owner *)
            simpl.
            
            assert ((length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                            (fun e : nat * address => snd e =? owner))) =
                    length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
            apply V2A.filter_length_f_equal.
            simpl. intros k.
            destruct (Nat.eq_dec __token k).
            + subst __token. V2A.msimpl.
            + V2A.msimpl.
            + rewrite H0. apply Hinv. auto.
        }
            repeat (split; auto).
            apply upd_inc_dec_lt_1.
            unfold INV in *.
            apply Nat.eqb_neq in Htoken.
            apply Nat.eqb_eq in Htokenfrom.
            rewrite Htokenfrom in Htoken.
            rewrite <- Hinv.
            simpl.
            assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __to)) > 0).
            apply V2A.filter_length_exist_nonzero. simpl.
            exists __token. apply Nat.eqb_eq. auto.
            omega. auto.
            simpl in Hcount.
            generalize (ownedTokensCount_in_range __to st). omega.
    - (* from <> to *)
      apply Nat.eqb_neq in n.
      rewrite n in Hexec.
      simpl in Hexec.
      
      rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
      generalize n. intros n1.
      apply Nat.eqb_neq in n1. apply Hcount in n1.
      apply Nat.leb_le in n1. rewrite n1 in Hexec.
      autorewrite with dsl_proof in Hexec.
      simpl in Hexec.
      destruct (env_contract env __to).
     {(* Some r *)
       destruct (Hcontract).
       - inversion H0.
       - destruct H0. destruct H0.
         rewrite H1 in Hexec.
         rewrite (Nat.eqb_refl _) in Hexec.
         rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
         rewrite (plus_safe_lt _ _) in Hexec.
         rewrite <- Hexec.
         simpl. apply Nat.eqb_neq in n.
         split.
         + unfold INV in *.
           intros owner Howner.
           apply Nat.eqb_eq in Htokenfrom.
             
              destruct (Nat.eq_dec __to owner).
              { (* to = owner *)
                subst __to.
                A2V.msimpl.
                simpl. A2V.msimpl.
                
                assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token owner)
                                               (fun e : nat * address => snd e =? owner)) =
                length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) +1
                       ).
                apply V2A.filter_length_upd_false_true with __token.
                simpl. auto.
                rewrite Htokenfrom.
                apply Nat.eqb_neq. auto.
                simpl. V2A.msimpl. apply Nat.eqb_eq. auto.
                intros k' Hktoken.
                simpl. V2A.msimpl.

                rewrite H2.
                
                apply Nat.add_cancel_r.
                apply Hinv. auto.
              }
              { (* to <> owner *)
                simpl.
                destruct (Nat.eq_dec __from owner).
                - (* from = owner *)
                  subst __from.
                  simpl in *.
                  A2V.msimpl.
                  assert (length  (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                                  (fun e0 : nat * address => snd e0 =? owner)) =
                          length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) - 1).
                  apply V2A.filter_length_upd_true_false with __token.
                  simpl. apply Nat.eqb_eq in e. auto.
                  simpl. V2A.msimpl. apply Nat.eqb_neq in n0. auto.
                  intros k' Hktoken.
                  simpl. V2A.msimpl.

                  rewrite H2.
                  rewrite e.
                  assert (length (V2A.map_filter (st_tokenOwner st) (fun e0 : nat * address => snd e0 =? owner))  =
                          A2V.get (st_ownedTokensCount st) owner).
                  apply Hinv. auto.
                  rewrite H3. auto.
                - (* from <> owner *)
                  apply Nat.eqb_neq in n.
                  simpl in *.
                  A2V.msimpl.
                  assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                                 (fun e : nat * address => snd e =? owner)) =
                 length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
                  apply V2A.filter_length_f_equal.
                  intros. simpl.
                  destruct (Nat.eq_dec __token k).
                  subst __token. rewrite Htokenfrom. V2A.msimpl.
                  apply Nat.eqb_neq in n0. apply Nat.eqb_neq in n2.
                  rewrite n0,n2. auto.
                  V2A.msimpl.

                  rewrite H2. apply Hinv. auto.
                  
              }
            + repeat (split; auto).
              unfold A2V.upd_inc, A2V.upd_dec.
              rewrite (minus_safe _ _); [> idtac | auto].
              rewrite (plus_safe_lt _ _).
              auto.
              
              A2V.msimpl.
              unfold INV in *.
              apply Nat.eqb_neq in Htoken.
              apply Nat.eqb_eq in Htokenfrom.
              rewrite Htokenfrom in Htoken.
              rewrite <- Hinv.
              simpl.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) > 0).
              apply V2A.filter_length_exist_nonzero. simpl.
              exists __token. apply Nat.eqb_eq. auto.
              
              omega.
              auto.
            + apply Nat.eqb_neq in n.
              simpl. A2V.msimpl.
            + unfold INV in *.
              apply Nat.eqb_neq in Htoken.
              apply Nat.eqb_eq in Htokenfrom.
              rewrite Htokenfrom in Htoken.
              rewrite <- Hinv.
              simpl.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) > 0).
              apply V2A.filter_length_exist_nonzero. simpl.
              exists __token. apply Nat.eqb_eq. auto.
              omega. auto.
        }
        {(* None *)
          apply Nat.eqb_neq in n.
          rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
          rewrite (plus_safe_lt _ _) in Hexec.
          A2V.msimpl_in Hexec.
          rewrite <- Hexec.
          simpl.
          split.
          - unfold INV in *. intros owner Howner.
            destruct (Nat.eq_dec __to owner).
            {(* __to = owner *)
              subst __to.
              simpl. A2V.msimpl.
              assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token owner)(fun e : nat * address => snd e =? owner)) =
                      length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) +1).              
              apply V2A.filter_length_upd_false_true with __token.
              simpl.
              apply Nat.eqb_eq in Htokenfrom. rewrite Htokenfrom.
              apply Nat.eqb_neq in n. rewrite n. auto.
              simpl. V2A.msimpl. apply Nat.eqb_eq. auto.
              intros k' Hktoken.
              simpl. V2A.msimpl.

              rewrite H0.
              apply Nat.add_cancel_r.
              apply Hinv. auto.
            }
            {(* __to <> owner *)
              destruct (Nat.eq_dec __from owner).
              - (* from = owner *)
                subst __from.
                simpl in *.
                A2V.msimpl.
                assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                    (fun e : nat * address => snd e =? owner)) =
                        length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) -1).
                apply V2A.filter_length_upd_true_false with __token.
                simpl. auto.
                simpl. V2A.msimpl. apply Nat.eqb_neq in n0. auto.
                intros k' Hktoken.
                simpl. V2A.msimpl.
                rewrite H0.

                assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) =
                        A2V.get (st_ownedTokensCount st) owner).
                apply Hinv. auto.
                omega.
              - (* from <> owner *)
                simpl. V2A.msimpl. A2V.msimpl.
                assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                               (fun e : nat * address => snd e =? owner)) =
                        length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
                 apply V2A.filter_length_f_equal.
                  intros. simpl.
                  destruct (Nat.eq_dec __token k).
                  subst __token. V2A.msimpl.
                  apply Nat.eqb_eq in Htokenfrom.
                  rewrite Htokenfrom.
                  apply Nat.eqb_neq in n0. apply Nat.eqb_neq in n2.
                  rewrite n0,n2. auto.
                  V2A.msimpl.

                  rewrite H0. apply Hinv. auto.
            }
          - repeat (split; auto).
            unfold A2V.upd_inc, A2V.upd_dec.
            rewrite (minus_safe _ _); [> idtac | auto].
            rewrite (plus_safe_lt _ _).
            A2V.msimpl.
            rewrite A2V.get_upd_neq; auto.
            unfold INV in *.
            
              apply Nat.eqb_neq in Htoken.
              apply Nat.eqb_eq in Htokenfrom.
              rewrite Htokenfrom in Htoken.
              rewrite <- Hinv.
              simpl.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) > 0).
              apply V2A.filter_length_exist_nonzero. simpl.
              exists __token. apply Nat.eqb_eq. auto.
              omega.
              auto.
          - rewrite A2V.get_upd_neq; auto.
          - unfold INV in *.
             apply Nat.eqb_neq in Htoken.
              apply Nat.eqb_eq in Htokenfrom.
              rewrite Htokenfrom in Htoken.
              rewrite <- Hinv.
              simpl.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) > 0).
              apply V2A.filter_length_exist_nonzero. simpl.
              exists __token. apply Nat.eqb_eq. auto.
              omega.
              auto.
        }     
  Qed.

  Lemma safeTransferFrom_w_data_dsl_revert:
    forall st env msg this,
      m_func msg = mc_safeTransferFrom __from __to __token (Some __data) ->
      INV st env msg ->
      ~ spec_require (funcspec_safeTransferFrom __from __to __token (Some __data) this env msg) st ->
      forall result,
        dsl_exec safeTransferFrom_w_data_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    generalize max_uint256_lt_1. intros max.
    unfold funcspec_safeTransferFrom in *.
    simpl in *. 
    unfold dsl_neq, dsl_and, dsl_add, dsl_eq, dsl_or,dsl_le, dsl_ownedTokensCount_access, dsl_sub, dsl_remote_onERC721Received_call, dsl_tokenApprovals_access, dsl_tokenOwner_access, dsl_operatorApprovals_access in Hexec.

    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    destruct (Nat.eq_dec  __to 0).
    - (* __to = 0 *)
      apply Nat.eqb_eq in e.
      rewrite e in Hexec. simpl in Hexec.
      rewrite <- Hexec. 
      split;auto.
    - (* __to <> 0*)
      apply Nat.eqb_neq in n.
      rewrite n in Hexec. simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      destruct (Nat.eq_dec (V2A.get (st_tokenOwner st) __token) 0).
      + (* V2A.get (st_tokenOwner st) __token = 0*)
        apply Nat.eqb_eq in e.
        rewrite e in Hexec. simpl in Hexec.
        rewrite <- Hexec. unfold Stop.
        split;auto.
      + (* V2A.get (st_tokenOwner st) __token <> 0*)
        apply Nat.eqb_neq in n0.
        rewrite n0 in Hexec. simpl in Hexec.
        destruct (Nat.eq_dec (V2A.get (st_tokenOwner st) __token) __from).
        {(* (V2A.get (st_tokenOwner st) __token) =  __from*)
          apply Nat.eqb_eq in e.
          rewrite e in Hexec. simpl in Hexec.
          autorewrite with dsl_proof in Hexec.
          destruct (bool_dec ((m_sender msg =? V2A.get (st_tokenOwner st) __token)
                      || (m_sender msg =? V2A.get (st_tokenApprovals st) __token)
                      || AA2B.get (st_operatorApprovals st)
                                  (V2A.get (st_tokenOwner st) __token, m_sender msg)) otrue).
          - rewrite e0 in Hexec. simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            destruct (Nat.eq_dec __from __to).
            + (* __from = __to *)
              subst __from.
              rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
              autorewrite with dsl_proof in Hexec.
              simpl in Hexec.
              autorewrite with dsl_proof in Hexec.
              destruct (env_contract env __to).
              {(* Some r *)
                destruct (onERC721Received_oracle __to __to __token (Some __data)).
                - destruct (Nat.eq_dec  b  onERC721Received_succ_ret).
                  + subst b. rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
                    
                    assert ((V2A.get (st_tokenOwner st) __token <> 0 /\
                             V2A.get (st_tokenOwner st) __token = __to /\
                             (m_sender msg = V2A.get (st_tokenOwner st) __token \/
                              m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                              m_sender msg = V2A.get (st_tokenApprovals st) __token \/
                              m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                              m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
                              AA2B.get (st_operatorApprovals st)
                                       (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue) /\
                             __to <> 0 /\
                             (Some r = None \/ (exists RS : ReceiverState, Some r = Some RS /\
                                                                           Some onERC721Received_succ_ret = Some onERC721Received_succ_ret)) /\
                             (__to <> __to -> A2V.get (st_ownedTokensCount st) __to <= MAX_UINT256 - 1))).
                    {
                      apply Nat.eqb_neq in n0.
                      apply Nat.eqb_eq in e.
                      split. auto.
                      split. auto.
                      assert ((m_sender msg = V2A.get (st_tokenOwner st) __token \/
                               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                               m_sender msg = V2A.get (st_tokenApprovals st) __token \/
                               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                               m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
                               AA2B.get (st_operatorApprovals st) (V2A.get (st_tokenOwner st) __token, m_sender msg) =
                               otrue)).
                      destruct (Nat.eq_dec (m_sender msg)  (V2A.get (st_tokenOwner st) __token)).
                      - left. auto.
                      - right. destruct (Nat.eq_dec (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                        + left. split;auto.
                        + right.  repeat (split;auto).
                          unfold orb in e0. apply Nat.eqb_neq in n1. apply Nat.eqb_neq in n2.
                          rewrite n1, n2 in e0. auto.
                      - split. auto.
                        apply Nat.eqb_neq in n.  split. auto.
                        split. right. exists r. auto.
                        intros Htoto. contradiction.
                    }
                    contradiction.
                  + apply Nat.eqb_neq in n1. rewrite n1 in Hexec.
                    rewrite <- Hexec. split; auto.
                - rewrite <- Hexec. split; auto.
              }
              {
                contradict Hreq_neg.
                split. apply Nat.eqb_neq in n0. auto.
                split. apply Nat.eqb_eq in e. auto.
                split.
                destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenOwner st) __token)).
                - left. auto.
                - right. destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                  + left. auto.
                  + right. repeat (split; auto).
                    apply Nat.eqb_neq in n1. apply Nat.eqb_neq in n2. rewrite n1,n2 in e0. simpl in e0.
                    auto.
                - split. apply Nat.eqb_neq in n. auto.
                  split. left. auto.
                  intros. contradiction.
              }
            + (* __from <> __to *)
              apply Nat.eqb_neq in n1.
              rewrite n1 in Hexec.
              simpl in Hexec.
              rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
              destruct (le_dec (A2V.get (st_ownedTokensCount st) __to) (MAX_UINT256 - 1)).
              {
                apply Nat.leb_le in l.
                rewrite l in Hexec. simpl in Hexec.
                autorewrite with dsl_proof in Hexec.
                simpl in Hexec.
                autorewrite with dsl_proof in Hexec.
                simpl in Hexec.
                autorewrite with dsl_proof in Hexec.
                simpl in Hexec.
                autorewrite with dsl_proof in Hexec.
                destruct (env_contract env __to).
                {(* Some r *)
                  destruct (onERC721Received_oracle __from __to __token (Some __data)).
                - destruct (Nat.eq_dec  b  onERC721Received_succ_ret).
                  + subst b. rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
                    
                    assert ((V2A.get (st_tokenOwner st) __token <> 0 /\
                             V2A.get (st_tokenOwner st) __token = __from /\
                             (m_sender msg = V2A.get (st_tokenOwner st) __token \/
                              m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                              m_sender msg = V2A.get (st_tokenApprovals st) __token \/
                              m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                              m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
                              AA2B.get (st_operatorApprovals st)
                                       (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue) /\
                             __to <> 0 /\
                             (Some r = None \/
                              (exists RS : ReceiverState,
                                  Some r = Some RS /\
                                  Some onERC721Received_succ_ret = Some onERC721Received_succ_ret)) /\
                             (__from <> __to -> A2V.get (st_ownedTokensCount st) __to <= MAX_UINT256 - 1))).
                    {
                      apply Nat.eqb_neq in n0.
                      apply Nat.eqb_eq in e.
                      split. auto.
                      split. auto.
                      assert ((m_sender msg = V2A.get (st_tokenOwner st) __token \/
                               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                               m_sender msg = V2A.get (st_tokenApprovals st) __token \/
                               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                               m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
                               AA2B.get (st_operatorApprovals st) (V2A.get (st_tokenOwner st) __token, m_sender msg) =
                               otrue)).
                      destruct (Nat.eq_dec (m_sender msg)  (V2A.get (st_tokenOwner st) __token)).
                      - left. auto.
                      - right. destruct (Nat.eq_dec (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                        + left. split;auto.
                        + right.  repeat (split;auto).
                          unfold orb in e0. apply Nat.eqb_neq in n3. apply Nat.eqb_neq in n2.
                          rewrite n3, n2 in e0. auto.
                      - split. auto.
                        apply Nat.eqb_neq in n.  split. auto.
                        split. right. exists r. auto.
                        apply Nat.eqb_neq in n1.
                        apply Nat.leb_le in l. auto.
                    }
                    contradiction.
                  + apply Nat.eqb_neq in n2. rewrite n2 in Hexec.
                    rewrite <- Hexec. split; auto.
                - rewrite <- Hexec. split; auto.
                }
                {
                  contradict Hreq_neg.
                  split. apply Nat.eqb_neq in n0. auto.
                  split. apply Nat.eqb_eq in e. auto.
                  split.
                  destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenOwner st) __token)).
                  - left. auto.
                  - right. destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                    + left. auto.
                    + right. repeat (split; auto).
                      apply Nat.eqb_neq in n3. apply Nat.eqb_neq in n2. rewrite n3, n2 in e0. simpl in e0.
                      auto.
                  - split. apply Nat.eqb_neq in n. auto.
                    split. left. auto.
                    intros. apply Nat.leb_le. auto.
                }
              }
              {
                apply Nat.leb_nle in n2.
                rewrite n2 in Hexec.
                simpl in Hexec.
                rewrite <- Hexec.
                split; auto. 
              }
          - apply not_true_is_false in n1.
            rewrite n1 in Hexec.
            simpl in Hexec.
             rewrite <- Hexec.
             split; auto.
        }
        {(* (V2A.get (st_tokenOwner st) __token) <>  __from*)
          apply Nat.eqb_neq in n1.
          rewrite n1 in Hexec.
          simpl in Hexec.
          rewrite <- Hexec.
             split; auto.
        }
Qed.
   
End dsl_safeTransferFrom_w_data.

Section dsl_safeTransferFrom_wo_data.
  Context `{ _from: Expr address }.
  Context `{ __from: address }.
  Context `{ from_immutable:
               forall this st env msg, _from this st env msg = Valid __from }.

  Context `{ _to: Expr address }.
  Context `{ __to: address }.
  Context `{ to_immutable:
               forall this st env msg, _to this st env msg = Valid __to }.

  Context `{ _token: Expr uint256 }.
  Context `{ __token: uint256 }.
  Context `{ token_immutable:
               forall this st env msg, _token this st env msg = Valid __token }.

  Context `{ ERC721_RECEIVED: Expr bytes4 }.
  Context `{ ERC721_RECEIVED_immutable:
               forall this st env msg, ERC721_RECEIVED this st env msg = Valid onERC721Received_succ_ret }.

  Hint Rewrite
       from_immutable
       to_immutable
       token_immutable
       ERC721_RECEIVED_immutable
    : dsl_proof.

  Definition safeTransferFrom_wo_data_dsl : Stmt :=
    (@require(_to != zero);
     @address owner = tokenOwner[_token];
     @require((owner != zero) && (owner == _from));
     @address sender = msg.sender;
     @require((sender == owner) || (sender == tokenApprovals[_token]) || operatorApprovals[owner][sender]);
     @tokenApprovals[_token] = zero;
     @tokenOwner[_token] = _to;
     @if (_from != _to) {
        (@require(ownedTokensCount[_to] <= max_uint256 - one);
         @ownedTokensCount[_from] -= one;
         @ownedTokensCount[_to] += one)
     } else {
        (@nop)
     } ;
     (@emit Transfer(_from, _to, _token));
     @if (isContract(_to)) {
        (@require(_to.onERC721Received(_from, _to, _token) == ERC721_RECEIVED))
     } else {
        (@nop)
     }
    )%dsl.

  Lemma safeTransferFrom_wo_data_dsl_sat_spec:
      dsl_sat_spec (mc_safeTransferFrom __from __to __token None)
                   safeTransferFrom_wo_data_dsl
                   (funcspec_safeTransferFrom __from __to __token None).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.
    generalize max_uint256_lt_1. intros max.
    
    unfold funcspec_safeTransferFrom in *.
    simpl in *.

    destruct Hreq as [HtokenOwner [HtokenOwnerFrom [Hsender [Hto [Hcontract HownedTokenCount]]]]].

    unfold dsl_neq, dsl_and, dsl_eq, dsl_or, dsl_tokenOwner_access, dsl_operatorApprovals_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.

    unfold dsl_tokenApprovals_access,dsl_add, dsl_le, dsl_ownedTokensCount_access, dsl_sub, dsl_remote_onERC721Received_call in Hexec.
    
    apply Nat.eqb_neq in Hto.
    rewrite Hto in Hexec. simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    apply Nat.eqb_neq in HtokenOwner.
    apply Nat.eqb_eq in HtokenOwnerFrom.
    rewrite HtokenOwnerFrom, HtokenOwner in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.

    assert((m_sender msg =? V2A.get (st_tokenOwner st) __token)
                      || (m_sender msg =? V2A.get (st_tokenApprovals st) __token)
                      || AA2B.get (st_operatorApprovals st)
                                  (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue).
    unfold orb.
    destruct Hsender. apply Nat.eqb_eq in H. rewrite H. auto.
    destruct H. destruct H. apply Nat.eqb_neq in H. apply Nat.eqb_eq in H0.
    rewrite H. rewrite H0. auto.
    destruct H. destruct H0. apply Nat.eqb_neq in H. apply Nat.eqb_neq in H0.
    rewrite H. rewrite H0. auto.

    rewrite H in Hexec. simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.

    destruct (Nat.eq_dec __from __to).
    - (* __from = __to *)
      subst __from.
      rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      destruct (env_contract env __to).
      + (* Some r *)
        destruct Hcontract. inversion H0.
        destruct H0. destruct H0.
        rewrite H1 in Hexec.
        rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.

        rewrite <- Hexec.
        simpl.
        split.
        {
          unfold INV in *.
          intros owner Howner.
          simpl.
          assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                         (fun e : nat * address => snd e =? owner)) =
                  length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
          apply V2A.filter_length_f_equal.
          intros k. simpl.
          apply Nat.eqb_eq in HtokenOwnerFrom.
          destruct (Nat.eq_dec __token k).
          - subst __token. rewrite V2A.get_upd_eq. rewrite HtokenOwnerFrom. auto. auto.
          - rewrite V2A.get_upd_neq. auto. auto.
          - rewrite H2. apply Hinv. auto.
            
        }
        repeat (split; auto).
        apply upd_inc_dec_lt_1.
         unfold INV in *.
              apply Nat.eqb_neq in HtokenOwner.
              apply Nat.eqb_eq in HtokenOwnerFrom.
              rewrite HtokenOwnerFrom in HtokenOwner.
              rewrite <- Hinv.
              simpl.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __to)) > 0).
              apply V2A.filter_length_exist_nonzero. simpl.
              exists __token. apply Nat.eqb_eq. auto.
              omega. auto.
              generalize (ownedTokensCount_in_range __to st). omega.
      + (* None *)
        rewrite <- Hexec.
        simpl.
         split.
        {
          unfold INV in *.
          intros owner Howner.
          simpl.
          assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                         (fun e : nat * address => snd e =? owner)) =
                  length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
          apply V2A.filter_length_f_equal.
          intros k. simpl.
          apply Nat.eqb_eq in HtokenOwnerFrom.
          destruct (Nat.eq_dec __token k).
          - subst __token. rewrite V2A.get_upd_eq. rewrite HtokenOwnerFrom. auto. auto.
          - rewrite V2A.get_upd_neq. auto. auto.
          - rewrite H0. apply Hinv. auto.
        }
        repeat (split; auto).
        apply upd_inc_dec_lt_1.
         unfold INV in *.
              apply Nat.eqb_neq in HtokenOwner.
              apply Nat.eqb_eq in HtokenOwnerFrom.
              rewrite HtokenOwnerFrom in HtokenOwner.
              rewrite <- Hinv.
              simpl.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __to)) > 0).
              apply V2A.filter_length_exist_nonzero. simpl.
              exists __token. apply Nat.eqb_eq. auto.
              omega. auto.
              generalize (ownedTokensCount_in_range __to st). omega.
    - (* __from <> __to *)
      apply Nat.eqb_neq in n.
      rewrite n in Hexec.
      simpl in Hexec.
      rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
      apply Nat.eqb_neq in n. generalize n; intros n1.
      apply HownedTokenCount in n.
      apply Nat.leb_le in n. rewrite n in Hexec.
      simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      destruct (env_contract env __to).
      + (* Some r *)
        destruct Hcontract. inversion H0.
        destruct H0. destruct H0.
        rewrite H1 in Hexec.
        rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
        
        rewrite <- Hexec.
        simpl.
        split.
        {
          unfold INV in *.
          intros owner Howner.
          simpl.
          rewrite (minus_safe _ _).
          rewrite (plus_safe_lt _ _).
          simpl. A2V.msimpl.
          destruct (Nat.eq_dec __to owner).
          - (* __to = owner *)
            subst __to. A2V.msimpl.
            assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token owner)
                    (fun e : nat * address => snd e =? owner)) =
                    length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) + 1).
            apply V2A.filter_length_upd_false_true with __token.
            simpl. apply Nat.eqb_neq. apply Nat.eqb_eq in HtokenOwnerFrom.
            rewrite HtokenOwnerFrom. auto.
            simpl. rewrite V2A.get_upd_eq. apply Nat.eqb_eq. auto. auto.
            intros k' Hktoken. simpl. rewrite V2A.get_upd_neq. auto. auto.
            
            rewrite H2. apply Nat.add_cancel_r. apply Hinv. auto.
          - (* __to <> owner *)
            destruct (Nat.eq_dec __from owner).
            + (* __from = owner *)
              subst __from.
              simpl. A2V.msimpl.
              assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                    (fun e : nat * address => snd e =? owner)) =
                      length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) -1).
              apply Nat.eqb_eq in HtokenOwnerFrom. 
              apply V2A.filter_length_upd_true_false with __token.
              simpl.  rewrite HtokenOwnerFrom. apply Nat.eqb_eq. auto.
              simpl. rewrite V2A.get_upd_eq.  apply Nat.eqb_neq. auto.
              auto. intros k' Hktoken.
              simpl. rewrite V2A.get_upd_neq.  auto. auto.

              rewrite H2.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) =
                      A2V.get (st_ownedTokensCount st) owner).
              apply Hinv. auto.
              omega.
            + (* __from <> owner *)
              A2V.msimpl.
              assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                    (fun e : nat * address => snd e =? owner)) =
                      length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
              
              apply V2A.filter_length_f_equal.
              intros k. simpl.
              apply Nat.eqb_eq in HtokenOwnerFrom.
              destruct (Nat.eq_dec __token k).
              subst __token. rewrite V2A.get_upd_eq. rewrite HtokenOwnerFrom.
              apply Nat.eqb_neq in n0.
              apply Nat.eqb_neq in n2.
              rewrite n0, n2. auto.
              auto.
              rewrite V2A.get_upd_neq. auto. auto.

              rewrite H2. apply Hinv. auto.

        - rewrite A2V.get_upd_neq. apply Nat.leb_le. auto. auto.

        - rewrite <- Hinv.
          assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) > 0).
          apply V2A.filter_length_exist_nonzero.
          exists __token. simpl. auto.

          omega.
          apply Nat.eqb_neq in HtokenOwner.
          apply Nat.eqb_eq in HtokenOwnerFrom.
          rewrite HtokenOwnerFrom in HtokenOwner.
          auto.
        }
        repeat (split; auto).
      + (* None *)
        rewrite (minus_safe _ _) in Hexec.
        rewrite (plus_safe_lt _ _) in Hexec.
        A2V.msimpl_in Hexec.
        rewrite <- Hexec. simpl.
        split.
        {
          unfold INV in *.
          intros owner Howner.
          simpl.
          destruct (Nat.eq_dec __to owner).
          - (* __to = owner *)
            subst __to.
            A2V.msimpl.
            assert ( length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token owner)
                    (fun e : nat * address => snd e =? owner)) =
                     length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) +1).
            apply V2A.filter_length_upd_false_true with __token. simpl.
            apply Nat.eqb_eq in HtokenOwnerFrom. rewrite HtokenOwnerFrom. apply Nat.eqb_neq. auto.
            simpl. rewrite V2A.get_upd_eq. apply Nat.eqb_eq. auto. auto.
            intros k' Hktoken. simpl. rewrite V2A.get_upd_neq. auto. auto.

            rewrite H0. apply Nat.add_cancel_r.
            apply Hinv. auto.
          - (* __to <> owner *)
            A2V.msimpl.
            destruct (Nat.eq_dec __from owner).
            + (* __from =  owner *)
              subst __from.
              A2V.msimpl.
              assert ( length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                              (fun e0 : nat * address => snd e0 =? owner)) =
                       length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) - 1).
              apply V2A.filter_length_upd_true_false with __token.
              simpl. auto. simpl. rewrite V2A.get_upd_eq. apply Nat.eqb_neq. auto. auto.
              intros k  Hktoken. simpl. rewrite V2A.get_upd_neq. auto. auto.

              rewrite H0.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) =
                      A2V.get (st_ownedTokensCount st) owner).
              apply Hinv. auto.
              omega.
            +(* __from <> owner *)
               A2V.msimpl.
              assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                    (fun e : nat * address => snd e =? owner)) =
                      length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
              apply V2A.filter_length_f_equal. intros k. simpl.
              destruct (Nat.eq_dec __token k).
              subst __token.  rewrite V2A.get_upd_eq.
              apply Nat.eqb_eq in HtokenOwnerFrom. rewrite  HtokenOwnerFrom.
              apply Nat.eqb_neq in n0. apply Nat.eqb_neq in  n2.
              rewrite n0, n2. auto.
              auto. 
              rewrite V2A.get_upd_neq. auto.  auto.

              rewrite H0. apply Hinv. auto.
        }
        repeat (split; auto).
        unfold A2V.upd_inc, A2V.upd_dec.
        rewrite (minus_safe _ _).
        rewrite (plus_safe_lt _ _).
        simpl. rewrite A2V.get_upd_neq. auto.
        auto. rewrite A2V.get_upd_neq. auto. auto.

        unfold INV in *. rewrite <- Hinv.
        assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) > 0).
         apply V2A.filter_length_exist_nonzero.
         exists __token. simpl. auto.
         omega.
         apply Nat.eqb_neq in HtokenOwner.
         apply Nat.eqb_eq in HtokenOwnerFrom.
         rewrite HtokenOwnerFrom in HtokenOwner.
         auto.

         rewrite A2V.get_upd_neq. apply Nat.leb_le. auto.
         auto. 

         unfold INV in *. rewrite <- Hinv.
        assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) > 0).
         apply V2A.filter_length_exist_nonzero.
         exists __token. simpl. auto.
         omega.
         apply Nat.eqb_neq in HtokenOwner.
         apply Nat.eqb_eq in HtokenOwnerFrom.
         rewrite HtokenOwnerFrom in HtokenOwner.
         auto.
 Qed.


  Lemma safeTransferFrom_wo_data_dsl_revert:
    forall st env msg this,
      m_func msg = mc_safeTransferFrom __from __to __token None ->
      INV st env msg ->
      ~ spec_require (funcspec_safeTransferFrom __from __to __token None this env msg) st ->
      forall result,
        dsl_exec safeTransferFrom_wo_data_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    generalize max_uint256_lt_1. intros max.
    unfold funcspec_safeTransferFrom in *.
    simpl in *.

    unfold dsl_neq,dsl_and, dsl_eq,dsl_add, dsl_tokenOwner_access,dsl_ownedTokensCount_access, dsl_remote_onERC721Received_call, dsl_tokenApprovals_access, dsl_or, dsl_operatorApprovals_access, dsl_le,dsl_sub in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    destruct (Nat.eq_dec __to 0).
    - (*__to = 0*)
      subst __to. simpl in Hexec.
      rewrite <- Hexec. split;auto.
    - (* __to <> 0 *)
      apply Nat.eqb_neq in n. rewrite n in Hexec.
      simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      destruct (Nat.eq_dec (V2A.get (st_tokenOwner st) __token)  0).
      + (* V2A.get (st_tokenOwner st) __token = 0 *)
        rewrite e in Hexec. simpl in Hexec.
        rewrite <- Hexec. split;auto.
      + (* V2A.get (st_tokenOwner st) __token <> 0 *)
        apply Nat.eqb_neq in n0. rewrite n0 in Hexec.
        destruct (Nat.eq_dec (V2A.get (st_tokenOwner st) __token)  __from).
        {(* V2A.get (st_tokenOwner st) __token = from *)
          rewrite e in Hexec. simpl in Hexec. simpl in Hexec.
          rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
          autorewrite with dsl_proof in Hexec.
          destruct (bool_dec ((m_sender msg =? V2A.get (st_tokenOwner st) __token)
                      || (m_sender msg =? V2A.get (st_tokenApprovals st) __token)
                      || AA2B.get (st_operatorApprovals st)
                                  (V2A.get (st_tokenOwner st) __token, m_sender msg)) otrue).
          {
            rewrite e0 in Hexec.
            simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            destruct (Nat.eq_dec __from __to).
            - (* __from = __to *)
              apply Nat.eqb_eq in e1. rewrite e1 in Hexec. simpl in Hexec.
              autorewrite with dsl_proof in Hexec.
              simpl in Hexec.
              autorewrite with dsl_proof in Hexec.
              destruct (env_contract env __to).
              {(* Some r *)
                destruct (onERC721Received_oracle __from __to __token None).
                - destruct (Nat.eq_dec  b  onERC721Received_succ_ret).
                  + subst b. rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
                    
                    assert ((V2A.get (st_tokenOwner st) __token <> 0 /\
                             V2A.get (st_tokenOwner st) __token = __from /\
                             (m_sender msg = V2A.get (st_tokenOwner st) __token \/
                              m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                              m_sender msg = V2A.get (st_tokenApprovals st) __token \/
                              m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                              m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
                              AA2B.get (st_operatorApprovals st)
                                       (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue) /\
                             __to <> 0 /\
                             (Some r = None \/
                              (exists RS : ReceiverState,
                                  Some r = Some RS /\
                                  Some onERC721Received_succ_ret = Some onERC721Received_succ_ret)) /\
                             (__from <> __to -> A2V.get (st_ownedTokensCount st) __to <= MAX_UINT256 - 1))).
                    {
                      apply Nat.eqb_neq in n0.
                      apply Nat.eqb_eq in e.
                      split. auto.
                      split. apply Nat.eqb_eq in e. auto.
                      
                      assert ((m_sender msg = V2A.get (st_tokenOwner st) __token \/
                               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                               m_sender msg = V2A.get (st_tokenApprovals st) __token \/
                               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                               m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
                               AA2B.get (st_operatorApprovals st) (V2A.get (st_tokenOwner st) __token, m_sender msg) =
                               otrue)).
                      destruct (Nat.eq_dec (m_sender msg)  (V2A.get (st_tokenOwner st) __token)).
                      - left. auto.
                      - right. destruct (Nat.eq_dec (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                        + left. split;auto.
                        + right.  repeat (split;auto).
                          unfold orb in e0. apply Nat.eqb_neq in n1. apply Nat.eqb_neq in n2.
                          rewrite n1, n2 in e0. auto.
                      - split. auto.
                        apply Nat.eqb_neq in n.  split. auto.
                        split. right. exists r. auto.
                        intros Htoto. apply Nat.eqb_eq in e1. contradiction.
                    }
                    contradiction.
                  + apply Nat.eqb_neq in n1. rewrite n1 in Hexec.
                    rewrite <- Hexec. split; auto.
                - rewrite <- Hexec. split; auto.
              }
              {
                contradict Hreq_neg.
                split. apply Nat.eqb_neq in n0. auto.
                split. auto.
                split.
                destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenOwner st) __token)).
                - left. auto.
                - right. destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                  + left. auto.
                  + right. repeat (split; auto).
                    apply Nat.eqb_neq in n1. apply Nat.eqb_neq in n2. rewrite n1,n2 in e0. simpl in e0.
                    auto.
                - split. apply Nat.eqb_neq in n. auto.
                  split. left. auto.
                  intros.  apply Nat.eqb_eq in e1. contradiction.
              }
             
            - (* __from <> __to *)
              apply Nat.eqb_neq in n1.
              rewrite n1 in Hexec.
              simpl in Hexec.
              rewrite (minus_safe _ _) in Hexec; [> idtac | auto].

              destruct (le_dec (A2V.get (st_ownedTokensCount st) __to) (MAX_UINT256 - 1)).
              + (* A2V.get (st_ownedTokensCount st) __to <=? MAX_UINT256 - 1 *)
                apply Nat.leb_le in l. rewrite l in Hexec.
                simpl in Hexec.
                autorewrite with dsl_proof in Hexec.
                simpl in Hexec.
                autorewrite with dsl_proof in Hexec.
                unfold A2V.upd_inc, A2V.upd_dec in Hexec.
                rewrite (minus_safe _ _) in Hexec.
                rewrite (plus_safe_lt _ _) in Hexec.
                simpl in Hexec.
                autorewrite with dsl_proof in Hexec.
                simpl in Hexec.
                autorewrite with dsl_proof in Hexec.
                destruct (env_contract env __to).
                {(* Some r *)
                  destruct (onERC721Received_oracle __from __to __token None).
                  - destruct (Nat.eq_dec  b  onERC721Received_succ_ret).
                    + subst b. rewrite (Nat.eqb_refl _) in Hexec. simpl in Hexec.
                    
                    assert ((V2A.get (st_tokenOwner st) __token <> 0 /\
                             V2A.get (st_tokenOwner st) __token = __from /\
                             (m_sender msg = V2A.get (st_tokenOwner st) __token \/
                              m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                              m_sender msg = V2A.get (st_tokenApprovals st) __token \/
                              m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                              m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
                              AA2B.get (st_operatorApprovals st)
                                       (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue) /\
                             __to <> 0 /\
                             (Some r = None \/
                              (exists RS : ReceiverState,
                                  Some r = Some RS /\
                                  Some onERC721Received_succ_ret = Some onERC721Received_succ_ret)) /\
                             (__from <> __to -> A2V.get (st_ownedTokensCount st) __to <= MAX_UINT256 - 1))).
                    {
                      apply Nat.eqb_neq in n0.
                      apply Nat.eqb_eq in e.
                      split. auto.
                      split. apply Nat.eqb_eq in e. auto.
                      assert ((m_sender msg = V2A.get (st_tokenOwner st) __token \/
                               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                               m_sender msg = V2A.get (st_tokenApprovals st) __token \/
                               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
                               m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
                               AA2B.get (st_operatorApprovals st) (V2A.get (st_tokenOwner st) __token, m_sender msg) =
                               otrue)).
                      destruct (Nat.eq_dec (m_sender msg)  (V2A.get (st_tokenOwner st) __token)).
                      - left. auto.
                      - right. destruct (Nat.eq_dec (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                        + left. split;auto.
                        + right.  repeat (split;auto).
                          unfold orb in e0. apply Nat.eqb_neq in n3. apply Nat.eqb_neq in n2.
                          rewrite n3, n2 in e0. auto.
                      - split. auto.
                        split. apply Nat.eqb_neq in n. auto.
                        split. right. exists r. auto.
                        intros Htoto.  apply Nat.leb_le. auto. 
                    }
                    contradiction.
                  + apply Nat.eqb_neq in n2. rewrite n2 in Hexec.
                    rewrite <- Hexec. split; auto.
                - rewrite <- Hexec. split; auto.
                }
               {
                contradict Hreq_neg.
                split. apply Nat.eqb_neq in n0. auto.
                split. auto.
                split.
                destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenOwner st) __token)).
                - left. auto.
                - right. destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                  + left. auto.
                  + right. repeat (split; auto).
                    apply Nat.eqb_neq in n3. apply Nat.eqb_neq in n2. rewrite n3,n2 in e0. simpl in e0.
                    auto.
                - split. apply Nat.eqb_neq in n. auto.
                  split. left. auto.
                  intros.  apply Nat.leb_le in l. auto.
               }
                rewrite A2V.get_upd_neq. apply Nat.leb_le. auto.
                apply Nat.eqb_neq in n1. auto.
                unfold INV in *. rewrite <- Hinv.
                assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) > 0).
                apply V2A.filter_length_exist_nonzero.
                exists __token. simpl. apply Nat.eqb_eq in e. auto. omega.
                rewrite e in n0. apply Nat.eqb_neq in n0. auto.
              + (* A2V.get (st_ownedTokensCount st) __to <=? MAX_UINT256 - 1 *)
                apply Nat.leb_nle in n2. rewrite n2 in Hexec.
                simpl in Hexec.
                rewrite <- Hexec. split;auto.
          }
          {
            apply not_true_is_false in n1.
            rewrite n1 in Hexec. simpl in Hexec.
            rewrite <- Hexec. split;auto.            
          }

        }
        {(* V2A.get (st_tokenOwner st) __token <> from *)
          apply Nat.eqb_neq in n1. rewrite n1 in Hexec.
          simpl in Hexec.
          rewrite <- Hexec. split;auto.
        }
Qed.        

End dsl_safeTransferFrom_wo_data.

Section dsl_transferFrom.
  Context `{ _from: Expr address }.
  Context `{ __from: address }.
  Context `{ from_immutable:
               forall this st env msg, _from this st env msg = Valid __from }.

  Context `{ _to: Expr address }.
  Context `{ __to: address }.
  Context `{ to_immutable:
               forall this st env msg, _to this st env msg = Valid __to }.

  Context `{ _token: Expr uint256 }.
  Context `{ __token: uint256 }.
  Context `{ token_immutable:
               forall this st env msg, _token this st env msg = Valid __token }.

  Hint Rewrite
       from_immutable
       to_immutable
       token_immutable
    : dsl_proof.

  Definition transferFrom_dsl : Stmt :=
    (@require(_to != zero);
     @address owner = tokenOwner[_token];
     @require((owner != zero) && (owner == _from));
     @address sender = msg.sender;
     @require((sender == owner) || (sender == tokenApprovals[_token]) || operatorApprovals[owner][sender]);
     @tokenApprovals[_token] = zero;
     @tokenOwner[_token] = _to;
     @if (_from != _to) {
        (@require(ownedTokensCount[_to] <= max_uint256 - one);
         @ownedTokensCount[_from] -= one;
         @ownedTokensCount[_to] += one)
     } else {
        (@nop)
     } ;
     (@emit Transfer(_from, _to, _token))
    )%dsl.

  Lemma transferFrom_dsl_sat_spec:
      dsl_sat_spec (mc_transferFrom __from __to __token)
                   transferFrom_dsl
                   (funcspec_transferFrom __from __to __token).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.
    generalize max_uint256_lt_1. intros max.

    unfold funcspec_transferFrom in *.
    simpl in *.

    unfold  dsl_and, dsl_neq, dsl_add, dsl_tokenOwner_access, dsl_ownedTokensCount_access, dsl_tokenApprovals_access, dsl_eq,dsl_le, dsl_sub, dsl_tokenOwner_access, dsl_or, dsl_eq, dsl_operatorApprovals_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.

    destruct Hreq as [HtokenOwner [HtokenOwnerfrom [Hsender [Hto Hfromto]]]].
    apply Nat.eqb_neq in Hto. rewrite Hto in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    apply Nat.eqb_neq in HtokenOwner. rewrite HtokenOwner in Hexec.
    apply Nat.eqb_eq in HtokenOwnerfrom. rewrite HtokenOwnerfrom in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    assert ((m_sender msg =? V2A.get (st_tokenOwner st) __token)
                    || (m_sender msg =? V2A.get (st_tokenApprovals st) __token)
                    || AA2B.get (st_operatorApprovals st)
                                (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue).
    {
      unfold orb.
      destruct Hsender.
      apply Nat.eqb_eq in H. rewrite H. simpl. auto.
      destruct H. destruct H. apply Nat.eqb_eq in H0. apply Nat.eqb_neq in H. rewrite H0.  rewrite H.  auto.
      destruct H. destruct H0. apply Nat.eqb_neq in H0. apply Nat.eqb_neq in H.
      rewrite H, H0. auto.

    }
    rewrite H in Hexec. simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
    
    
    destruct (Nat.eq_dec __from __to).
     - (* __from = __to *)
       subst __from.
       rewrite (Nat.eqb_refl _) in Hexec.
       autorewrite with dsl_proof in Hexec.
       simpl in Hexec.
       autorewrite with dsl_proof in Hexec.
       rewrite <- Hexec.
       simpl.
       split.
       + unfold INV in *.
         intros owner Howner.
         simpl.
         destruct (Nat.eq_dec __to owner).
         {(* __to = owner *)
          subst __to.
          simpl in *.
          V2A.msimpl.
          assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token owner)
                                          (fun e1 : nat * address => snd e1 =? owner)) =
                   length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
          apply V2A.filter_length_f_equal.
          intros k. simpl.
          destruct (Nat.eq_dec __token k).
          - (* __token = k *)
            subst __token.
            rewrite (V2A.get_upd_eq); auto.
            apply Nat.eqb_eq in HtokenOwnerfrom. rewrite HtokenOwnerfrom. auto.
         - (* __token <> k *)
            rewrite (V2A.get_upd_neq); auto.
         - rewrite H0. apply Hinv. auto.
        }
        {(* __to <> owner *)
         assert(length  (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                        (fun e1 : nat * address => snd e1 =? owner)) = 
          length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
          apply V2A.filter_length_f_equal.
          intros k. simpl.
          destruct (Nat.eq_dec __token k).
          - (* __token = k *)
            subst __token. rewrite (V2A.get_upd_eq); auto.
            apply Nat.eqb_eq in HtokenOwnerfrom. rewrite HtokenOwnerfrom. auto.
          - (* __token <> k *)
            rewrite (V2A.get_upd_neq); auto.
         - rewrite H0. apply Hinv. auto.
      }
      + repeat (split; auto).
        apply upd_inc_dec_lt_1.
         unfold INV in *.
              apply Nat.eqb_neq in HtokenOwner.
              apply Nat.eqb_eq in HtokenOwnerfrom.
              rewrite HtokenOwnerfrom in HtokenOwner.
              rewrite <- Hinv.
              simpl.
              assert (length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __to)) > 0).
              apply V2A.filter_length_exist_nonzero. simpl.
              exists __token. apply Nat.eqb_eq. auto.
              omega. auto.
              generalize (ownedTokensCount_in_range __to st). omega.
     - (* __from <> __to *)
       generalize n; intros n1.
       apply Nat.eqb_neq in n. rewrite n in Hexec. simpl in Hexec.
       apply Hfromto in n1. apply Nat.leb_le in n1.
       rewrite n1 in Hexec. simpl in Hexec.
       autorewrite with dsl_proof in Hexec.
       simpl in Hexec.
       autorewrite with dsl_proof in Hexec.
       simpl in Hexec.
       autorewrite with dsl_proof in Hexec.
       rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
       rewrite (plus_safe_lt _ _) in Hexec.
       rewrite <- Hexec. simpl. split.
       + unfold INV in *. 
         intros owner Howner. simpl.
         destruct (Nat.eq_dec __to owner).
        {(* __to = owner *)
          subst __to. apply Nat.eqb_neq in n. A2V.msimpl.
          assert(length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token owner)
                                        (fun e1 : nat * address => snd e1 =? owner)) =
                 length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))+1).
          apply V2A.filter_length_upd_false_true with __token.
          simpl. apply Nat.eqb_eq in HtokenOwnerfrom. rewrite HtokenOwnerfrom. apply Nat.eqb_neq. auto.
          simpl. rewrite (V2A.get_upd_eq). apply Nat.eqb_eq. auto. auto.
          intros k' Hktoken. simpl. rewrite (V2A.get_upd_neq); auto.
          rewrite H0. apply Nat.add_cancel_r. apply Hinv. auto.
        }
        {(* __to <> owner *)
         simpl. A2V.msimpl.
         destruct (Nat.eq_dec __from owner).
         - (* __from = owner *)
           subst __from. A2V.msimpl.
           assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                          (fun e1 : nat * address => snd e1 =? owner)) =
                   length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) -1                                                                                    
                  ).
           apply V2A.filter_length_upd_true_false with __token.
           simpl. auto. simpl.
           rewrite (V2A.get_upd_eq). apply Nat.eqb_neq. auto. auto.
           intros k' Hktoken. simpl. rewrite (V2A.get_upd_neq); auto.
           rewrite H0.
           assert (length (V2A.map_filter (st_tokenOwner st) (fun e1 : nat * address => snd e1 =? owner)) =
                   A2V.get (st_ownedTokensCount st) owner ).           
           apply Hinv. auto. omega.
         - (* __from <> owner *)
           apply Nat.eqb_neq in n2. A2V.msimpl.
            assert ( length  (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                                             (fun e1 : nat * address => snd e1 =? owner)) =
                     length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).
            apply V2A.filter_length_f_equal.
            intros k. destruct (Nat.eq_dec __token k).
            + (* __token  = k*)
              subst __token. simpl.
              rewrite (V2A.get_upd_eq); auto.
              apply Nat.eqb_eq in HtokenOwnerfrom. rewrite HtokenOwnerfrom.
              apply Nat.eqb_neq in n0.
              rewrite n2, n0. auto.
            + (* __token  <> K *)
              rewrite (V2A.get_upd_neq); auto.
            + rewrite H0. apply Nat.eqb_neq in n2.
              A2V.msimpl.
        }
        + repeat (split; auto).
          unfold A2V.upd_inc, A2V.upd_dec .
          rewrite (minus_safe _ _). rewrite (plus_safe_lt _ _). auto.
          apply Nat.eqb_neq in n.  A2V.msimpl.

          unfold INV in *.
          assert ( length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) =
                   A2V.get (st_ownedTokensCount st) __from).
          apply Hinv. apply Nat.eqb_neq in n. apply Nat.eqb_eq in HtokenOwnerfrom. rewrite HtokenOwnerfrom in HtokenOwner. auto.
          apply Nat.eqb_neq in HtokenOwner. auto.
          assert (length (V2A.map_filter (st_tokenOwner st) (fun e1 : nat * address => snd e1 =? __from)) > 0).
          apply V2A.filter_length_exist_nonzero. exists __token. simpl. auto.
          omega.
        + apply Nat.eqb_neq in n.
          A2V.msimpl.
       +   unfold INV in *.
          assert ( length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? __from)) =
                   A2V.get (st_ownedTokensCount st) __from).
          apply Hinv. apply Nat.eqb_neq in n. apply Nat.eqb_eq in HtokenOwnerfrom. rewrite HtokenOwnerfrom in HtokenOwner. auto.
          apply Nat.eqb_neq in HtokenOwner. auto.
          assert (length (V2A.map_filter (st_tokenOwner st) (fun e1 : nat * address => snd e1 =? __from)) > 0).
          apply V2A.filter_length_exist_nonzero. exists __token. simpl. auto.
          omega.
Qed.    


  Lemma transferFrom_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transferFrom __from __to __token ->
      INV st env msg ->
      ~ spec_require (funcspec_transferFrom __from __to __token this env msg) st ->
      forall result,
        dsl_exec transferFrom_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    generalize max_uint256_lt_1. intros max.
    unfold funcspec_transferFrom in *.
    simpl in *.

    unfold dsl_neq, dsl_and, dsl_neq, dsl_le,dsl_add, dsl_ownedTokensCount_access, dsl_sub ,dsl_tokenOwner_access,dsl_tokenApprovals_access , dsl_eq, dsl_or, dsl_operatorApprovals_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    destruct (Nat.eq_dec __to 0).
    - (* __to = 0 *)
      apply Nat.eqb_eq in e.
      rewrite e in Hexec.
      simpl in Hexec.
      rewrite <- Hexec.
      simpl.
      split;auto.
    -(* __to <> 0*)
      apply Nat.eqb_neq in n.
      rewrite n in Hexec.
      simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      destruct (Nat.eq_dec (V2A.get (st_tokenOwner st) __token) 0).
      + (* V2A.get (st_tokenOwner st) __token = 0 *)
        apply Nat.eqb_eq in e.
        rewrite e in Hexec.
        simpl in Hexec.
        rewrite <- Hexec.
        simpl; auto.
      + (* V2A.get (st_tokenOwner st) __token <> 0 *)
        apply Nat.eqb_neq in n0.
        rewrite n0 in Hexec.
        simpl in Hexec.
        destruct (Nat.eq_dec (V2A.get (st_tokenOwner st) __token) __from).
        {(* V2A.get (st_tokenOwner st) __token = __from *)
          apply Nat.eqb_eq in e. rewrite e in Hexec.
          simpl in Hexec.
          autorewrite with dsl_proof in Hexec.
          destruct (bool_dec ((m_sender msg =? V2A.get (st_tokenOwner st) __token)
                    || (m_sender msg =? V2A.get (st_tokenApprovals st) __token)
                    || AA2B.get (st_operatorApprovals st)
                                (V2A.get (st_tokenOwner st) __token, m_sender msg)) otrue).
          {
            rewrite e0 in Hexec. simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            simpl in Hexec.
            autorewrite with dsl_proof in Hexec.
            destruct (Nat.eq_dec __from __to).
            - (* __from = __to *)
              subst __from.

              assert ((V2A.get (st_tokenOwner st) __token <> 0 /\
              V2A.get (st_tokenOwner st) __token = __to /\
              (m_sender msg = V2A.get (st_tokenOwner st) __token \/
               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
               m_sender msg = V2A.get (st_tokenApprovals st) __token \/
               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
               m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
               AA2B.get (st_operatorApprovals st)
                 (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue) /\
              __to <> 0 /\
              (__to <> __to -> A2V.get (st_ownedTokensCount st) __to <= MAX_UINT256 - 1))).
              {
                split. apply Nat.eqb_neq in n0. auto.
                split. apply Nat.eqb_eq in e. auto.
                split. unfold orb in e0.
                destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenOwner st) __token)).
                - left. auto.
                - right.
                  destruct (Nat.eq_dec (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                  + left. split; auto.
                  + right. repeat(split; auto).
                    apply Nat.eqb_neq in n1. apply Nat.eqb_neq in n2.
                    rewrite n1 in e0. rewrite n2 in e0. auto.
                - split. apply Nat.eqb_neq in n. auto.
                  intros. contradiction.
              }
              contradiction.
            - (* from <> to *)
              apply Nat.eqb_neq in n1.
              rewrite n1 in Hexec.
              simpl in Hexec.
              rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
              destruct (le_dec (A2V.get (st_ownedTokensCount st) __to) (MAX_UINT256 - 1)).
              + (* A2V.get (st_ownedTokensCount st) __to <=? MAX_UINT256 - 1 *)

                assert((V2A.get (st_tokenOwner st) __token <> 0 /\
              V2A.get (st_tokenOwner st) __token = __from /\
              (m_sender msg = V2A.get (st_tokenOwner st) __token \/
               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
               m_sender msg = V2A.get (st_tokenApprovals st) __token \/
               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
               m_sender msg <> V2A.get (st_tokenApprovals st) __token /\
               AA2B.get (st_operatorApprovals st)
                 (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue) /\
              __to <> 0 /\
              (__from <> __to -> A2V.get (st_ownedTokensCount st) __to <= MAX_UINT256 - 1))).
                {
                  apply Nat.eqb_neq in n0.
                  apply Nat.eqb_eq in e.
                  split. auto.
                  split. auto.
                  split. unfold orb in e0.
                  destruct (Nat.eq_dec  (m_sender msg) (V2A.get (st_tokenOwner st) __token)).
                  - left. auto.
                  - right.
                    destruct (Nat.eq_dec (m_sender msg) (V2A.get (st_tokenApprovals st) __token)).
                    + left. split; auto.
                    + right. repeat(split; auto).
                      apply Nat.eqb_neq in n2. apply Nat.eqb_neq in n3.
                      rewrite n2 in e0. rewrite n3 in e0. auto.
                - split. apply Nat.eqb_neq in n. auto.
                  intros. auto.
                }
                contradiction.
               + apply Nat.leb_nle in n2.
                rewrite n2 in Hexec. simpl in Hexec.
                rewrite <- Hexec.
                simpl; auto.
          }
          {
            apply not_true_is_false in n1.
            rewrite n1 in Hexec.
            simpl in Hexec.
            rewrite <- Hexec.
                simpl; auto.
          }
        }
        {(* V2A.get (st_tokenOwner st) __token <> __from *)
          apply Nat.eqb_neq in n1. rewrite n1 in Hexec.
          simpl in Hexec.
                rewrite <- Hexec.
                simpl; auto.
        }
  Qed.
  
End dsl_transferFrom.

Section dsl_approve.
  Context `{ _approved: Expr address }.
  Context `{ __approved: address }.
  Context `{ approved_immutable:
               forall this st env msg, _approved this st env msg = Valid __approved }.

  Context `{ _token: Expr uint256 }.
  Context `{ __token: uint256 }.
  Context `{ token_immutable:
               forall this st env msg, _token this st env msg = Valid __token }.

  Hint Rewrite
       approved_immutable
       token_immutable
    : dsl_proof.

  Definition approve_dsl : Stmt :=
    (@address owner = tokenOwner[_token];
     @require(_approved != owner);
     @address sender = msg.sender;
     @require((sender == owner) || operatorApprovals[owner][sender]);
     @tokenApprovals[_token] = _approved;
     @emit Approval(owner, _approved, _token)
    )%dsl.

  Lemma approve_dsl_sat_spec:
      dsl_sat_spec (mc_approve __approved __token)
                   approve_dsl
                   (funcspec_approve __approved __token).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.
    generalize max_uint256_lt_1. intros max.
    unfold funcspec_approve in *.
    simpl in *.

    destruct Hreq as [Hreq_token Hreq_approved].
    apply Nat.eqb_neq in Hreq_approved.

    
    unfold dsl_neq, dsl_or, dsl_eq, dsl_operatorApprovals_access, dsl_tokenOwner_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite Hreq_approved in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.

    assert ( ((m_sender msg =? V2A.get (st_tokenOwner st) __token)
                || AA2B.get (st_operatorApprovals st)
                            (V2A.get (st_tokenOwner st) __token, m_sender msg)) = otrue).
    unfold otrue.
    unfold orb.
    inversion Hreq_token.
    apply Nat.eqb_eq in H. rewrite H. auto.
    destruct H. apply Nat.eqb_neq in H. rewrite H. auto.

    rewrite H in Hexec. simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite <- Hexec.
    simpl.
    split.
    - unfold INV in *.
      intros owner Howner.
      simpl. apply Hinv. auto.
    - split;auto.
  Qed.

  Lemma approve_dsl_revert:
    forall st env msg this,
      m_func msg = mc_approve __approved __token ->
      INV st env msg ->
      ~ spec_require (funcspec_approve __approved __token this env msg) st ->
      forall result,
        dsl_exec approve_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    unfold funcspec_approve in Hreq_neg. simpl in *.

    unfold dsl_neq, dsl_tokenOwner_access,  dsl_or, dsl_eq, dsl_operatorApprovals_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    destruct (Nat.eq_dec __approved (V2A.get (st_tokenOwner st) __token)).
    - (* __approved = V2A.get (st_tokenOwner st) __token *)
      apply Nat.eqb_eq in e.
      rewrite e in Hexec. simpl in Hexec.
      rewrite <- Hexec.
      split; auto.
    - (* __approved <> V2A.get (st_tokenOwner st) __token *)
      apply Nat.eqb_neq in n.
      rewrite n in Hexec. simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      destruct (bool_dec ((m_sender msg =? V2A.get (st_tokenOwner st) __token)
                || AA2B.get (st_operatorApprovals st)
                            (V2A.get (st_tokenOwner st) __token, m_sender msg)) otrue).
      + assert ((m_sender msg = V2A.get (st_tokenOwner st) __token \/
               m_sender msg <> V2A.get (st_tokenOwner st) __token /\
               AA2B.get (st_operatorApprovals st)
                 (V2A.get (st_tokenOwner st) __token, m_sender msg) = otrue) /\
                __approved <> V2A.get (st_tokenOwner st) __token).
        split.
        unfold orb in e.
        destruct (Nat.eq_dec (m_sender msg) (V2A.get (st_tokenOwner st) __token)).
        left;auto.
        right. split.
        auto.
        apply Nat.eqb_neq in n0. rewrite n0 in e.  auto.
        apply Nat.eqb_neq in n. auto.
        contradiction.
      + apply not_true_is_false in n0.
        rewrite n0 in Hexec. simpl in Hexec.
        rewrite <- Hexec. split;auto.
Qed.    

End dsl_approve.

Section dsl_setApprovalForAll.
  Context `{ _operator: Expr address }.
  Context `{ __operator: address }.
  Context `{ operator_immutable:
               forall this st env msg, _operator this st env msg = Valid __operator }.

  Context `{ _approved: Expr bool }.
  Context `{ __approved: bool }.
  Context `{ approved_immutable:
               forall this st env msg, _approved this st env msg = Valid __approved }.

  Hint Rewrite
       operator_immutable
       approved_immutable
    : dsl_proof.

  Definition setApprovalForAll_dsl : Stmt :=
    (@address sender = msg.sender;
     @require(_operator != sender);
     @operatorApprovals[sender][_operator] = _approved;
     @emit ApprovalForAll(sender, _operator, _approved)
    )%dsl.

  Lemma setApprovalForAll_dsl_sat_spec:
      dsl_sat_spec (mc_setApprovalForAll __operator __approved)
                   setApprovalForAll_dsl
                   (funcspec_setApprovalForAll __operator __approved).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.
    unfold funcspec_setApprovalForAll in *.
    simpl in *.

    apply Nat.neq_sym in Hreq.
    apply Nat.eqb_neq in Hreq.

    unfold dsl_neq in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite Hreq in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.

    rewrite <- Hexec.
    simpl.
    split.
    - unfold INV in *.
      intros owner Howner.
      simpl. apply Hinv;auto.
    - split;auto.
 Qed.

  Lemma setApprovalForAll_dsl_revert:
    forall st env msg this,
      m_func msg = mc_setApprovalForAll __operator __approved ->
      INV st env msg ->
      ~ spec_require (funcspec_setApprovalForAll __operator __approved this env msg) st ->
      forall result,
        dsl_exec setApprovalForAll_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    unfold funcspec_setApprovalForAll in *.
    simpl in *.
    apply Nat.eq_dne in Hreq_neg.
    apply Nat.eq_sym in Hreq_neg.
    apply Nat.eqb_eq in Hreq_neg.

    unfold  dsl_neq in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite Hreq_neg in Hexec.
    simpl in Hexec.

    rewrite <- Hexec.
    split; auto.
Qed.    
End dsl_setApprovalForAll.

Section dsl_getApproved.
  Context `{ _token: Expr uint256 }.
  Context `{ __token: uint256 }.
  Context `{ token_immutable:
               forall this st env msg, _token this st env msg = Valid __token }.

  Hint Rewrite
       token_immutable
    : dsl_proof.

  Definition getApproved_dsl : Stmt :=
    ( @require(tokenOwner[_token] != zero);
      @return tokenApprovals[_token]
    )%dsl.

  Lemma getApproved_dsl_sat_spec:
      dsl_sat_spec (mc_getApproved __token)
                   getApproved_dsl
                   (funcspec_getApproved __token).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold funcspec_getApproved in *.
    simpl in *.

    apply Nat.eqb_neq in Hreq.

    unfold dsl_tokenApprovals_access, dsl_neq,dsl_tokenOwner_access  in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    rewrite Hreq in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite <- Hexec.
    simpl.
    split;auto.
Qed.    

  Lemma getApproved_dsl_revert:
    forall st env msg this,
      m_func msg = mc_getApproved __token ->
      INV st env msg ->
      ~ spec_require (funcspec_getApproved __token this env msg) st ->
      forall result,
        dsl_exec getApproved_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    unfold funcspec_getApproved in *.
    simpl in *.
    apply Nat.eq_dne in Hreq_neg.
    apply Nat.eqb_eq in Hreq_neg.

    unfold dsl_tokenApprovals_access, dsl_neq, dsl_tokenOwner_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    rewrite Hreq_neg in Hexec.
    simpl in Hexec.
    rewrite <- Hexec.
    simpl.
    split;auto.
Qed.    

End dsl_getApproved.

Section dsl_isApprovedForAll.
  Context `{ _owner: Expr address }.
  Context `{ __owner: address }.
  Context `{ owner_immutable:
               forall this st env msg, _owner this st env msg = Valid __owner }.

  Context `{ _operator: Expr address }.
  Context `{ __operator: address }.
  Context `{ operator_immutable:
               forall this st env msg, _operator this st env msg = Valid __operator }.

  Hint Rewrite
       owner_immutable
       operator_immutable
    : dsl_proof.

  Definition isApprovedForAll_dsl : Stmt :=
    (@return operatorApprovals[_owner][_operator]
    )%dsl.

  Lemma isApprovedForAll_dsl_sat_spec:
      dsl_sat_spec (mc_isApprovedForAll __owner __operator)
                   isApprovedForAll_dsl
                   (funcspec_isApprovedForAll __owner __operator).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold funcspec_isApprovedForAll in *.
    simpl in *.

    unfold dsl_operatorApprovals_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite <- Hexec.
    simpl.
    split; auto.
Qed.

  Lemma isApprovedForAll_dsl_revert:
    forall st env msg this,
      m_func msg = mc_isApprovedForAll __owner __operator ->
      INV st env msg ->
      ~ spec_require (funcspec_isApprovedForAll __owner __operator this env msg) st ->
      forall result,
        dsl_exec isApprovedForAll_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.

    unfold funcspec_isApprovedForAll in *.
    simpl in *.

    contradiction.
Qed.

End dsl_isApprovedForAll.

Section dsl_supportsInterface.
  Context `{ _id: Expr bytes4 }.
  Context `{ __id: bytes4 }.
  Context `{ id_immutable:
               forall this st env msg, _id this st env msg = Valid __id }.

  Context `{ erc721_interface_id: Expr bytes4 }.
  Context `{ erc721_interface_id_immutable:
               forall this st env msg, erc721_interface_id this st env msg = Valid ERC721_INTERFACE_ID }.

  Context `{ erc165_interface_id: Expr bytes4 }.
  Context `{ erc165_interface_id_immutable:
               forall this st env msg, erc165_interface_id this st env msg = Valid ERC165_INTERFACE_ID }.

  Hint Rewrite
       id_immutable
       erc721_interface_id_immutable
       erc165_interface_id_immutable
    : dsl_proof.

  Definition supportsInterface_dsl : Stmt :=
    (@if (_id == erc165_interface_id) {
        (@return true)
     } else {
       (@if (_id == erc721_interface_id) {
          (@return true)
       } else {
          (@return false)
       })
     }
    )%dsl.

  Lemma supportsInterface_dsl_sat_spec:
      dsl_sat_spec (mc_supportsInterface __id)
                   supportsInterface_dsl
                   (funcspec_supportsInterface __id).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.

    unfold funcspec_supportsInterface in *.
    simpl in *.

    unfold dsl_eq in Hexec.
    autorewrite with dsl_proof in Hexec.
    destruct(Nat.eq_dec __id ERC165_INTERFACE_ID).
    - apply Nat.eqb_eq in e.
      rewrite e in Hexec.
      rewrite <- Hexec.
      simpl.
      repeat(split; auto).
      rewrite e. auto.
    - apply Nat.eqb_neq in n.
      rewrite n in Hexec.
      destruct(Nat.eq_dec __id ERC721_INTERFACE_ID).
      + apply Nat.eqb_eq in e.
        rewrite e in Hexec.
        rewrite <- Hexec.
        simpl.
        repeat(split; auto).
        rewrite e. rewrite n. auto.
      + apply Nat.eqb_neq in n0.
        rewrite n0 in Hexec.
        rewrite <- Hexec.
        simpl.
        repeat(split; auto).
        rewrite n.
        rewrite n0.
        auto.
  Qed.
  
  Lemma supportsInterface_dsl_revert:
    forall st env msg this,
      m_func msg = mc_supportsInterface __id ->
      INV st env msg ->
      ~ spec_require (funcspec_supportsInterface __id this env msg) st ->
      forall result,
        dsl_exec supportsInterface_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    unfold funcspec_supportsInterface in *.
    simpl in *.

    contradiction.
Qed.    

End dsl_supportsInterface.

Section dsl_mint.
  Context `{ _to: Expr address }.
  Context `{ __to: address }.
  Context `{ to_immutable:
               forall this st env msg, _to this st env msg = Valid __to }.

  Context `{ _token: Expr uint256 }.
  Context `{ __token: uint256 }.
  Context `{ token_immutable:
               forall this st env msg, _token this st env msg = Valid __token }.

  Hint Rewrite
       to_immutable
       token_immutable
    : dsl_proof.

  Definition mint_dsl : Stmt :=
    (@require(_to != zero);
     @require(tokenOwner[_token] == zero);
     @require(ownedTokensCount[_to] <= max_uint256 - one);
     @tokenOwner[_token] = _to;
     @ownedTokensCount[_to] += one;
     @emit Transfer(zero, _to, _token)
    )%dsl.

  Lemma mint_dsl_sat_spec:
      dsl_sat_spec (mc_mint __to __token)
                   mint_dsl
                   (funcspec_mint __to __token).
  Proof.
    unfold dsl_sat_spec.
    intros st env msg this Hfunc Hreq st0 result Hexec Hinv.
    generalize max_uint256_lt_1. intros max.
    unfold funcspec_mint in *.
    simpl in *.
    destruct Hreq as [Hreq_tokenOwner [Hreq_ownedTokenCount Hto]].
    apply Nat.eqb_eq in Hreq_tokenOwner.
    apply Nat.leb_le in Hreq_ownedTokenCount.
    apply Nat.eqb_neq in Hto.

    unfold dsl_neq,  dsl_sub,dsl_eq, dsl_le,dsl_add, dsl_tokenOwner_access, dsl_ownedTokensCount_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    rewrite Hto in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite Hreq_tokenOwner in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
    rewrite Hreq_ownedTokenCount in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.
    rewrite (plus_safe_lt _ _) in Hexec.
    simpl in Hexec.
    autorewrite with dsl_proof in Hexec.

    rewrite <- Hexec.
    simpl.
    split.
    - unfold INV in *. intros owner Howner.
      simpl.
      destruct (Nat.eq_dec __to owner).
      + (* __to = owner *)
        subst __to.
        A2V.msimpl.
        assert (length
    (V2A.map_filter (V2A.upd (st_tokenOwner st) __token owner)
                    (fun e : nat * address => snd e =? owner)) =
                length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner)) +1 ).
        apply V2A.filter_length_upd_false_true with __token.
        simpl. apply Nat.eqb_eq in Hreq_tokenOwner.
        rewrite  Hreq_tokenOwner. apply Nat.eqb_neq. auto.
        simpl. rewrite (V2A.get_upd_eq); auto. apply Nat.eqb_eq. auto.
        intros k' Hktoken. rewrite (V2A.get_upd_neq); auto.
        
        rewrite H. apply Nat.add_cancel_r.
        apply Hinv. auto.
      + (*__to <> owner *)
        rewrite (A2V.get_upd_neq); auto.
        assert (length (V2A.map_filter (V2A.upd (st_tokenOwner st) __token __to)
                    (fun e : nat * address => snd e =? owner)) =
                length (V2A.map_filter (st_tokenOwner st) (fun e : nat * address => snd e =? owner))).

        apply V2A.filter_length_f_equal.
        intros k. simpl.
        apply Nat.eqb_eq in Hreq_tokenOwner.
        destruct (Nat.eq_dec __token k).
        {
          subst __token. rewrite (V2A.get_upd_eq); auto.
          rewrite Hreq_tokenOwner.
          apply Nat.neq_sym in Howner.
          apply Nat.eqb_neq in Howner. apply Nat.eqb_neq in n.
          rewrite Howner, n. auto.
        }
        {
          rewrite (V2A.get_upd_neq); auto.
        }

        rewrite H.
        apply Hinv;auto.

    - apply Nat.leb_le in Hreq_ownedTokenCount.
      repeat (split;auto).
      unfold A2V.upd_inc. 
      rewrite (plus_safe_lt _ _); auto.
      
    - apply Nat.leb_le in Hreq_ownedTokenCount; auto.
Qed.        
    
  Lemma mint_dsl_revert:
    forall st env msg this,
      m_func msg = mc_mint __to __token ->
      INV st env msg ->
      ~ spec_require (funcspec_mint __to __token this env msg) st ->
      forall result,
        dsl_exec mint_dsl st st env msg this nil = result ->
        result = Stop st (ev_revert this :: nil) /\
        INV (ret_st result) env msg.
  Proof.
    intros st env msg this Hfunc Hinv Hreq_neg result Hexec.
    generalize max_uint256_lt_1. intros max.
    unfold funcspec_mint in *.
    simpl in *.

    unfold dsl_neq, dsl_sub, dsl_eq, dsl_tokenOwner_access, dsl_le, dsl_add, dsl_ownedTokensCount_access in Hexec.
    autorewrite with dsl_proof in Hexec.
    simpl in Hexec.
    destruct (Nat.eq_dec __to 0).
    - (* __to = 0 *)
      apply Nat.eqb_eq in e. rewrite e in Hexec.
      simpl in Hexec.
      rewrite <- Hexec. split;auto.
    - (* __to <> 0 *)
      apply Nat.eqb_neq in n. rewrite n in Hexec.
      simpl in Hexec.
      autorewrite with dsl_proof in Hexec.
      destruct (Nat.eq_dec (V2A.get (st_tokenOwner st) __token) 0).
      + (*V2A.get (st_tokenOwner st) __token = 0*)
        apply Nat.eqb_eq in e. rewrite e in Hexec.
        simpl in Hexec.
        autorewrite with dsl_proof in Hexec.
        rewrite (minus_safe _ _) in Hexec; [> idtac | auto].
        destruct (le_dec (A2V.get (st_ownedTokensCount st) __to) (MAX_UINT256 - 1)).
        {
          assert((V2A.get (st_tokenOwner st) __token = 0 /\
                  A2V.get (st_ownedTokensCount st) __to <= MAX_UINT256 - 1 /\ __to <> 0)).
          split. apply Nat.eqb_eq in e. auto.
          split. auto.
          apply Nat.eqb_neq in n. auto.

          contradiction.
          
        }
        {
          apply Nat.leb_nle in n0.
          rewrite n0 in Hexec.
          simpl in Hexec.
          rewrite <- Hexec.
          split;auto.
        }
      +  (*V2A.get (st_tokenOwner st) __token <> 0*)
        apply Nat.eqb_neq in n0.
        rewrite n0 in Hexec.
        simpl in Hexec.
        rewrite <- Hexec.
        split; auto.
Qed.        

End dsl_mint.