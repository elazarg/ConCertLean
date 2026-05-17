/- Port of the abstract CIS1 specification layer from examples/cis1/CIS1Spec.v. -/

import ConCert.Examples.CIS1.CIS1
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Perm.Basic

namespace ConCert.Examples.CIS1

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.SerializableBase

namespace Spec

variable [Base : ChainBase]

/-- The abstract storage view used by the CIS1 standard specification. -/
structure View (Storage TokenID : Type) where
  get_balance_opt : Storage → TokenID → Base.Address → Option TokenAmount
  get_operators : Storage → Base.Address → List Base.Address
  get_owners : Storage → TokenID → List Base.Address
  get_owners_no_dup :
    ∀ st token_id, (get_owners st token_id).Nodup
  get_owners_balances :
    ∀ st owner token_id,
      owner ∈ get_owners st token_id ↔
        ∃ balance, get_balance_opt st token_id owner = some balance
  token_id_exists : Storage → TokenID → Bool

namespace ReceiveHook

abbrev Params (TokenID : Type) : Type :=
  TokenID × TokenAmount × Base.Address

inductive ReceiverMsg (TokenID Msg : Type) where
  | receive_hook : Params (Base := Base) TokenID → ReceiverMsg TokenID Msg
  | other_msg : Msg → ReceiverMsg TokenID Msg
  deriving Serializable

end ReceiveHook

namespace Axioms

variable {Storage TokenID : Type} [Serializable TokenID]
variable (view : View (Base := Base) Storage TokenID)

def get_balance (st : Storage) (token_id : TokenID) (addr : Base.Address) :
    Option TokenAmount :=
  if view.token_id_exists st token_id then
    match view.get_balance_opt st token_id addr with
    | some bal => some bal
    | none => some 0
  else
    none

def get_balance_total
    (st : Storage) (token_id : TokenID)
    (_p : view.token_id_exists st token_id = true)
    (addr : Base.Address) : TokenAmount :=
  (get_balance view st token_id addr).getD 0

structure TransferData where
  token_id : TokenID
  amount : TokenAmount
  from_ : Base.Address
  to_ : Base.Address

structure TransferParams where
  transfers : List (@TransferData Base TokenID)

inductive UpdateOperatorKind where
  | remove_operator
  | add_operator
  deriving DecidableEq

structure UpdateOperatorUpdate where
  kind : UpdateOperatorKind
  operator_address : Base.Address

structure UpdateOperatorParams where
  updates : List (@UpdateOperatorUpdate Base)

structure BalanceOfQuery where
  token_id : TokenID
  address : Base.Address

structure BalanceOfParams where
  query : List (@BalanceOfQuery Base TokenID)
  result_address : Base.Address
  result_address_is_contract :
    Base.address_is_contract result_address = true

inductive EntryPoint where
  | transfer : @TransferParams Base TokenID → EntryPoint
  | updateOperator : @UpdateOperatorParams Base → EntryPoint
  | balanceOf : @BalanceOfParams Base TokenID → EntryPoint

def transfer_to (params : @TransferParams Base TokenID) :
    List (TokenID × Base.Address) :=
  params.transfers.map (fun x => (x.token_id, x.to_))

def transfer_from (params : @TransferParams Base TokenID) :
    List (TokenID × Base.Address) :=
  params.transfers.map (fun x => (x.token_id, x.from_))

def get_receive_hook_params
    (params : List (@TransferData Base TokenID)) :
    List (Base.Address × ReceiveHook.Params (Base := Base) TokenID) :=
  params.map (fun x => (x.to_, (x.token_id, x.amount, x.from_)))

def transfer_single_spec
    (prev_st next_st : Storage)
    (token_id : TokenID)
    (p : view.token_id_exists prev_st token_id = true)
    (q : view.token_id_exists next_st token_id = true)
    (owner from_ to_ : Base.Address)
    (amount : TokenAmount) : Prop :=
  let prev_from := get_balance_total view prev_st token_id p from_
  let next_from := get_balance_total view next_st token_id q from_
  let prev_to := get_balance_total view prev_st token_id p to_
  let next_to := get_balance_total view next_st token_id q to_
  (∀ addr, addr ≠ from_ → addr ≠ to_ →
    view.get_balance_opt next_st token_id addr =
      view.get_balance_opt prev_st token_id addr) ∧
  (∀ addr other_token_id, other_token_id ≠ token_id →
    view.get_balance_opt next_st other_token_id addr =
      view.get_balance_opt prev_st other_token_id addr) ∧
  (∀ token_id,
    view.token_id_exists prev_st token_id =
      view.token_id_exists next_st token_id) ∧
  (from_ = owner ∨ from_ ∈ view.get_operators prev_st owner) ∧
  (from_ ≠ to_ → prev_from = next_from + amount ∧ next_to = prev_to + amount) ∧
  (from_ = to_ → amount ≤ prev_from ∧ prev_from = next_from)

def compose_transfers
    (init_st final_st : Storage)
    (params : List (@TransferData Base TokenID))
    (single_transfer :
      ∀ (prev_st next_st : Storage)
        (params : @TransferData Base TokenID),
        view.token_id_exists prev_st params.token_id = true →
        view.token_id_exists next_st params.token_id = true → Prop) : Prop :=
  match params with
  | [] => init_st = final_st
  | pr :: ps =>
      ∃ (st : Storage)
        (p : view.token_id_exists init_st pr.token_id = true)
        (q : view.token_id_exists st pr.token_id = true),
        single_transfer init_st st pr p q ∧
          compose_transfers st final_st ps single_transfer

def is_valid_receive_hook
    (p : ReceiveHook.Params (Base := Base) TokenID)
    (serialized_params : SerializedValue) : Prop :=
  ∃ (Msg : Type) (_ : Serializable Msg)
    (f : Msg → ReceiveHook.Params (Base := Base) TokenID) (msg : Msg),
    deserialize serialized_params = some msg ∧ f msg = p

structure TransferSpec
    (ctx : @ContractCallContext Base)
    (params : @TransferParams Base TokenID)
    (prev_st next_st : Storage)
    (ret_ops : List (@ActionBody Base)) : Prop where
  transfer_dec_inc :
    compose_transfers view prev_st next_st params.transfers
      (fun st1 st2 x p q =>
        transfer_single_spec view st1 st2 x.token_id p q
          ctx.ctx_from x.from_ x.to_ x.amount)
  transfer_receive_hook_calls :
    let transfers_to_contracts :=
      params.transfers.filter (fun x => Base.address_is_contract x.to_)
    List.Forall₂
      (fun op pair =>
        ∃ val,
          op = ActionBody.act_call pair.1 0 val ∧
            is_valid_receive_hook pair.2 val)
      ret_ops
      (get_receive_hook_params transfers_to_contracts)

def updateOperator_single_spec
    (ctx : @ContractCallContext Base)
    (prev_st next_st : Storage)
    (p : @UpdateOperatorUpdate Base) : Prop :=
  match p.kind with
  | .remove_operator =>
      let addr := p.operator_address
      (∀ addr0, addr0 ≠ addr →
        (addr0 ∈ view.get_operators prev_st ctx.ctx_from ↔
          addr0 ∈ view.get_operators next_st ctx.ctx_from)) ∧
      addr ∉ view.get_operators next_st ctx.ctx_from
  | .add_operator =>
      let addr := p.operator_address
      (∀ addr0, addr0 ≠ addr →
        (addr0 ∈ view.get_operators prev_st ctx.ctx_from ↔
          addr0 ∈ view.get_operators next_st ctx.ctx_from)) ∧
      addr ∈ view.get_operators next_st ctx.ctx_from

def compose_updateOperator_specs
    (ctx : @ContractCallContext Base)
    (st final_st : Storage)
    (updates : List (@UpdateOperatorUpdate Base)) : Prop :=
  match updates with
  | [] => st = final_st
  | p :: ps =>
      ∃ next_st,
        updateOperator_single_spec view ctx st next_st p ∧
          compose_updateOperator_specs ctx next_st final_st ps

structure UpdateOperatorSpec
    (ctx : @ContractCallContext Base)
    (params : @UpdateOperatorParams Base)
    (prev_st next_st : Storage)
    (_ret_ops : List (@ActionBody Base)) : Prop where
  token_ids_preserved :
    ∀ token_id,
      view.token_id_exists prev_st token_id =
        view.token_id_exists next_st token_id
  balances_preserved :
    ∀ addr token_id,
      view.get_balance_opt prev_st token_id addr =
        view.get_balance_opt next_st token_id addr
  add_remove :
    compose_updateOperator_specs view ctx prev_st next_st params.updates

abbrev BalanceOfCallbackType : Type :=
  List (TokenID × Base.Address × TokenAmount)

def get_balances (st : Storage)
    (params : @BalanceOfParams Base TokenID) :
    Option (@BalanceOfCallbackType Base TokenID) :=
  params.query.mapM (fun q => do
    let balance ← get_balance view st q.token_id q.address
    some (q.token_id, q.address, balance))

structure BalanceOfSpec
    (params : @BalanceOfParams Base TokenID)
    (prev_st next_st : Storage)
    (ret_ops : List (@ActionBody Base)) : Prop where
  operators_preserved :
    ∀ addr, view.get_operators next_st addr = view.get_operators prev_st addr
  token_ids_preserved :
    ∀ token_id,
      view.token_id_exists prev_st token_id =
        view.token_id_exists next_st token_id
  balances_preserved :
    ∀ token_id addr,
      view.get_balance_opt next_st token_id addr =
        view.get_balance_opt prev_st token_id addr
  callback :
    match get_balances view prev_st params with
    | some query_results =>
        ret_ops =
          [ActionBody.act_call params.result_address 0 (serialize query_results)]
    | none => False

end Axioms

namespace ReceiveSpec

open Axioms

variable {Storage TokenID Msg : Type} [Serializable TokenID]
variable (view : View (Base := Base) Storage TokenID)

/-- Abstract interface expected from a concrete CIS1 receiver. -/
structure Spec where
  get_CIS1_entry_point :
    Msg → Option (@EntryPoint Base TokenID)
  get_contract_msg :
    @EntryPoint Base TokenID → Msg
  left_inverse_get_CIS1_entry_point :
    ∀ entry_point,
      get_CIS1_entry_point (get_contract_msg entry_point) = some entry_point
  contract_receive :
    Chain → @ContractCallContext Base → Storage → Option Msg →
      Option (Storage × List (@ActionBody Base))
  contract_receive_spec :
    ∀ chain ctx prev_st msg next_st ret_ops entry_point,
      get_CIS1_entry_point msg = some entry_point →
      contract_receive chain ctx prev_st (some msg) = some (next_st, ret_ops) →
      match entry_point with
      | .transfer params =>
          TransferSpec view ctx params prev_st next_st ret_ops
      | .updateOperator params =>
          UpdateOperatorSpec view ctx params prev_st next_st ret_ops
      | .balanceOf params =>
          BalanceOfSpec view params prev_st next_st ret_ops

end ReceiveSpec

namespace Operators

open Axioms

variable {Storage TokenID : Type}
variable {view : View (Base := Base) Storage TokenID}

theorem compose_updateOperator_add_add
    (ctx : @ContractCallContext Base)
    (prev_st next_st : Storage) (addr1 addr2 : Base.Address)
    (h :
      compose_updateOperator_specs view ctx prev_st next_st
        [{ kind := .add_operator, operator_address := addr1 },
         { kind := .add_operator, operator_address := addr2 }]) :
    addr1 ∈ view.get_operators next_st ctx.ctx_from := by
  rcases h with ⟨st1, hst1, st2, hst2, heq⟩
  subst next_st
  rcases hst1 with ⟨_hstable1, hadd1⟩
  rcases hst2 with ⟨hstable2, hadd2⟩
  by_cases heq : addr1 = addr2
  · subst addr2
    exact hadd2
  · exact (hstable2 addr1 heq).mp hadd1

theorem compose_updateOperator_add_remove_same
    (ctx : @ContractCallContext Base)
    (prev_st next_st : Storage) (addr : Base.Address)
    (h :
      compose_updateOperator_specs view ctx prev_st next_st
        [{ kind := .add_operator, operator_address := addr },
         { kind := .remove_operator, operator_address := addr }]) :
    addr ∉ view.get_operators next_st ctx.ctx_from := by
  rcases h with ⟨st1, _hst1, st2, hst2, heq⟩
  subst next_st
  exact hst2.2

theorem compose_updateOperator_remove_one_remove_another
    (ctx : @ContractCallContext Base)
    (prev_st next_st : Storage) (addr1 addr2 : Base.Address)
    (hneq : addr1 ≠ addr2)
    (h :
      compose_updateOperator_specs view ctx prev_st next_st
        [{ kind := .remove_operator, operator_address := addr1 },
         { kind := .add_operator, operator_address := addr2 }]) :
    addr1 ∉ view.get_operators next_st ctx.ctx_from := by
  rcases h with ⟨st1, hst1, st2, hst2, heq⟩
  subst next_st
  rcases hst1 with ⟨_hstable1, hremoved1⟩
  rcases hst2 with ⟨hstable2, _hadd2⟩
  intro hin
  exact hremoved1 ((hstable2 addr1 hneq).mpr hin)

end Operators

namespace Balances

open Axioms

variable {Storage TokenID : Type}
variable {view : View (Base := Base) Storage TokenID}

def get_balance_default
    (st : Storage) (token_id : TokenID) (addr : Base.Address) :
    TokenAmount :=
  (get_balance view st token_id addr).getD 0

def sum_balances
    (st : Storage) (token_id : TokenID) (owners : List Base.Address) :
    TokenAmount :=
  (owners.map (fun addr => get_balance_default (view := view) st token_id addr)).sum

omit Base in
private theorem list_sum_of_perm {xs ys : List Nat} (h : xs.Perm ys) :
    xs.sum = ys.sum := by
  simpa [List.sum_eq_foldr] using
    (h.foldr_eq (f := fun x acc => x + acc) 0)

def removeAddr (addr : Base.Address) (owners : List Base.Address) :
    List Base.Address :=
  owners.filter (fun owner => decide (owner ≠ addr))

theorem mem_removeAddr {addr owner : Base.Address}
    {owners : List Base.Address} :
    addr ∈ removeAddr owner owners ↔ addr ≠ owner ∧ addr ∈ owners := by
  classical
  simp [removeAddr, and_comm]

theorem remove_owner
    (st : Storage) (token_id : TokenID)
    (owners : List Base.Address) (owner : Base.Address)
    (h :
      owner ∈ owners ∨
        get_balance_default (view := view) st token_id owner = 0)
    (hnd : owners.Nodup) :
    sum_balances (view := view) st token_id owners =
      get_balance_default (view := view) st token_id owner +
        sum_balances (view := view) st token_id
          (removeAddr (Base := Base) owner owners) := by
  classical
  by_cases hmem : owner ∈ owners
  · have hperm :
        (owner :: removeAddr (Base := Base) owner owners).Perm owners := by
      have hndleft :
          (owner :: removeAddr (Base := Base) owner owners).Nodup := by
        constructor
        · intro a ha
          exact (mem_removeAddr.mp ha).1.symm
        · exact hnd.filter _
      exact (List.perm_ext_iff_of_nodup hndleft hnd).mpr (by
        intro x
        rw [List.mem_cons, mem_removeAddr]
        constructor
        · intro hx
          rcases hx with rfl | ⟨_hne, hxowners⟩
          · exact hmem
          · exact hxowners
        · intro hxowners
          by_cases hx : x = owner
          · exact Or.inl hx
          · exact Or.inr ⟨hx, hxowners⟩)
    have hsum := list_sum_of_perm
      (hperm.map
        (fun addr => get_balance_default (view := view) st token_id addr))
    simpa [sum_balances, removeAddr] using hsum.symm
  · have hzero :
        get_balance_default (view := view) st token_id owner = 0 := by
      cases h with
      | inl hin => exact False.elim (hmem hin)
      | inr hz => exact hz
    have hfilter : removeAddr (Base := Base) owner owners = owners := by
      unfold removeAddr
      apply List.filter_eq_self.mpr
      intro x hx
      have hxne : x ≠ owner := by
        intro heq
        exact hmem (by simpa [heq] using hx)
      simp [hxne]
    rw [hfilter, hzero, Nat.zero_add]

theorem sum_of_balances_eq
    {addrs : List Base.Address} {prev_st next_st : Storage}
    {token_id : TokenID}
    (hbal :
      ∀ addr, addr ∈ addrs →
        get_balance_default (view := view) next_st token_id addr =
          get_balance_default (view := view) prev_st token_id addr) :
    sum_balances (view := view) next_st token_id addrs =
      sum_balances (view := view) prev_st token_id addrs := by
  induction addrs with
  | nil =>
      simp [sum_balances]
  | cons addr addrs ih =>
      have htail := ih (by
        intro a ha
        exact hbal a (by simp [ha]))
      change
        get_balance_default (view := view) next_st token_id addr +
            sum_balances (view := view) next_st token_id addrs =
          get_balance_default (view := view) prev_st token_id addr +
            sum_balances (view := view) prev_st token_id addrs
      rw [hbal addr (by simp)]
      exact congrArg
        (fun n =>
          get_balance_default (view := view) prev_st token_id addr + n)
        htail

theorem sum_balances_extensional
    (st : Storage) (token_id : TokenID)
    {owners1 owners2 : List Base.Address}
    (hnd1 : owners1.Nodup) (hnd2 : owners2.Nodup)
    (hiff : ∀ addr, addr ∈ owners1 ↔ addr ∈ owners2) :
    sum_balances (view := view) st token_id owners1 =
      sum_balances (view := view) st token_id owners2 := by
  have hperm : owners1.Perm owners2 :=
    (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr hiff
  exact list_sum_of_perm
    (hperm.map
      (fun addr => get_balance_default (view := view) st token_id addr))

theorem sum_of_balances_eq_extensional
    {owners1 owners2 : List Base.Address}
    {prev_st next_st : Storage} {token_id : TokenID}
    (hnd1 : owners1.Nodup) (hnd2 : owners2.Nodup)
    (hiff : ∀ addr, addr ∈ owners1 ↔ addr ∈ owners2)
    (hbal :
      ∀ addr, addr ∈ owners1 →
        get_balance_default (view := view) next_st token_id addr =
          get_balance_default (view := view) prev_st token_id addr) :
    sum_balances (view := view) next_st token_id owners1 =
      sum_balances (view := view) prev_st token_id owners2 := by
  calc
    sum_balances (view := view) next_st token_id owners1 =
        sum_balances (view := view) prev_st token_id owners1 :=
      sum_of_balances_eq (view := view) hbal
    _ = sum_balances (view := view) prev_st token_id owners2 :=
      sum_balances_extensional (view := view) prev_st token_id hnd1 hnd2 hiff

theorem get_balance_opt_default
    {next_st prev_st : Storage} {token_id : TokenID} {addr : Base.Address}
    (hids :
      view.token_id_exists prev_st token_id =
        view.token_id_exists next_st token_id)
    (hopt :
      view.get_balance_opt next_st token_id addr =
        view.get_balance_opt prev_st token_id addr) :
    get_balance_default (view := view) next_st token_id addr =
      get_balance_default (view := view) prev_st token_id addr := by
  unfold get_balance_default get_balance
  rw [← hids]
  rw [hopt]

theorem get_balance_total_get_balance_default
    (st : Storage) (token_id : TokenID)
    (p : view.token_id_exists st token_id = true)
    (owner : Base.Address) :
    get_balance_total view st token_id p owner =
      get_balance_default (view := view) st token_id owner := rfl

theorem same_owners_of_balances
    {next_st prev_st : Storage} {token_id : TokenID}
    (hbal :
      ∀ addr,
        view.get_balance_opt next_st token_id addr =
          view.get_balance_opt prev_st token_id addr) :
    ∀ addr,
      addr ∈ view.get_owners next_st token_id ↔
        addr ∈ view.get_owners prev_st token_id := by
  intro addr
  rw [view.get_owners_balances, view.get_owners_balances]
  constructor
  · rintro ⟨balance, hnext⟩
    exact ⟨balance, by rwa [← hbal addr]⟩
  · rintro ⟨balance, hprev⟩
    exact ⟨balance, by rwa [hbal addr]⟩

theorem in_owners_or_zero_balance_default
    (st : Storage) (token_id : TokenID) (owner : Base.Address) :
    owner ∈ view.get_owners st token_id ∨
      get_balance_default (view := view) st token_id owner = 0 := by
  by_cases hmem : owner ∈ view.get_owners st token_id
  · exact Or.inl hmem
  · right
    unfold get_balance_default get_balance
    cases view.token_id_exists st token_id <;> simp
    cases hopt : view.get_balance_opt st token_id owner <;> simp
    exact False.elim
      (hmem ((view.get_owners_balances st owner token_id).mpr ⟨_, hopt⟩))

private theorem compose_transfer_token_ids_preserved
    {ctx : @ContractCallContext Base}
    {transfers : List (@TransferData Base TokenID)}
    {prev_st next_st : Storage} {token_id : TokenID}
    (h :
      compose_transfers view prev_st next_st transfers
        (fun st1 st2 x p q =>
          transfer_single_spec view st1 st2 x.token_id p q
            ctx.ctx_from x.from_ x.to_ x.amount)) :
    view.token_id_exists prev_st token_id =
      view.token_id_exists next_st token_id := by
  revert prev_st
  induction transfers with
  | nil =>
      intro prev_st h
      simp [compose_transfers] at h
      subst next_st
      rfl
  | cons transfer transfers ih =>
      intro prev_st h
      simp [compose_transfers] at h
      exact Exists.elim h (fun st h1 => by
        let hrest := h1.2
        rcases h1.1 with ⟨_p, _q, hsingle⟩
        rcases hsingle with
          ⟨_hbal, _hother, hids, _hauth, _hmove, _hself⟩
        exact (hids token_id).trans (ih hrest))

theorem transfer_token_ids_preserved
    (ctx : @ContractCallContext Base)
    (transfers : List (@TransferData Base TokenID))
    (prev_st next_st : Storage) (ops : List (@ActionBody Base))
    (token_id : TokenID)
    (spec :
      TransferSpec view ctx { transfers := transfers } prev_st next_st ops) :
    view.token_id_exists prev_st token_id =
      view.token_id_exists next_st token_id :=
  compose_transfer_token_ids_preserved
    (view := view) (ctx := ctx) (transfers := transfers)
    (token_id := token_id) spec.transfer_dec_inc

private theorem compose_transfer_other_balances_preserved
    {ctx : @ContractCallContext Base}
    {transfers : List (@TransferData Base TokenID)}
    {prev_st next_st : Storage} {addr : Base.Address} {token_id : TokenID}
    (h :
      compose_transfers view prev_st next_st transfers
        (fun st1 st2 x p q =>
          transfer_single_spec view st1 st2 x.token_id p q
            ctx.ctx_from x.from_ x.to_ x.amount))
    (hfrom :
      (token_id, addr) ∉
        transfer_from { transfers := transfers })
    (hto :
      (token_id, addr) ∉
        transfer_to { transfers := transfers }) :
    view.get_balance_opt prev_st token_id addr =
      view.get_balance_opt next_st token_id addr := by
  revert prev_st
  induction transfers with
  | nil =>
      intro prev_st h
      simp [compose_transfers] at h
      subst next_st
      rfl
  | cons transfer transfers ih =>
      intro prev_st h
      simp [compose_transfers] at h
      exact Exists.elim h (fun st h1 => by
        let hrest := h1.2
        rcases h1.1 with ⟨_p, _q, hsingle⟩
        rcases hsingle with
          ⟨hbal_not_addr, hbal_other_tokens, _hids, _hauth, _hmove, _hself⟩
        have hfrom_tail :
            (token_id, addr) ∉
              transfer_from { transfers := transfers } := by
          intro hin
          exact hfrom (by
            change (token_id, addr) ∈
              (transfer :: transfers).map (fun x => (x.token_id, x.from_))
            exact List.mem_cons_of_mem _ hin)
        have hto_tail :
            (token_id, addr) ∉
              transfer_to { transfers := transfers } := by
          intro hin
          exact hto (by
            change (token_id, addr) ∈
              (transfer :: transfers).map (fun x => (x.token_id, x.to_))
            exact List.mem_cons_of_mem _ hin)
        have hfirst_from :
            (token_id, addr) ≠ (transfer.token_id, transfer.from_) := by
          intro heq
          exact hfrom (by
            change (token_id, addr) ∈
              (transfer :: transfers).map (fun x => (x.token_id, x.from_))
            simp [heq])
        have hfirst_to :
            (token_id, addr) ≠ (transfer.token_id, transfer.to_) := by
          intro heq
          exact hto (by
            change (token_id, addr) ∈
              (transfer :: transfers).map (fun x => (x.token_id, x.to_))
            simp [heq])
        have hfirst :
            view.get_balance_opt prev_st token_id addr =
              view.get_balance_opt st token_id addr := by
          by_cases htok : token_id = transfer.token_id
          · subst token_id
            have haddr_from : addr ≠ transfer.from_ := by
              intro haddr
              exact hfirst_from (by simp [haddr])
            have haddr_to : addr ≠ transfer.to_ := by
              intro haddr
              exact hfirst_to (by simp [haddr])
            exact (hbal_not_addr addr haddr_from haddr_to).symm
          · exact (hbal_other_tokens addr token_id htok).symm
        exact hfirst.trans (ih hfrom_tail hto_tail hrest))

theorem transfer_other_balances_preserved
    (ctx : @ContractCallContext Base)
    (transfers : List (@TransferData Base TokenID))
    (prev_st next_st : Storage) (ops : List (@ActionBody Base))
    (addr : Base.Address) (token_id : TokenID)
    (spec :
      TransferSpec view ctx { transfers := transfers } prev_st next_st ops)
    (hfrom :
      (token_id, addr) ∉
        transfer_from { transfers := transfers })
    (hto :
      (token_id, addr) ∉
        transfer_to { transfers := transfers }) :
    view.get_balance_opt prev_st token_id addr =
      view.get_balance_opt next_st token_id addr :=
  compose_transfer_other_balances_preserved
    (view := view) (ctx := ctx) (transfers := transfers)
    spec.transfer_dec_inc hfrom hto

theorem transfer_single_spec_sufficient_funds
    {prev_st next_st : Storage} {token_id : TokenID}
    {from_ to_ owner : Base.Address} {amount : TokenAmount}
    {p : view.token_id_exists prev_st token_id = true}
    {q : view.token_id_exists next_st token_id = true}
    (spec :
      transfer_single_spec view prev_st next_st token_id p q
        owner from_ to_ amount) :
    get_balance_total view prev_st token_id p from_ ≥ amount := by
  rcases spec with ⟨_hbal, _hother, _hids, _hauth, htransfer, hself⟩
  by_cases haddr : from_ = to_
  · exact (hself haddr).1
  · have h := (htransfer haddr).1
    rw [h]
    exact Nat.le_add_left amount _

theorem transfer_single_spec_preserves_balances
    {prev_st next_st : Storage} {token_id : TokenID}
    {owner from_ to_ : Base.Address} {amount : TokenAmount}
    {p : view.token_id_exists prev_st token_id = true}
    {q : view.token_id_exists next_st token_id = true}
    (spec :
      transfer_single_spec view prev_st next_st token_id p q
        owner from_ to_ amount) :
    let owners1 := view.get_owners prev_st token_id
    let owners2 := view.get_owners next_st token_id
    sum_balances (view := view) next_st token_id owners2 =
      sum_balances (view := view) prev_st token_id owners1 := by
  intro owners1 owners2
  rcases spec with
    ⟨hbal_not_addr, _hbal_other_tokens, hids, _hauth, htransfer, hself_transfer⟩
  by_cases haddr : from_ = to_
  · subst to_
    have hprev_split :=
      remove_owner (view := view) prev_st token_id owners1 from_
        (in_owners_or_zero_balance_default (view := view) prev_st token_id from_)
        (view.get_owners_no_dup prev_st token_id)
    have hnext_split :=
      remove_owner (view := view) next_st token_id owners2 from_
        (in_owners_or_zero_balance_default (view := view) next_st token_id from_)
        (view.get_owners_no_dup next_st token_id)
    have hrem :
        sum_balances (view := view) next_st token_id
            (removeAddr (Base := Base) from_ owners2) =
          sum_balances (view := view) prev_st token_id
            (removeAddr (Base := Base) from_ owners1) := by
      apply sum_of_balances_eq_extensional (view := view)
      · exact (view.get_owners_no_dup next_st token_id).filter _
      · exact (view.get_owners_no_dup prev_st token_id).filter _
      · intro addr
        rw [mem_removeAddr, mem_removeAddr]
        constructor
        · rintro ⟨hne, hin_next⟩
          refine ⟨hne, ?_⟩
          rw [view.get_owners_balances] at hin_next ⊢
          rcases hin_next with ⟨balance, hnext⟩
          exact ⟨balance, by rwa [← hbal_not_addr addr hne hne]⟩
        · rintro ⟨hne, hin_prev⟩
          refine ⟨hne, ?_⟩
          rw [view.get_owners_balances] at hin_prev ⊢
          rcases hin_prev with ⟨balance, hprev⟩
          exact ⟨balance, by rwa [hbal_not_addr addr hne hne]⟩
      · intro addr hin
        have hne := (mem_removeAddr.mp hin).1
        exact get_balance_opt_default (view := view)
          (hids token_id) (hbal_not_addr addr hne hne)
    have hsame :
        get_balance_default (view := view) next_st token_id from_ =
          get_balance_default (view := view) prev_st token_id from_ := by
      have h := (hself_transfer rfl).2
      simpa [get_balance_total, get_balance_default] using h.symm
    rw [hnext_split, hprev_split, hrem, hsame]
  · have hprev_from_split :=
      remove_owner (view := view) prev_st token_id owners1 from_
        (in_owners_or_zero_balance_default (view := view) prev_st token_id from_)
        (view.get_owners_no_dup prev_st token_id)
    have hprev_to_cond :
        to_ ∈ removeAddr (Base := Base) from_ owners1 ∨
          get_balance_default (view := view) prev_st token_id to_ = 0 := by
      rcases in_owners_or_zero_balance_default
          (view := view) prev_st token_id to_ with hin | hz
      · left
        rw [mem_removeAddr]
        exact ⟨Ne.symm haddr, hin⟩
      · exact Or.inr hz
    have hprev_to_split :=
      remove_owner (view := view) prev_st token_id
        (removeAddr (Base := Base) from_ owners1) to_
        hprev_to_cond
        ((view.get_owners_no_dup prev_st token_id).filter _)
    have hnext_from_split :=
      remove_owner (view := view) next_st token_id owners2 from_
        (in_owners_or_zero_balance_default (view := view) next_st token_id from_)
        (view.get_owners_no_dup next_st token_id)
    have hnext_to_cond :
        to_ ∈ removeAddr (Base := Base) from_ owners2 ∨
          get_balance_default (view := view) next_st token_id to_ = 0 := by
      rcases in_owners_or_zero_balance_default
          (view := view) next_st token_id to_ with hin | hz
      · left
        rw [mem_removeAddr]
        exact ⟨Ne.symm haddr, hin⟩
      · exact Or.inr hz
    have hnext_to_split :=
      remove_owner (view := view) next_st token_id
        (removeAddr (Base := Base) from_ owners2) to_
        hnext_to_cond
        ((view.get_owners_no_dup next_st token_id).filter _)
    have hrem :
        sum_balances (view := view) next_st token_id
            (removeAddr (Base := Base) to_
              (removeAddr (Base := Base) from_ owners2)) =
          sum_balances (view := view) prev_st token_id
            (removeAddr (Base := Base) to_
              (removeAddr (Base := Base) from_ owners1)) := by
      apply sum_of_balances_eq_extensional (view := view)
      · exact ((view.get_owners_no_dup next_st token_id).filter _).filter _
      · exact ((view.get_owners_no_dup prev_st token_id).filter _).filter _
      · intro addr
        simp only [mem_removeAddr]
        constructor
        · rintro ⟨hne_to, hne_from, hin_next⟩
          refine ⟨hne_to, hne_from, ?_⟩
          rw [view.get_owners_balances] at hin_next ⊢
          rcases hin_next with ⟨balance, hnext⟩
          exact ⟨balance, by rwa [← hbal_not_addr addr hne_from hne_to]⟩
        · rintro ⟨hne_to, hne_from, hin_prev⟩
          refine ⟨hne_to, hne_from, ?_⟩
          rw [view.get_owners_balances] at hin_prev ⊢
          rcases hin_prev with ⟨balance, hprev⟩
          exact ⟨balance, by rwa [hbal_not_addr addr hne_from hne_to]⟩
      · intro addr hin
        have hne_to := (mem_removeAddr.mp hin).1
        have hin_from_removed := (mem_removeAddr.mp hin).2
        have hne_from := (mem_removeAddr.mp hin_from_removed).1
        exact get_balance_opt_default (view := view)
          (hids token_id) (hbal_not_addr addr hne_from hne_to)
    rcases htransfer haddr with ⟨hfrom_bal, hto_bal⟩
    have hfrom_default :
        get_balance_default (view := view) prev_st token_id from_ =
          get_balance_default (view := view) next_st token_id from_ + amount := by
      simpa [get_balance_total, get_balance_default] using hfrom_bal
    have hto_default :
        get_balance_default (view := view) next_st token_id to_ =
          get_balance_default (view := view) prev_st token_id to_ + amount := by
      simpa [get_balance_total, get_balance_default] using hto_bal
    rw [hnext_from_split, hnext_to_split, hprev_from_split, hprev_to_split,
      hrem, hfrom_default, hto_default]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem compose_transfer_preserves_sum_of_balances
    {ctx : @ContractCallContext Base}
    {transfers : List (@TransferData Base TokenID)}
    {prev_st next_st : Storage} {token_id : TokenID}
    (h :
      compose_transfers view prev_st next_st transfers
        (fun st1 st2 x p q =>
          transfer_single_spec view st1 st2 x.token_id p q
            ctx.ctx_from x.from_ x.to_ x.amount)) :
    let owners1 := view.get_owners prev_st token_id
    let owners2 := view.get_owners next_st token_id
    sum_balances (view := view) prev_st token_id owners1 =
      sum_balances (view := view) next_st token_id owners2 := by
  intro owners1 owners2
  revert prev_st
  induction transfers with
  | nil =>
      intro prev_st h
      simp [compose_transfers] at h
      subst next_st
      rfl
  | cons transfer transfers ih =>
      intro prev_st h
      simp [compose_transfers] at h
      exact Exists.elim h (fun st h1 => by
        let hrest := h1.2
        rcases h1.1 with ⟨_p, _q, hsingle⟩
        have htail := ih hrest
        by_cases htok : token_id = transfer.token_id
        · subst token_id
          have hsingle_sum :=
            transfer_single_spec_preserves_balances
              (view := view) hsingle
          exact hsingle_sum.symm.trans htail
        · rcases hsingle with
            ⟨_hbal_not_addr, hbal_other_tokens, hids,
              _hauth, _htransfer, _hself_transfer⟩
          have hsingle_other :
              sum_balances (view := view) st token_id
                  (view.get_owners st token_id) =
                sum_balances (view := view) prev_st token_id
                  (view.get_owners prev_st token_id) := by
            apply sum_of_balances_eq_extensional (view := view)
            · exact view.get_owners_no_dup st token_id
            · exact view.get_owners_no_dup prev_st token_id
            · intro addr
              exact same_owners_of_balances (view := view)
                (fun addr => hbal_other_tokens addr token_id htok) addr
            · intro addr _hin
              exact get_balance_opt_default (view := view)
                (hids token_id) (hbal_other_tokens addr token_id htok)
          exact hsingle_other.symm.trans htail)

theorem transfer_preserves_sum_of_balances
    (ctx : @ContractCallContext Base)
    (transfers : List (@TransferData Base TokenID))
    (prev_st next_st : Storage) (ops : List (@ActionBody Base))
    (token_id : TokenID)
    (spec :
      TransferSpec view ctx { transfers := transfers } prev_st next_st ops) :
    let owners1 := view.get_owners prev_st token_id
    let owners2 := view.get_owners next_st token_id
    sum_balances (view := view) prev_st token_id owners1 =
      sum_balances (view := view) next_st token_id owners2 := by
  intro owners1 owners2
  exact compose_transfer_preserves_sum_of_balances
    (view := view) (ctx := ctx) (transfers := transfers)
    (token_id := token_id) spec.transfer_dec_inc

theorem balanceOf_preserves_sum_of_balances
    [Serializable TokenID]
    (params : @BalanceOfParams Base TokenID)
    (prev_st next_st : Storage) (token_id : TokenID)
    (ops : List (@ActionBody Base))
    (spec : BalanceOfSpec view params prev_st next_st ops) :
    let owners1 := view.get_owners prev_st token_id
    let owners2 := view.get_owners next_st token_id
    sum_balances (view := view) next_st token_id owners2 =
      sum_balances (view := view) prev_st token_id owners1 := by
  intro owners1 owners2
  apply sum_of_balances_eq_extensional (view := view)
  · exact view.get_owners_no_dup next_st token_id
  · exact view.get_owners_no_dup prev_st token_id
  · intro addr
    exact same_owners_of_balances (view := view)
      (fun addr => spec.balances_preserved token_id addr) addr
  · intro addr _hin
    exact get_balance_opt_default (view := view)
      (spec.token_ids_preserved token_id)
      (spec.balances_preserved token_id addr)

theorem updateOperator_preserves_sum_of_balances
    (ctx : @ContractCallContext Base)
    (params : @UpdateOperatorParams Base)
    (prev_st next_st : Storage) (token_id : TokenID)
    (ops : List (@ActionBody Base))
    (spec : UpdateOperatorSpec view ctx params prev_st next_st ops) :
    let owners1 := view.get_owners prev_st token_id
    let owners2 := view.get_owners next_st token_id
    sum_balances (view := view) next_st token_id owners2 =
      sum_balances (view := view) prev_st token_id owners1 := by
  intro owners1 owners2
  apply sum_of_balances_eq_extensional (view := view)
  · exact view.get_owners_no_dup next_st token_id
  · exact view.get_owners_no_dup prev_st token_id
  · intro addr
    exact same_owners_of_balances (view := view)
      (fun addr => (spec.balances_preserved addr token_id).symm) addr
  · intro addr _hin
    exact get_balance_opt_default (view := view)
      (spec.token_ids_preserved token_id)
      (spec.balances_preserved addr token_id).symm

end Balances

end Spec

end ConCert.Examples.CIS1
