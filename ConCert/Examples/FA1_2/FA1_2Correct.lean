/- Local functional-correctness lemmas for examples/fa1_2/FA1_2Correct.v. -/

import ConCert.Examples.FA1_2.FA1_2
import ConCert.Execution.BlockchainInduction
import Mathlib.Tactic.Linarith

namespace ConCert.Examples.FA1_2

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.Containers
open ConCert.Execution.ContractCommon
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Utils.Extras

variable [Base : ChainBase]

private theorem without_actions_ok_acts
    {T E : Type} {r : Result T E} {new_state : T}
    {new_acts : List (@ActionBody Base)}
    (h : without_actions (Base := Base) r = .Ok (new_state, new_acts)) :
    new_acts = [] := by
  cases r with
  | Ok st =>
      simp [without_actions] at h
      exact h.2
  | Err e =>
      simp [without_actions] at h

private theorem without_actions_ok_state
    {T E : Type} {r : Result T E} {new_state : T}
    {new_acts : List (@ActionBody Base)}
    (h : without_actions (Base := Base) r = .Ok (new_state, new_acts)) :
    r = .Ok new_state := by
  cases r with
  | Ok st =>
      simp [without_actions] at h
      cases h.1
      rfl
  | Err e =>
      simp [without_actions] at h

omit Base in
private theorem with_default_maybe (n : Nat) :
    with_default 0 (maybe n) = n := by
  unfold maybe
  by_cases hzero : n = 0
  · simp [hzero, with_default, withDefault]
  · simp [hzero, with_default, withDefault]

omit Base in
private theorem maybe_some_pos {m n : Nat} (h : maybe m = some n) :
    0 < n := by
  unfold maybe at h
  by_cases hzero : m = 0
  · simp [hzero] at h
  · have hne : (m == 0) = false := by simp [hzero]
    simp [hne] at h
    cases h
    exact Nat.pos_of_ne_zero hzero

theorem contract_not_payable
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    ctx.ctx_amount ≤ 0 := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · exact le_of_not_gt hpos

theorem contract_not_payable'
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (msg : Option Msg)
    (hpos : 0 < ctx.ctx_amount) :
    receive chain ctx prev_state msg = .Err default_error := by
  simp [receive, non_zero_amount, hpos]

theorem default_entrypoint_none
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) :
    receive chain ctx prev_state none = .Err default_error := by
  by_cases hpos : 0 < ctx.ctx_amount <;>
    simp [receive, non_zero_amount, hpos, default_error]

private theorem receive_transfer_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts)) :
    try_transfer ctx.ctx_from param prev_state = .Ok new_state ∧
      new_acts = [] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  have hnot : ¬ 0 < ctx.ctx_amount := hpos
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact ⟨without_actions_ok_state (Base := Base) h,
    without_actions_ok_acts (Base := Base) h⟩

private theorem receive_approve_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {param : @ApproveParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve param)) =
      .Ok (new_state, new_acts)) :
    try_approve ctx.ctx_from param prev_state = .Ok new_state ∧
      new_acts = [] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  have hnot : ¬ 0 < ctx.ctx_amount := hpos
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact ⟨without_actions_ok_state (Base := Base) h,
    without_actions_ok_acts (Base := Base) h⟩

theorem try_transfer_preserves_total_supply_direct
    {sender : Base.Address} {param : @TransferParam Base}
    {prev_state new_state : @State Base}
    (h : try_transfer sender param prev_state = .Ok new_state) :
    new_state.total_supply = prev_state.total_supply := by
  unfold try_transfer at h
  by_cases hsender : Base.address_eqb sender param.from_
  · simp [hsender] at h
    by_cases hbal :
        Utils.Extras.with_default 0
          (AddressMap.find param.from_ prev_state.tokens) < param.value
    · simp [hbal] at h
    · simp [hbal] at h
      rw [← h]
  · simp [hsender] at h
    by_cases hall :
        Utils.Extras.with_default 0
          (find_allowance (param.from_, sender) prev_state.allowances) < param.value
    · simp [hall] at h
    · simp [hall] at h
      by_cases hbal :
          Utils.Extras.with_default 0
            (AddressMap.find param.from_ prev_state.tokens) < param.value
      · simp [hbal] at h
      · simp [hbal] at h
        rw [← h]

theorem try_approve_preserves_total_supply_direct
    {sender : Base.Address} {param : @ApproveParam Base}
    {prev_state new_state : @State Base}
    (h : try_approve sender param prev_state = .Ok new_state) :
    new_state.total_supply = prev_state.total_supply := by
  unfold try_approve at h
  dsimp at h
  split at h <;> simp_all
  rw [← h]

theorem try_approve_preserves_balances_direct
    {sender : Base.Address} {param : @ApproveParam Base}
    {prev_state new_state : @State Base}
    (h : try_approve sender param prev_state = .Ok new_state) :
    new_state.tokens = prev_state.tokens := by
  unfold try_approve at h
  dsimp at h
  split at h <;> simp_all
  rw [← h]

omit Base in
private theorem list_sum_of_perm {xs ys : List Nat} (h : xs.Perm ys) :
    xs.sum = ys.sum := by
  simpa [List.sum_eq_foldr] using
    (h.foldr_eq (f := fun x acc => x + acc) 0)

def fmap_nat_sum (m : FMap Base.Address Nat) : Nat :=
  ((FMap.elements m).map (fun p : Base.Address × Nat => p.2)).sum

theorem sum_balances_eq_fmap_nat_sum (state : @State Base) :
    sum_balances state = fmap_nat_sum state.tokens := rfl

theorem fmap_nat_sum_add_new
    (k : Base.Address) (v : Nat) (m : FMap Base.Address Nat)
    (hfind : FMap.find k m = none) :
    fmap_nat_sum (FMap.add k v m) = v + fmap_nat_sum m := by
  have hperm :=
    (FMap.elements_add k v m hfind).map
      (fun p : Base.Address × Nat => p.2)
  simpa [fmap_nat_sum] using list_sum_of_perm hperm

theorem fmap_nat_sum_add_existing
    (k : Base.Address) (old new : Nat) (m : FMap Base.Address Nat)
    (hfind : FMap.find k m = some old) :
    fmap_nat_sum (FMap.add k new m) = fmap_nat_sum m - old + new := by
  have hnew :=
    list_sum_of_perm
      ((FMap.elements_add_existing k old new m hfind).map
        (fun p : Base.Address × Nat => p.2))
  have holdPerm := FMap.elements_add_existing k old old m hfind
  rw [FMap.add_id k old m hfind] at holdPerm
  have hold :=
    list_sum_of_perm
      (holdPerm.map (fun p : Base.Address × Nat => p.2))
  unfold fmap_nat_sum
  rw [hnew, hold]
  simp only [List.map_cons, List.sum_cons]
  omega

theorem fmap_nat_sum_add
    (k : Base.Address) (new : Nat) (m : FMap Base.Address Nat) :
    fmap_nat_sum (FMap.add k new m) =
      fmap_nat_sum m - with_default 0 (FMap.find k m) + new := by
  cases hfind : FMap.find k m with
  | none =>
      rw [fmap_nat_sum_add_new k new m hfind]
      simp [with_default, withDefault]
      omega
  | some old =>
      rw [fmap_nat_sum_add_existing k old new m hfind]
      simp [with_default, withDefault]

omit Base in
private theorem nat_le_sum_of_mem :
    ∀ {xs : List Nat} {x : Nat}, x ∈ xs → x ≤ xs.sum
  | [], _, h => by cases h
  | y :: ys, x, h => by
      simp only [List.mem_cons] at h
      simp only [List.sum_cons]
      rcases h with rfl | hmem
      · omega
      · have ih := nat_le_sum_of_mem (xs := ys) hmem
        omega

theorem fmap_nat_sum_find_le
    (k : Base.Address) (m : FMap Base.Address Nat) :
    with_default 0 (FMap.find k m) ≤ fmap_nat_sum m := by
  cases hfind : FMap.find k m with
  | none =>
      exact Nat.zero_le _
  | some old =>
      have hmem_pair : (k, old) ∈ FMap.elements m :=
        (FMap.In_elements k old m).mpr hfind
      have hmem :
          old ∈ (FMap.elements m).map
              (fun p : Base.Address × Nat => p.2) := by
        exact List.mem_map.mpr ⟨(k, old), hmem_pair, rfl⟩
      simpa [fmap_nat_sum, with_default, withDefault] using
        nat_le_sum_of_mem hmem

theorem balance_le_sum_balances
    (addr : Base.Address) (state : @State Base) :
    with_default 0 (FMap.find addr state.tokens) ≤ sum_balances state := by
  simpa [sum_balances, fmap_nat_sum] using
    fmap_nat_sum_find_le (Base := Base) addr state.tokens

theorem fmap_nat_sum_remove_existing
    (k : Base.Address) (old : Nat) (m : FMap Base.Address Nat)
    (hfind : FMap.find k m = some old) :
    fmap_nat_sum (FMap.remove k m) = fmap_nat_sum m - old := by
  have hperm :=
    list_sum_of_perm
      ((FMap.elements_add_existing k old 0 m hfind).map
        (fun p : Base.Address × Nat => p.2))
  have hadd := fmap_nat_sum_add_existing k old 0 m hfind
  have hremove :
      fmap_nat_sum (FMap.add k 0 m) =
        fmap_nat_sum (FMap.remove k m) := by
    simpa [fmap_nat_sum] using hperm
  rw [← hremove, hadd]
  omega

theorem fmap_nat_sum_remove
    (k : Base.Address) (m : FMap Base.Address Nat) :
    fmap_nat_sum (FMap.remove k m) =
      fmap_nat_sum m - with_default 0 (FMap.find k m) := by
  cases hfind : FMap.find k m with
  | none =>
      have hremove : FMap.remove k m = m := by
        apply Std.ExtTreeMap.ext_getElem?
        intro x
        by_cases hx : k = x
        · subst hx
          simpa [FMap.remove, FMap.find, FMap.lookup] using hfind
        · have hne : compare k x ≠ Ordering.eq := by
            intro hcmp
            exact hx (Std.LawfulEqCmp.eq_of_compare hcmp)
          simp [FMap.remove, Std.ExtTreeMap.getElem?_erase, hne]
      have hsum : fmap_nat_sum (FMap.remove k m) = fmap_nat_sum m := by
        rw [hremove]
      rw [hsum]
      simp [with_default, withDefault]
  | some old =>
      rw [fmap_nat_sum_remove_existing k old m hfind]
      simp [with_default, withDefault]

theorem fmap_nat_sum_update_maybe
    (k : Base.Address) (new : Nat) (m : FMap Base.Address Nat) :
    fmap_nat_sum (FMap.update k (maybe new) m) =
      fmap_nat_sum m - with_default 0 (FMap.find k m) + new := by
  unfold FMap.update maybe
  by_cases hzero : new = 0
  · simp [hzero, fmap_nat_sum_remove]
  · simp [hzero, fmap_nat_sum_add]

def transfer_balance_update_correct
    (old_state new_state : @State Base)
    (from_ to_ : Base.Address) (amount : Nat) : Bool :=
  let get_balance_ addr state := with_default 0 (FMap.find addr state.tokens)
  let from_balance_before := get_balance_ from_ old_state
  let to_balance_before := get_balance_ to_ old_state
  let from_balance_after := get_balance_ from_ new_state
  let to_balance_after := get_balance_ to_ new_state
  if Base.address_eqb from_ to_ then
    (from_balance_before == from_balance_after) &&
      (to_balance_before == to_balance_after)
  else
    (from_balance_before == from_balance_after + amount) &&
      (to_balance_before + amount == to_balance_after)

def transfer_allowances_update_correct
    (old_state new_state : @State Base)
    (sender from_ : Base.Address) (amount : Nat) : Bool :=
  let get_allowance_ addr1 addr2 state :=
    with_default 0 (FMap.find (addr1, addr2) state.allowances)
  let allowance_before := get_allowance_ from_ sender old_state
  let allowance_after := get_allowance_ from_ sender new_state
  if Base.address_eqb sender from_ then
    allowance_before == allowance_after
  else
    allowance_before == allowance_after + amount

private theorem try_transfer_tokens_shape
    {sender : Base.Address} {param : @TransferParam Base}
    {prev_state new_state : @State Base}
    (h : try_transfer sender param prev_state = .Ok new_state) :
    let from_balance :=
      with_default 0 (AddressMap.find param.from_ prev_state.tokens)
    let tokens_from :=
      AddressMap.update param.from_ (maybe (from_balance - param.value))
        prev_state.tokens
    let to_balance := with_default 0 (AddressMap.find param.to_ tokens_from)
    param.value ≤ from_balance ∧
      new_state.tokens =
        AddressMap.update param.to_ (maybe (to_balance + param.value))
          tokens_from := by
  unfold try_transfer at h
  by_cases hsender : Base.address_eqb sender param.from_ = true
  · simp [hsender] at h
    by_cases hbal :
        with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
          param.value
    · simp [hbal] at h
    · simp [hbal] at h
      cases h
      exact ⟨le_of_not_gt hbal, rfl⟩
  · simp [hsender] at h
    by_cases hallow :
        with_default 0
            (find_allowance (param.from_, sender) prev_state.allowances) <
          param.value
    · simp [hallow] at h
    · simp [hallow] at h
      by_cases hbal :
          with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
            param.value
      · simp [hbal] at h
      · simp [hbal] at h
        cases h
        exact ⟨le_of_not_gt hbal, rfl⟩

theorem try_transfer_preserves_balances_sum_direct
    {sender : Base.Address} {param : @TransferParam Base}
    {prev_state new_state : @State Base}
    (h : try_transfer sender param prev_state = .Ok new_state) :
    sum_balances prev_state = sum_balances new_state := by
  rcases try_transfer_tokens_shape (Base := Base) h with
    ⟨hbalance, htokens⟩
  unfold sum_balances
  let from_balance :=
    with_default 0 (AddressMap.find param.from_ prev_state.tokens)
  let tokens_from :=
    AddressMap.update param.from_ (maybe (from_balance - param.value))
      prev_state.tokens
  let to_balance := with_default 0 (AddressMap.find param.to_ tokens_from)
  change
    fmap_nat_sum prev_state.tokens =
      fmap_nat_sum new_state.tokens
  rw [htokens]
  change
    fmap_nat_sum prev_state.tokens =
      fmap_nat_sum
        (AddressMap.update param.to_ (maybe (to_balance + param.value))
          tokens_from)
  unfold AddressMap.update
  rw [fmap_nat_sum_update_maybe]
  have hto_le := fmap_nat_sum_find_le (Base := Base) param.to_ tokens_from
  have hto_le' : to_balance ≤ fmap_nat_sum tokens_from := by
    simpa [to_balance, AddressMap.find] using hto_le
  change
    fmap_nat_sum prev_state.tokens =
      fmap_nat_sum tokens_from - to_balance + (to_balance + param.value)
  rw [← Nat.add_assoc]
  rw [Nat.sub_add_cancel hto_le']
  unfold tokens_from AddressMap.update
  rw [fmap_nat_sum_update_maybe]
  have hfrom_le :=
    fmap_nat_sum_find_le (Base := Base) param.from_ prev_state.tokens
  have hfrom_le' : from_balance ≤ fmap_nat_sum prev_state.tokens := by
    simpa [from_balance, AddressMap.find] using hfrom_le
  have hbalance' : param.value ≤ from_balance := by
    simpa [from_balance, AddressMap.find] using hbalance
  change
    fmap_nat_sum prev_state.tokens =
      fmap_nat_sum prev_state.tokens - from_balance +
        (from_balance - param.value) + param.value
  rw [Nat.add_assoc]
  rw [Nat.sub_add_cancel hbalance']
  rw [Nat.sub_add_cancel hfrom_le']

theorem try_transfer_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @TransferParam Base}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts)) :
    new_acts = [] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · exact without_actions_ok_acts (Base := Base)
      (by simpa [receive, non_zero_amount, hpos] using h)

theorem try_transfer_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @TransferParam Base}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts)) :
    new_state.total_supply = prev_state.total_supply := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · unfold receive at h
    simp [non_zero_amount, hpos] at h
    cases hTransfer : try_transfer ctx.ctx_from param prev_state with
    | Err e =>
        simp [hTransfer, without_actions] at h
    | Ok st =>
        simp [hTransfer, without_actions] at h
        have hstate : st = new_state := h.1
        subst new_state
        exact try_transfer_preserves_total_supply_direct hTransfer

theorem try_transfer_preserves_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @TransferParam Base}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state = sum_balances new_state := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · unfold receive at h
    simp [non_zero_amount, hpos] at h
    cases hTransfer : try_transfer ctx.ctx_from param prev_state with
    | Err e =>
        simp [hTransfer, without_actions] at h
    | Ok st =>
        simp [hTransfer, without_actions] at h
        have hstate : st = new_state := h.1
        subst new_state
        exact try_transfer_preserves_balances_sum_direct hTransfer

theorem try_transfer_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts)) :
    transfer_balance_update_correct prev_state new_state
      param.from_ param.to_ param.value = true := by
  rcases receive_transfer_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_transfer_tokens_shape (Base := Base) hraw with
    ⟨hbalance, htokens⟩
  unfold transfer_balance_update_correct
  simp only
  rw [htokens]
  by_cases hftb : Base.address_eqb param.from_ param.to_ = true
  · have hft := (Base.address_eqb_spec param.from_ param.to_).mp hftb
    have hsame : Base.address_eqb param.to_ param.to_ = true :=
      (Base.address_eqb_spec _ _).mpr rfl
    simpa [hftb, hft, hsame, AddressMap.find, AddressMap.update,
      FMap.find_update_eq, with_default_maybe] using
      (Nat.sub_add_cancel hbalance).symm
  · have hft : param.from_ ≠ param.to_ := by
      intro heq
      exact hftb ((Base.address_eqb_spec param.from_ param.to_).mpr heq)
    simpa [hftb, AddressMap.find, AddressMap.update,
      FMap.find_update_ne param.from_ param.to_ _ _ hft,
      FMap.find_update_ne param.to_ param.from_ _ _ (Ne.symm hft),
      FMap.find_update_eq, with_default_maybe] using
      (Nat.sub_add_cancel hbalance).symm

theorem try_transfer_allowance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts)) :
    transfer_allowances_update_correct prev_state new_state
      ctx.ctx_from param.from_ param.value = true := by
  rcases receive_transfer_ok (Base := Base) h with ⟨hraw, _⟩
  unfold try_transfer at hraw
  by_cases hsender : Base.address_eqb ctx.ctx_from param.from_ = true
  · simp [hsender] at hraw
    by_cases hbal :
        with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
          param.value
    · simp [hbal] at hraw
    · simp [hbal] at hraw
      cases hraw
      simp [transfer_allowances_update_correct, hsender]
  · simp [hsender] at hraw
    by_cases hallow :
        with_default 0
            (find_allowance (param.from_, ctx.ctx_from)
              prev_state.allowances) <
          param.value
    · simp [hallow] at hraw
    · simp [hallow] at hraw
      by_cases hbal :
          with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
            param.value
      · simp [hbal] at hraw
      · simp [hbal] at hraw
        cases hraw
        have hle :
            param.value ≤
              with_default 0
                (find_allowance (param.from_, ctx.ctx_from)
                  prev_state.allowances) := le_of_not_gt hallow
        have hsub :
            with_default 0
                (maybe
                  (with_default 0
                      (find_allowance (param.from_, ctx.ctx_from)
                        prev_state.allowances) -
                    param.value)) +
              param.value =
              with_default 0
                (find_allowance (param.from_, ctx.ctx_from)
                  prev_state.allowances) := by
          rw [with_default_maybe]
          exact Nat.sub_add_cancel hle
        simpa [transfer_allowances_update_correct, hsender, update_allowance,
          find_allowance, FMap.find_update_eq] using hsub.symm

theorem try_transfer_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base} {account : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts))
    (h_from : account ≠ param.from_) (h_to : account ≠ param.to_) :
    FMap.find account prev_state.tokens =
      FMap.find account new_state.tokens := by
  rcases receive_transfer_ok (Base := Base) h with ⟨hraw, _⟩
  unfold try_transfer at hraw
  by_cases hsender : Base.address_eqb ctx.ctx_from param.from_ = true
  · simp [hsender] at hraw
    by_cases hbal :
        with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
          param.value
    · simp [hbal] at hraw
    · simp [hbal] at hraw
      cases hraw
      simp [AddressMap.update,
        FMap.find_update_ne account param.to_ _ _ h_to,
        FMap.find_update_ne account param.from_ _ _ h_from]
  · simp [hsender] at hraw
    by_cases hallow :
        with_default 0
            (find_allowance (param.from_, ctx.ctx_from)
              prev_state.allowances) <
          param.value
    · simp [hallow] at hraw
    · simp [hallow] at hraw
      by_cases hbal :
          with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
            param.value
      · simp [hbal] at hraw
      · simp [hbal] at hraw
        cases hraw
        simp [AddressMap.update,
          FMap.find_update_ne account param.to_ _ _ h_to,
          FMap.find_update_ne account param.from_ _ _ h_from]

theorem try_transfer_preserves_other_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base}
    {allowance_key : Base.Address × Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts))
    (h_key : allowance_key ≠ (param.from_, ctx.ctx_from)) :
    FMap.find allowance_key prev_state.allowances =
      FMap.find allowance_key new_state.allowances := by
  rcases receive_transfer_ok (Base := Base) h with ⟨hraw, _⟩
  unfold try_transfer at hraw
  by_cases hsender : Base.address_eqb ctx.ctx_from param.from_ = true
  · simp [hsender] at hraw
    by_cases hbal :
        with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
          param.value
    · simp [hbal] at hraw
    · simp [hbal] at hraw
      cases hraw
      rfl
  · simp [hsender] at hraw
    by_cases hallow :
        with_default 0
            (find_allowance (param.from_, ctx.ctx_from)
              prev_state.allowances) <
          param.value
    · simp [hallow] at hraw
    · simp [hallow] at hraw
      by_cases hbal :
          with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
            param.value
      · simp [hbal] at hraw
      · simp [hbal] at hraw
        cases hraw
        simp [update_allowance,
          FMap.find_update_ne allowance_key (param.from_, ctx.ctx_from)
            _ prev_state.allowances h_key]

theorem try_transfer_remove_empty_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h_prev :
      ∀ n,
        FMap.find (param.from_, ctx.ctx_from) prev_state.allowances =
          some n →
        0 < n)
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts))
    {n : Nat}
    (h_find :
      FMap.find (param.from_, ctx.ctx_from) new_state.allowances =
        some n) :
    0 < n := by
  rcases receive_transfer_ok (Base := Base) h with ⟨hraw, _⟩
  unfold try_transfer at hraw
  by_cases hsender : Base.address_eqb ctx.ctx_from param.from_ = true
  · simp [hsender] at hraw
    by_cases hbal :
        with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
          param.value
    · simp [hbal] at hraw
    · simp [hbal] at hraw
      cases hraw
      exact h_prev n h_find
  · simp [hsender] at hraw
    by_cases hallow :
        with_default 0
            (find_allowance (param.from_, ctx.ctx_from)
              prev_state.allowances) <
          param.value
    · simp [hallow] at hraw
    · simp [hallow] at hraw
      by_cases hbal :
          with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
            param.value
      · simp [hbal] at hraw
      · simp [hbal] at hraw
        cases hraw
        simp [update_allowance, FMap.find_update_eq] at h_find
        rcases maybe_cases
            (with_default 0
                (find_allowance (param.from_, ctx.ctx_from)
                  prev_state.allowances) -
              param.value) with hnone | hsome
        · rcases hnone with ⟨hnone, _⟩
          simp [hnone] at h_find
        · rcases hsome with ⟨hsome, hpos⟩
          simp [hsome] at h_find
          cases h_find
          exact hpos

theorem try_transfer_remove_empty_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer param)) =
      .Ok (new_state, new_acts))
    (n : Nat) :
    (FMap.find param.from_ new_state.tokens = some n → 0 < n) ∧
      (FMap.find param.to_ new_state.tokens = some n → 0 < n) := by
  rcases receive_transfer_ok (Base := Base) h with ⟨hraw, _⟩
  unfold try_transfer at hraw
  by_cases hsender : Base.address_eqb ctx.ctx_from param.from_ = true
  · simp [hsender] at hraw
    by_cases hbal :
        with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
          param.value
    · simp [hbal] at hraw
    · simp [hbal] at hraw
      cases hraw
      constructor
      · intro h_find
        by_cases hft : param.from_ = param.to_
        · simp [AddressMap.update, hft, FMap.find_update_eq] at h_find
          exact maybe_some_pos h_find
        · simp [AddressMap.update,
            FMap.find_update_ne param.from_ param.to_ _ _ hft,
            FMap.find_update_eq] at h_find
          exact maybe_some_pos h_find
      · intro h_find
        simp [AddressMap.update, FMap.find_update_eq] at h_find
        exact maybe_some_pos h_find
  · simp [hsender] at hraw
    by_cases hallow :
        with_default 0
            (find_allowance (param.from_, ctx.ctx_from)
              prev_state.allowances) <
          param.value
    · simp [hallow] at hraw
    · simp [hallow] at hraw
      by_cases hbal :
          with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
            param.value
      · simp [hbal] at hraw
      · simp [hbal] at hraw
        cases hraw
        constructor
        · intro h_find
          by_cases hft : param.from_ = param.to_
          · simp [AddressMap.update, hft, FMap.find_update_eq] at h_find
            exact maybe_some_pos h_find
          · simp [AddressMap.update,
              FMap.find_update_ne param.from_ param.to_ _ _ hft,
              FMap.find_update_eq] at h_find
            exact maybe_some_pos h_find
        · intro h_find
          simp [AddressMap.update, FMap.find_update_eq] at h_find
          exact maybe_some_pos h_find

theorem try_transfer_is_some
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @TransferParam Base) :
    (ctx.ctx_amount ≤ 0 ∧
        (if Base.address_eqb ctx.ctx_from param.from_ then
          True
        else
          param.value ≤
            with_default 0
              (find_allowance (param.from_, ctx.ctx_from)
                prev_state.allowances)) ∧
        param.value ≤
          with_default 0 (AddressMap.find param.from_ prev_state.tokens)) ↔
      ∃ new_state new_acts,
        receive chain ctx prev_state (some (.transfer param)) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro h
    rcases h with ⟨hamount, hallowance, hbalance⟩
    have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
    let from_balance :=
      with_default 0 (AddressMap.find param.from_ prev_state.tokens)
    let tokens_from :=
      AddressMap.update param.from_ (maybe (from_balance - param.value))
        prev_state.tokens
    let to_balance :=
      with_default 0 (AddressMap.find param.to_ tokens_from)
    let tokens_to :=
      AddressMap.update param.to_ (maybe (to_balance + param.value))
        tokens_from
    by_cases hsender : Base.address_eqb ctx.ctx_from param.from_ = true
    · let new_state :=
        { prev_state with tokens := tokens_to }
      refine ⟨new_state, [], ?_⟩
      have hbalance_not : ¬ from_balance < param.value := not_lt.mpr hbalance
      unfold receive try_transfer
      simp [non_zero_amount, hnot, hsender, from_balance, tokens_from,
        to_balance, tokens_to, new_state, hbalance_not, without_actions]
    · have hallow :
          param.value ≤
            with_default 0
              (find_allowance (param.from_, ctx.ctx_from)
                prev_state.allowances) := by
        simpa [hsender] using hallowance
      let allowances_ :=
        update_allowance (param.from_, ctx.ctx_from)
          (maybe
            (with_default 0
                (find_allowance (param.from_, ctx.ctx_from)
                  prev_state.allowances) -
              param.value))
          prev_state.allowances
      let new_state :=
        { prev_state with tokens := tokens_to, allowances := allowances_ }
      refine ⟨new_state, [], ?_⟩
      have hallow_not :
          ¬ with_default 0
              (find_allowance (param.from_, ctx.ctx_from)
                prev_state.allowances) <
            param.value := not_lt.mpr hallow
      have hbalance_not : ¬ from_balance < param.value := not_lt.mpr hbalance
      unfold receive try_transfer
      simp [non_zero_amount, hnot, hsender, hallow_not, from_balance,
        tokens_from, to_balance, tokens_to, allowances_, new_state,
        hbalance_not, without_actions]
  · rintro ⟨new_state, new_acts, h⟩
    rcases receive_transfer_ok (Base := Base) h with ⟨hraw, _⟩
    constructor
    · exact contract_not_payable (Base := Base) h
    constructor
    · by_cases hsender : Base.address_eqb ctx.ctx_from param.from_ = true
      · simp [hsender]
      · simp [hsender]
        unfold try_transfer at hraw
        simp [hsender] at hraw
        by_cases hallow :
            with_default 0
                (find_allowance (param.from_, ctx.ctx_from)
                  prev_state.allowances) <
              param.value
        · simp [hallow] at hraw
        · exact le_of_not_gt hallow
    · unfold try_transfer at hraw
      by_cases hsender : Base.address_eqb ctx.ctx_from param.from_ = true
      · simp [hsender] at hraw
        by_cases hbalance :
            with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
              param.value
        · simp [hbalance] at hraw
        · exact le_of_not_gt hbalance
      · simp [hsender] at hraw
        by_cases hallow :
            with_default 0
                (find_allowance (param.from_, ctx.ctx_from)
                  prev_state.allowances) <
              param.value
        · simp [hallow] at hraw
        · simp [hallow] at hraw
          by_cases hbalance :
              with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
                param.value
          · simp [hbalance] at hraw
          · exact le_of_not_gt hbalance

theorem try_approve_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @ApproveParam Base}
    (h : receive chain ctx prev_state (some (.approve param)) =
      .Ok (new_state, new_acts)) :
    new_acts = [] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · exact without_actions_ok_acts (Base := Base)
      (by simpa [receive, non_zero_amount, hpos] using h)

theorem try_approve_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @ApproveParam Base}
    (h : receive chain ctx prev_state (some (.approve param)) =
      .Ok (new_state, new_acts)) :
    new_state.total_supply = prev_state.total_supply := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · unfold receive at h
    simp [non_zero_amount, hpos] at h
    cases hApprove : try_approve ctx.ctx_from param prev_state with
    | Err e =>
        simp [hApprove, without_actions] at h
    | Ok st =>
        simp [hApprove, without_actions] at h
        have hstate : st = new_state := h.1
        subst new_state
        exact try_approve_preserves_total_supply_direct hApprove

theorem try_approve_preserves_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @ApproveParam Base}
    (h : receive chain ctx prev_state (some (.approve param)) =
      .Ok (new_state, new_acts)) :
    new_state.tokens = prev_state.tokens := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · unfold receive at h
    simp [non_zero_amount, hpos] at h
    cases hApprove : try_approve ctx.ctx_from param prev_state with
    | Err e =>
        simp [hApprove, without_actions] at h
    | Ok st =>
        simp [hApprove, without_actions] at h
        have hstate : st = new_state := h.1
        subst new_state
        exact try_approve_preserves_balances_direct hApprove

theorem try_approve_preserves_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @ApproveParam Base}
    (h : receive chain ctx prev_state (some (.approve param)) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state = sum_balances new_state := by
  unfold sum_balances
  rw [try_approve_preserves_balances h]

theorem try_approve_allowance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @ApproveParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve param)) =
      .Ok (new_state, new_acts)) :
    FMap.find (ctx.ctx_from, param.spender) new_state.allowances =
      maybe param.value_ := by
  rcases receive_approve_ok (Base := Base) h with ⟨hraw, _⟩
  unfold try_approve at hraw
  by_cases hbad :
      (decide
          (0 <
            with_default 0
              (find_allowance (ctx.ctx_from, param.spender)
                prev_state.allowances)) &&
        decide (0 < param.value_)) = true
  · simp [hbad] at hraw
  · simp [hbad] at hraw
    cases hraw
    simp [update_allowance, FMap.find_update_eq]

theorem try_approve_preserves_other_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @ApproveParam Base} {allowance_key : Base.Address × Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve param)) =
      .Ok (new_state, new_acts))
    (h_key : allowance_key ≠ (ctx.ctx_from, param.spender)) :
    FMap.find allowance_key prev_state.allowances =
      FMap.find allowance_key new_state.allowances := by
  rcases receive_approve_ok (Base := Base) h with ⟨hraw, _⟩
  unfold try_approve at hraw
  by_cases hbad :
      (decide
          (0 <
            with_default 0
              (find_allowance (ctx.ctx_from, param.spender)
                prev_state.allowances)) &&
        decide (0 < param.value_)) = true
  · simp [hbad] at hraw
  · simp [hbad] at hraw
    cases hraw
    simp [update_allowance,
      FMap.find_update_ne allowance_key (ctx.ctx_from, param.spender)
        _ prev_state.allowances h_key]

theorem try_approve_remove_empty_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @ApproveParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve param)) =
      .Ok (new_state, new_acts))
    {n : Nat}
    (hfind :
      FMap.find (ctx.ctx_from, param.spender) new_state.allowances =
        some n) :
    0 < n := by
  rw [try_approve_allowance_correct (Base := Base) h] at hfind
  exact maybe_some_pos hfind

theorem try_approve_is_some
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @ApproveParam Base) :
    (ctx.ctx_amount ≤ 0 ∧
        (with_default 0
            (find_allowance (ctx.ctx_from, param.spender)
              prev_state.allowances) = 0 ∨
          param.value_ = 0)) ↔
      ∃ new_state new_acts,
        receive chain ctx prev_state (some (.approve param)) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro h
    rcases h with ⟨hamount, hvalid⟩
    let allowance_key := (ctx.ctx_from, param.spender)
    let previous_value :=
      with_default 0 (find_allowance allowance_key prev_state.allowances)
    let new_state :=
      { prev_state with
        allowances :=
          update_allowance allowance_key (maybe param.value_)
            prev_state.allowances }
    refine ⟨new_state, [], ?_⟩
    have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
    have hbad :
        (decide (0 < previous_value) && decide (0 < param.value_)) =
      false := by
      rcases hvalid with hprev_zero | hval_zero
      · have hprev_not : ¬ 0 < previous_value := by
          simp [previous_value, allowance_key, hprev_zero]
        simp [hprev_not]
      · simp [hval_zero]
    unfold receive try_approve
    simp [non_zero_amount, hnot, allowance_key, previous_value, new_state,
      hbad, without_actions]
  · rintro ⟨new_state, new_acts, h⟩
    constructor
    · exact contract_not_payable (Base := Base) h
    · rcases receive_approve_ok (Base := Base) h with ⟨hraw, _⟩
      unfold try_approve at hraw
      by_cases hprev :
          with_default 0
              (find_allowance (ctx.ctx_from, param.spender)
                prev_state.allowances) =
            0
      · exact Or.inl hprev
      · by_cases hval : param.value_ = 0
        · exact Or.inr hval
        · have hbad :
            (decide
                (0 <
                  with_default 0
                    (find_allowance (ctx.ctx_from, param.spender)
                      prev_state.allowances)) &&
              decide (0 < param.value_)) = true := by
            have hprev_pos :
                0 <
                  with_default 0
                    (find_allowance (ctx.ctx_from, param.spender)
                      prev_state.allowances) := Nat.pos_of_ne_zero hprev
            have hval_pos : 0 < param.value_ := Nat.pos_of_ne_zero hval
            simp [hprev_pos, hval_pos]
          simp [hbad] at hraw

theorem try_get_allowance_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @GetAllowanceParam Base}
    (h : receive chain ctx prev_state (some (.getAllowance param)) =
      .Ok (new_state, new_acts)) :
    new_acts =
      [ .act_call param.allowance_callback.return_addr 0
          (serialize (receive_allowance_
            (get_allowance param.request.1 param.request.2 prev_state))) ] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · simp [receive, non_zero_amount, hpos, try_get_allowance, mk_callback,
      receive_allowance_, find_allowance] at h
    simpa [receive_allowance_, get_allowance, find_allowance] using h.2.symm

theorem try_get_allowance_preserves_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @GetAllowanceParam Base}
    (h : receive chain ctx prev_state (some (.getAllowance param)) =
      .Ok (new_state, new_acts)) :
    prev_state = new_state := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · simp [receive, non_zero_amount, hpos, try_get_allowance] at h
    exact h.1

theorem try_get_balance_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @GetBalanceParam Base}
    (h : receive chain ctx prev_state (some (.getBalance param)) =
      .Ok (new_state, new_acts)) :
    new_acts =
      [ .act_call param.balance_callback.return_addr 0
          (serialize (receive_balance_of_ (get_balance param.owner_ prev_state))) ] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · simp [receive, non_zero_amount, hpos, try_get_balance, mk_callback,
      receive_balance_of_] at h
    simpa [receive_balance_of_, get_balance] using h.2.symm

theorem try_get_balance_preserves_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @GetBalanceParam Base}
    (h : receive chain ctx prev_state (some (.getBalance param)) =
      .Ok (new_state, new_acts)) :
    prev_state = new_state := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · simp [receive, non_zero_amount, hpos, try_get_balance] at h
    exact h.1

theorem try_get_total_supply_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @GetTotalSupplyParam Base}
    (h : receive chain ctx prev_state (some (.getTotalSupply param)) =
      .Ok (new_state, new_acts)) :
    new_acts =
      [ .act_call param.supply_callback.return_addr 0
          (serialize (receive_total_supply_ prev_state.total_supply)) ] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · simp [receive, non_zero_amount, hpos, try_get_total_supply, mk_callback,
      receive_total_supply_] at h
    simpa [receive_total_supply_] using h.2.symm

theorem try_get_total_supply_preserves_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {new_acts : List (@ActionBody Base)}
    {param : @GetTotalSupplyParam Base}
    (h : receive chain ctx prev_state (some (.getTotalSupply param)) =
      .Ok (new_state, new_acts)) :
    prev_state = new_state := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  · simp [receive, non_zero_amount, hpos, try_get_total_supply] at h
    exact h.1

theorem init_balances_correct
    {chain : Chain} {ctx : @ContractCallContext Base} {setup : @Setup Base}
    {state : @State Base}
    (h : init chain ctx setup = .Ok state) :
    state.tokens = FMap.add setup.lqt_provider setup.initial_pool FMap.empty := by
  unfold init at h
  by_cases hpos : non_zero_amount ctx.ctx_amount
  · simp [hpos] at h
  · simp [hpos] at h
    cases h
    rfl

theorem init_allowances_correct
    {chain : Chain} {ctx : @ContractCallContext Base} {setup : @Setup Base}
    {state : @State Base}
    (h : init chain ctx setup = .Ok state) :
    state.allowances = FMap.empty := by
  unfold init at h
  by_cases hpos : non_zero_amount ctx.ctx_amount
  · simp [hpos] at h
  · simp [hpos] at h
    cases h
    rfl

theorem init_total_supply_correct
    {chain : Chain} {ctx : @ContractCallContext Base} {setup : @Setup Base}
    {state : @State Base}
    (h : init chain ctx setup = .Ok state) :
    state.total_supply = setup.initial_pool := by
  unfold init at h
  by_cases hpos : non_zero_amount ctx.ctx_amount
  · simp [hpos] at h
  · simp [hpos] at h
    cases h
    rfl

theorem init_preserves_balances_sum
    {chain : Chain} {ctx : @ContractCallContext Base} {setup : @Setup Base}
    {state : @State Base}
    (h : init chain ctx setup = .Ok state) :
    state.total_supply = sum_balances state := by
  rw [init_total_supply_correct h]
  unfold sum_balances
  rw [init_balances_correct h]
  change
    setup.initial_pool =
      fmap_nat_sum
        (FMap.add setup.lqt_provider setup.initial_pool
          (FMap.empty : FMap Base.Address Nat))
  rw [fmap_nat_sum_add_new]
  · simp [fmap_nat_sum, FMap.elements_empty]
  · exact FMap.find_empty setup.lqt_provider

theorem total_supply_correct
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate) :
    bstate.env_contracts caddr =
      some (contract_to_weak_contract (contract : @Contract Base _ _ _ _ _ _ _ _)) →
    ∃ (cstate : @State Base) (depinfo : @DeploymentInfo Base (@Setup Base)),
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr = some cstate ∧
      deployment_info (@Setup Base) trace caddr = some depinfo ∧
      cstate.total_supply = depinfo.deployment_setup.initial_pool := by
  intro hdeployed
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base (@Setup Base) →
          @State Base → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ dep cstate _ _ _ _ =>
      cstate.total_supply = dep.deployment_setup.initial_pool
  have hcases : ContractInductionCases contract
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True) P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
          cases eval <;> try trivial
          intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _
      exact ih
    · intro chain ctx setup result _ hinit _
      simp [P, contract] at hinit ⊢
      exact init_total_supply_correct hinit
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
      exact ih
    · intro chain ctx _ prev_state msg _ _ _ new_state new_acts
        _ _ ih hreceive _
      simp [P] at ih ⊢
      cases msg with
      | none =>
          simp [contract, receive] at hreceive
      | some msg =>
          cases msg with
          | transfer param =>
              have hp := try_transfer_preserves_total_supply
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              rw [hp]
              exact ih
          | approve param =>
              have hp := try_approve_preserves_total_supply
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              rw [hp]
              exact ih
          | getAllowance param =>
              have hstate := try_get_allowance_preserves_state
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              subst new_state
              exact ih
          | getBalance param =>
              have hstate := try_get_balance_preserves_state
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              subst new_state
              exact ih
          | getTotalSupply param =>
              have hstate := try_get_total_supply_preserves_state
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              subst new_state
              exact ih
    · intro chain ctx _ prev_state msg _ _ _ _ new_state new_acts
        _ _ ih _ hreceive _
      simp [P] at ih ⊢
      cases msg with
      | none =>
          simp [contract, receive] at hreceive
      | some msg =>
          cases msg with
          | transfer param =>
              have hp := try_transfer_preserves_total_supply
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              rw [hp]
              exact ih
          | approve param =>
              have hp := try_approve_preserves_total_supply
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              rw [hp]
              exact ih
          | getAllowance param =>
              have hstate := try_get_allowance_preserves_state
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              subst new_state
              exact ih
          | getBalance param =>
              have hstate := try_get_balance_preserves_state
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              subst new_state
              exact ih
          | getTotalSupply param =>
              have hstate := try_get_total_supply_preserves_state
                (chain := chain) (ctx := ctx) (new_acts := new_acts)
                (param := param) hreceive
              subst new_state
              exact ih
    · intro _ _ _ _ _ _ _ _ _ _ _ ih _ _
      exact ih
  obtain ⟨dep, cstate, _inc_calls, hdep, hstate, _hcalls, hP⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  exact ⟨cstate, dep, hstate, hdep, hP⟩

theorem sum_balances_eq_total_supply
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      cstate.total_supply = sum_balances cstate := by
  let Q : @State Base → Prop :=
    fun state => state.total_supply = sum_balances state
  obtain ⟨cstate, hstate, hQ⟩ :=
    lift_contract_state_prop
      (contract :=
        (contract :
          @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))
      (Q := Q)
      bstate caddr
      (by
        intro chain ctx setup result hinit
        exact init_preserves_balances_sum
          (chain := chain) (ctx := ctx) (setup := setup)
          (state := result) hinit)
      (by
        intro chain ctx cstate msg new_cstate acts hQ hreceive
        simp [Q] at hQ ⊢
        cases msg with
        | none =>
            simp [contract, receive] at hreceive
        | some msg =>
            cases msg with
            | transfer param =>
                have hsum := try_transfer_preserves_balances_sum
                  (chain := chain) (ctx := ctx) (new_acts := acts)
                  (param := param) hreceive
                have htotal := try_transfer_preserves_total_supply
                  (chain := chain) (ctx := ctx) (new_acts := acts)
                  (param := param) hreceive
                rw [htotal, ← hsum]
                exact hQ
            | approve param =>
                have hsum := try_approve_preserves_balances_sum
                  (chain := chain) (ctx := ctx) (new_acts := acts)
                  (param := param) hreceive
                have htotal := try_approve_preserves_total_supply
                  (chain := chain) (ctx := ctx) (new_acts := acts)
                  (param := param) hreceive
                rw [htotal, ← hsum]
                exact hQ
            | getAllowance param =>
                have hstate := try_get_allowance_preserves_state
                  (chain := chain) (ctx := ctx) (new_acts := acts)
                  (param := param) hreceive
                subst new_cstate
                exact hQ
            | getBalance param =>
                have hstate := try_get_balance_preserves_state
                  (chain := chain) (ctx := ctx) (new_acts := acts)
                  (param := param) hreceive
                subst new_cstate
                exact hQ
            | getTotalSupply param =>
                have hstate := try_get_total_supply_preserves_state
                  (chain := chain) (ctx := ctx) (new_acts := acts)
                  (param := param) hreceive
                subst new_cstate
                exact hQ)
      hr hdeployed
  exact ⟨cstate, hstate, hQ⟩

theorem token_balance_le_total_supply
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      ∀ addr,
        with_default 0 (FMap.find addr cstate.tokens) ≤ cstate.total_supply := by
  obtain ⟨cstate, hstate, hsum⟩ :=
    sum_balances_eq_total_supply bstate caddr hr hdeployed
  refine ⟨cstate, hstate, ?_⟩
  intro addr
  rw [hsum]
  exact balance_le_sum_balances (Base := Base) addr cstate

theorem zero_balances_removed
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))) :
    ∃ depinfo cstate,
      deployment_info (@Setup Base) trace caddr = some depinfo ∧
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      (let initial_tokens := depinfo.deployment_setup.initial_pool
       initial_tokens > 0 →
        ∀ addr n, FMap.find addr cstate.tokens = some n → 0 < n) := by
  let Q : @DeploymentInfo Base (@Setup Base) → @State Base → Prop :=
    fun dep cstate =>
      dep.deployment_setup.initial_pool > 0 →
        ∀ addr n, FMap.find addr cstate.tokens = some n → 0 < n
  obtain ⟨dep, cstate, hdep, hstate, hQ⟩ :=
    lift_dep_info_contract_state_prop
      (contract :=
        (contract :
          @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))
      (Q := Q)
      bstate caddr trace
      (by
        intro chain ctx setup result hinit hpositive addr n hfind
        simp [contract] at hinit
        rw [init_balances_correct hinit] at hfind
        by_cases haddr : addr = setup.lqt_provider
        · subst addr
          simp [FMap.find_add] at hfind
          cases hfind
          exact hpositive
        · rw [FMap.find_add_ne setup.lqt_provider addr
              setup.initial_pool FMap.empty (Ne.symm haddr),
            FMap.find_empty] at hfind
          cases hfind)
      (by
        intro chain ctx cstate msg new_cstate acts dep hQ hreceive
          hpositive addr n hfind
        simp [contract] at hreceive
        cases msg with
        | none =>
            simp [receive] at hreceive
        | some msg =>
            cases msg with
            | transfer param =>
                by_cases hfrom : addr = param.from_
                · subst addr
                  exact (try_transfer_remove_empty_balances
                    (Base := Base) hreceive n).1 hfind
                · by_cases hto : addr = param.to_
                  · subst addr
                    exact (try_transfer_remove_empty_balances
                      (Base := Base) hreceive n).2 hfind
                  · have hpres := try_transfer_preserves_other_balances
                      (Base := Base) (account := addr) hreceive hfrom hto
                    exact hQ hpositive addr n (by rw [hpres]; exact hfind)
            | approve param =>
                have htokens := try_approve_preserves_balances
                  (Base := Base) (chain := chain) (ctx := ctx)
                  (new_acts := acts) (param := param) hreceive
                exact hQ hpositive addr n (by rw [← htokens]; exact hfind)
            | getAllowance param =>
                have hstate := try_get_allowance_preserves_state
                  (Base := Base) (chain := chain) (ctx := ctx)
                  (new_acts := acts) (param := param) hreceive
                subst new_cstate
                exact hQ hpositive addr n hfind
            | getBalance param =>
                have hstate := try_get_balance_preserves_state
                  (Base := Base) (chain := chain) (ctx := ctx)
                  (new_acts := acts) (param := param) hreceive
                subst new_cstate
                exact hQ hpositive addr n hfind
            | getTotalSupply param =>
                have hstate := try_get_total_supply_preserves_state
                  (Base := Base) (chain := chain) (ctx := ctx)
                  (new_acts := acts) (param := param) hreceive
                subst new_cstate
                exact hQ hpositive addr n hfind)
      hdeployed
  exact ⟨dep, cstate, hdep, hstate, hQ⟩

theorem zero_allowances_removed
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      ∀ sender from_ n,
        FMap.find (sender, from_) cstate.allowances = some n → 0 < n := by
  let Q : @State Base → Prop :=
    fun cstate =>
      ∀ sender from_ n,
        FMap.find (sender, from_) cstate.allowances = some n → 0 < n
  obtain ⟨cstate, hstate, hQ⟩ :=
    lift_contract_state_prop
      (contract :=
        (contract :
          @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))
      (Q := Q)
      bstate caddr
      (by
        intro chain ctx setup result hinit sender from_ n hfind
        simp [contract] at hinit
        rw [init_allowances_correct hinit] at hfind
        rw [FMap.find_empty] at hfind
        cases hfind)
      (by
        intro chain ctx cstate msg new_cstate acts hQ hreceive sender from_ n hfind
        simp [contract] at hreceive
        cases msg with
        | none =>
            simp [receive] at hreceive
        | some msg =>
            cases msg with
            | transfer param =>
                by_cases hkey : (sender, from_) = (param.from_, ctx.ctx_from)
                · rcases hkey with ⟨rfl, rfl⟩
                  exact try_transfer_remove_empty_allowances
                    (Base := Base)
                    (h_prev := fun n h => hQ param.from_ ctx.ctx_from n h)
                    hreceive hfind
                · have hpres := try_transfer_preserves_other_allowances
                    (Base := Base) (allowance_key := (sender, from_))
                    hreceive hkey
                  exact hQ sender from_ n (by rw [hpres]; exact hfind)
            | approve param =>
                by_cases hkey : (sender, from_) = (ctx.ctx_from, param.spender)
                · rcases hkey with ⟨rfl, rfl⟩
                  exact try_approve_remove_empty_allowances
                    (Base := Base) hreceive hfind
                · have hpres := try_approve_preserves_other_allowances
                    (Base := Base) (allowance_key := (sender, from_))
                    hreceive hkey
                  exact hQ sender from_ n (by rw [hpres]; exact hfind)
            | getAllowance param =>
                have hstate := try_get_allowance_preserves_state
                  (Base := Base) (chain := chain) (ctx := ctx)
                  (new_acts := acts) (param := param) hreceive
                subst new_cstate
                exact hQ sender from_ n hfind
            | getBalance param =>
                have hstate := try_get_balance_preserves_state
                  (Base := Base) (chain := chain) (ctx := ctx)
                  (new_acts := acts) (param := param) hreceive
                subst new_cstate
                exact hQ sender from_ n hfind
            | getTotalSupply param =>
                have hstate := try_get_total_supply_preserves_state
                  (Base := Base) (chain := chain) (ctx := ctx)
                  (new_acts := acts) (param := param) hreceive
                subst new_cstate
                exact hQ sender from_ n hfind)
      hr hdeployed
  exact ⟨cstate, hstate, hQ⟩

end ConCert.Examples.FA1_2
