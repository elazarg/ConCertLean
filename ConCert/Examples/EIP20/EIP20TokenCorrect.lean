/- Local functional-correctness lemmas for examples/eip20/EIP20TokenCorrect.v. -/

import ConCert.Examples.EIP20.EIP20Token
import ConCert.Execution.BlockchainInduction
import ConCert.Utils.Extras
import Mathlib.Tactic.Linarith

namespace ConCert.Examples.EIP20.EIP20Token

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
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

theorem EIP20_not_payable
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    ctx.ctx_amount ≤ 0 := by
  by_cases hamount : ctx.ctx_amount > 0
  · simp [receive, hamount, error] at h
  · exact le_of_not_gt hamount

theorem EIP20_no_acts
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    new_acts = [] := by
  by_cases hamount : ctx.ctx_amount > 0
  · simp [receive, hamount, error] at h
  · cases msg with
    | none =>
        simp [receive, hamount, error] at h
    | some msg =>
        cases msg with
        | transfer to_ amount =>
            exact without_actions_ok_acts (Base := Base)
              (by simpa [receive, hamount, error] using h)
        | transfer_from from_ to_ amount =>
            exact without_actions_ok_acts (Base := Base)
              (by simpa [receive, hamount, error] using h)
        | approve delegate amount =>
            exact without_actions_ok_acts (Base := Base)
              (by simpa [receive, hamount, error] using h)

theorem receive_not_payable
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Msg}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some msg) = .Ok (new_state, new_acts)) :
    (match msg with
     | .transfer to_ amount =>
         without_actions (Base := Base)
           (try_transfer ctx.ctx_from to_ amount prev_state)
     | .transfer_from from_ to_ amount =>
         without_actions (Base := Base)
           (try_transfer_from ctx.ctx_from from_ to_ amount prev_state)
     | .approve delegate amount =>
         without_actions (Base := Base)
           (try_approve ctx.ctx_from delegate amount prev_state)) =
      .Ok (new_state, new_acts) := by
  have hamount : ¬ ctx.ctx_amount > 0 := not_lt.mpr (EIP20_not_payable h)
  cases msg <;> simpa [receive, hamount, without_actions, Result.bind] using h

theorem receive_no_acts
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Msg}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some msg) = .Ok (new_state, new_acts)) :
    receive chain ctx prev_state (some msg) = .Ok (new_state, []) := by
  rw [EIP20_no_acts h] at h
  exact h

theorem default_none
    (prev_state : @State Base) (chain : Chain) (ctx : @ContractCallContext Base) :
    receive chain ctx prev_state none = .Err default_error := by
  by_cases hamount : ctx.ctx_amount > 0 <;>
    simp [receive, hamount, error, default_error]

theorem add_is_partial_alter_plus
    (account : Base.Address) (amount : TokenValue)
    (balances : FMap Base.Address Nat) :
    FMap.partial_alter
        (fun balance : Option Nat => some (with_default 0 balance + amount))
        account balances =
      FMap.add account (with_default 0 (FMap.find account balances) + amount)
        balances := by
  apply FMap.ext_eq
  intro k
  by_cases h : account = k
  · subst k
    rw [FMap.find_partial_alter, FMap.find_add]
  · rw [FMap.find_partial_alter_ne account k _ _ h,
      FMap.find_add_ne account k _ _ h]

theorem increment_balance_is_partial_alter_plus
    (addr : Base.Address) (amount : TokenValue)
    (m : FMap Base.Address Nat) :
    increment_balance m addr amount =
      FMap.partial_alter
        (fun balance : Option Nat => some (with_default 0 balance + amount))
        addr m := by
  unfold increment_balance AddressMap.find AddressMap.add
  rw [add_is_partial_alter_plus]
  cases FMap.find addr m <;> simp [with_default, withDefault]

/-- Upstream Coq kept this misspelling; retain an alias for direct ports. -/
theorem increment_balanace_is_partial_alter_plus
    (addr : Base.Address) (amount : TokenValue)
    (m : FMap Base.Address Nat) :
    increment_balance m addr amount =
      FMap.partial_alter
        (fun balance : Option Nat => some (with_default 0 balance + amount))
        addr m :=
  increment_balance_is_partial_alter_plus addr amount m

def transfer_balance_update_correct
    (old_state new_state : @State Base)
    (from_ to_ : Base.Address) (tokens : TokenValue) : Bool :=
  let get_balance addr state := with_default 0 (FMap.find addr state.balances)
  let from_balance_before := get_balance from_ old_state
  let to_balance_before := get_balance to_ old_state
  let from_balance_after := get_balance from_ new_state
  let to_balance_after := get_balance to_ new_state
  if Base.address_eqb from_ to_ then
    (from_balance_before == from_balance_after) &&
      (to_balance_before == to_balance_after)
  else
    (from_balance_before == from_balance_after + tokens) &&
      (to_balance_before + tokens == to_balance_after)

def transfer_from_allowances_update_correct
    (old_state new_state : @State Base)
    (from_ delegate : Base.Address) (tokens : TokenValue) : Bool :=
  let delegate_allowance_before := get_allowance old_state from_ delegate
  let delegate_allowance_after := get_allowance new_state from_ delegate
  delegate_allowance_before == delegate_allowance_after + tokens

def approve_allowance_update_correct
    (new_state : @State Base)
    (from_ delegate : Base.Address) (tokens : TokenValue) : Bool :=
  let delegate_allowance_after := get_allowance new_state from_ delegate
  delegate_allowance_after == tokens

omit Base in
private theorem list_sum_of_perm {xs ys : List Nat} (h : xs.Perm ys) :
    xs.sum = ys.sum := by
  simpa [List.sum_eq_foldr] using
    (h.foldr_eq (f := fun x acc => x + acc) 0)

def fmap_nat_sum (m : FMap Base.Address Nat) : Nat :=
  ((FMap.elements m).map (fun p : Base.Address × Nat => p.2)).sum

theorem sum_balances_eq_fmap_nat_sum (state : @State Base) :
    sum_balances state = fmap_nat_sum state.balances := rfl

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
    with_default 0 (FMap.find addr state.balances) ≤ sum_balances state := by
  simpa [sum_balances, fmap_nat_sum] using
    fmap_nat_sum_find_le (Base := Base) addr state.balances

theorem fmap_nat_sum_increment_balance
    (m : FMap Base.Address Nat) (addr : Base.Address) (amount : Nat) :
    fmap_nat_sum (increment_balance m addr amount) =
      fmap_nat_sum m + amount := by
  unfold increment_balance AddressMap.find AddressMap.add
  cases hfind : FMap.find addr m with
  | none =>
      rw [fmap_nat_sum_add addr amount m]
      simp [hfind, with_default, withDefault]
  | some old =>
      rw [fmap_nat_sum_add addr (old + amount) m]
      have hle := fmap_nat_sum_find_le (Base := Base) addr m
      simp [hfind, with_default, withDefault] at hle ⊢
      omega

theorem try_transfer_balance_correct_raw
    {from_ to_ : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_transfer from_ to_ amount prev_state = .Ok new_state) :
    transfer_balance_update_correct prev_state new_state from_ to_ amount = true := by
  unfold try_transfer at h
  by_cases hlt :
      with_default 0 (AddressMap.find from_ prev_state.balances) < amount
  · simp [hlt, error] at h
  · have henough :
        amount ≤ with_default 0 (AddressMap.find from_ prev_state.balances) :=
      Nat.le_of_not_gt hlt
    simp [hlt] at h
    cases h
    unfold transfer_balance_update_correct
    cases haddr : Base.address_eqb from_ to_
    · have hne : from_ ≠ to_ := by
        intro heq
        subst to_
        simp [Address.address_eq_refl] at haddr
      simp [AddressMap.add, AddressMap.find,
        increment_balance_is_partial_alter_plus,
        FMap.find_partial_alter, FMap.find_add,
        FMap.find_partial_alter_ne to_ from_ _ _ (Ne.symm hne),
        FMap.find_add_ne from_ to_ _ _ hne,
        with_default, withDefault]
      exact (Nat.sub_add_cancel (by simpa [AddressMap.find] using henough)).symm
    · have heq : from_ = to_ := (Base.address_eqb_spec from_ to_).mp haddr
      subst to_
      simp [AddressMap.add, AddressMap.find,
        increment_balance_is_partial_alter_plus,
        FMap.find_partial_alter, FMap.find_add,
        with_default, withDefault]
      exact (Nat.sub_add_cancel (by simpa [AddressMap.find] using henough)).symm

theorem try_transfer_from_balance_correct_raw
    {delegate from_ to_ : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_transfer_from delegate from_ to_ amount prev_state = .Ok new_state) :
    transfer_balance_update_correct prev_state new_state from_ to_ amount = true ∧
      transfer_from_allowances_update_correct
        prev_state new_state from_ delegate amount = true := by
  unfold try_transfer_from at h
  cases hFrom : AddressMap.find from_ prev_state.allowances with
  | none =>
      simp [hFrom] at h
  | some from_allowances =>
      cases hDelegate : AddressMap.find delegate from_allowances with
      | none =>
          simp [hFrom, hDelegate] at h
      | some delegate_allowance =>
          let from_balance := with_default 0 (AddressMap.find from_ prev_state.balances)
          cases hBad : ((delegate_allowance < amount) || (from_balance < amount)) with
          | true =>
              simp [hFrom, hDelegate, from_balance, hBad, error] at h
          | false =>
              have hDelegateEnough : amount ≤ delegate_allowance := by
                apply Nat.le_of_not_gt
                intro hlt
                simp [hlt] at hBad
              have hFromEnough :
                  amount ≤ with_default 0 (AddressMap.find from_ prev_state.balances) := by
                apply Nat.le_of_not_gt
                intro hlt
                simp [from_balance, hlt] at hBad
              simp [hFrom, hDelegate, from_balance, hBad] at h
              cases h
              constructor
              · unfold transfer_balance_update_correct
                cases haddr : Base.address_eqb from_ to_
                · have hne : from_ ≠ to_ := by
                    intro heq
                    subst to_
                    simp [Address.address_eq_refl] at haddr
                  simp [AddressMap.add, AddressMap.find,
                    increment_balance_is_partial_alter_plus,
                    FMap.find_partial_alter, FMap.find_add,
                    FMap.find_partial_alter_ne to_ from_ _ _ (Ne.symm hne),
                    FMap.find_add_ne from_ to_ _ _ hne,
                    with_default, withDefault]
                  exact (Nat.sub_add_cancel
                    (by simpa [AddressMap.find] using hFromEnough)).symm
                · have heq : from_ = to_ :=
                    (Base.address_eqb_spec from_ to_).mp haddr
                  subst to_
                  simp [AddressMap.add, AddressMap.find,
                    increment_balance_is_partial_alter_plus,
                    FMap.find_partial_alter, FMap.find_add,
                    with_default, withDefault]
                  exact (Nat.sub_add_cancel
                    (by simpa [AddressMap.find] using hFromEnough)).symm
              · unfold transfer_from_allowances_update_correct
                unfold AddressMap.find at hFrom hDelegate
                simp [get_allowance, AddressMap.add, hFrom, hDelegate,
                  FMap.find_add, with_default, withDefault]
                exact (Nat.sub_add_cancel hDelegateEnough).symm

theorem try_transfer_preserves_balances_sum_raw
    {from_ to_ : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_transfer from_ to_ amount prev_state = .Ok new_state) :
    sum_balances prev_state = sum_balances new_state := by
  unfold try_transfer at h
  by_cases hlt :
      with_default 0 (AddressMap.find from_ prev_state.balances) < amount
  · simp [hlt, error] at h
  · have henough :
        amount ≤ with_default 0 (AddressMap.find from_ prev_state.balances) :=
      Nat.le_of_not_gt hlt
    simp [hlt] at h
    cases h
    unfold sum_balances
    let from_balance :=
      with_default 0 (AddressMap.find from_ prev_state.balances)
    let debited :=
      AddressMap.add from_ (from_balance - amount) prev_state.balances
    change
      fmap_nat_sum prev_state.balances =
        fmap_nat_sum (increment_balance debited to_ amount)
    rw [fmap_nat_sum_increment_balance]
    unfold debited AddressMap.add
    rw [fmap_nat_sum_add]
    have hfrom_le := fmap_nat_sum_find_le (Base := Base) from_ prev_state.balances
    have henough' : amount ≤ from_balance := by
      simpa [from_balance, AddressMap.find] using henough
    have hfrom_le' : from_balance ≤ fmap_nat_sum prev_state.balances := by
      simpa [from_balance, AddressMap.find] using hfrom_le
    change
      fmap_nat_sum prev_state.balances =
        fmap_nat_sum prev_state.balances - from_balance +
          (from_balance - amount) + amount
    rw [Nat.add_assoc]
    rw [Nat.sub_add_cancel henough']
    rw [Nat.sub_add_cancel hfrom_le']

theorem try_transfer_from_preserves_balances_sum_raw
    {delegate from_ to_ : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_transfer_from delegate from_ to_ amount prev_state = .Ok new_state) :
    sum_balances prev_state = sum_balances new_state := by
  unfold try_transfer_from at h
  cases hFrom : AddressMap.find from_ prev_state.allowances with
  | none =>
      simp [hFrom] at h
  | some from_allowances =>
      cases hDelegate : AddressMap.find delegate from_allowances with
      | none =>
          simp [hFrom, hDelegate] at h
      | some delegate_allowance =>
          let from_balance :=
            with_default 0 (AddressMap.find from_ prev_state.balances)
          cases hBad : ((delegate_allowance < amount) || (from_balance < amount)) with
          | true =>
              simp [hFrom, hDelegate, from_balance, hBad, error] at h
          | false =>
              have hFromEnough : amount ≤ from_balance := by
                apply Nat.le_of_not_gt
                intro hlt
                simp [from_balance, hlt] at hBad
              simp [hFrom, hDelegate, from_balance, hBad] at h
              cases h
              unfold sum_balances
              let debited :=
                AddressMap.add from_ (from_balance - amount) prev_state.balances
              change
                fmap_nat_sum prev_state.balances =
                  fmap_nat_sum (increment_balance debited to_ amount)
              rw [fmap_nat_sum_increment_balance]
              unfold debited AddressMap.add
              rw [fmap_nat_sum_add]
              have hfrom_le :=
                fmap_nat_sum_find_le (Base := Base) from_ prev_state.balances
              have hfrom_le' :
                  from_balance ≤ fmap_nat_sum prev_state.balances := by
                simpa [from_balance, AddressMap.find] using hfrom_le
              change
                fmap_nat_sum prev_state.balances =
                  fmap_nat_sum prev_state.balances - from_balance +
                    (from_balance - amount) + amount
              rw [Nat.add_assoc]
              rw [Nat.sub_add_cancel hFromEnough]
              rw [Nat.sub_add_cancel hfrom_le']

theorem try_transfer_preserves_total_supply_raw
    {from_ to_ : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_transfer from_ to_ amount prev_state = .Ok new_state) :
    new_state.total_supply = prev_state.total_supply := by
  unfold try_transfer at h
  by_cases hlt :
      with_default 0 (AddressMap.find from_ prev_state.balances) < amount
  · simp [hlt, error] at h
  · simp [hlt] at h
    cases h
    rfl

theorem try_transfer_preserves_allowances_raw
    {from_ to_ : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_transfer from_ to_ amount prev_state = .Ok new_state) :
    new_state.allowances = prev_state.allowances := by
  unfold try_transfer at h
  by_cases hlt :
      with_default 0 (AddressMap.find from_ prev_state.balances) < amount
  · simp [hlt, error] at h
  · simp [hlt] at h
    cases h
    rfl

theorem try_transfer_from_preserves_total_supply_raw
    {delegate from_ to_ : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_transfer_from delegate from_ to_ amount prev_state = .Ok new_state) :
    new_state.total_supply = prev_state.total_supply := by
  unfold try_transfer_from at h
  cases hFrom : AddressMap.find from_ prev_state.allowances with
  | none =>
      simp [hFrom] at h
  | some from_allowances =>
      cases hDelegate : AddressMap.find delegate from_allowances with
      | none =>
          simp [hFrom, hDelegate] at h
      | some delegate_allowance =>
          let from_balance := with_default 0 (AddressMap.find from_ prev_state.balances)
          cases hBad : ((delegate_allowance < amount) || (from_balance < amount)) with
          | false =>
              simp [hFrom, hDelegate, from_balance, hBad] at h
              cases h
              rfl
          | true =>
              simp [hFrom, hDelegate, from_balance, hBad, error] at h

theorem try_approve_preserves_total_supply_raw
    {caller delegate : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_approve caller delegate amount prev_state = .Ok new_state) :
    new_state.total_supply = prev_state.total_supply := by
  unfold try_approve at h
  split at h <;> simp at h <;> cases h <;> rfl

theorem try_approve_preserves_balances_raw
    {caller delegate : Base.Address} {amount : TokenValue}
    {prev_state new_state : @State Base}
    (h : try_approve caller delegate amount prev_state = .Ok new_state) :
    new_state.balances = prev_state.balances := by
  unfold try_approve at h
  split at h <;> simp at h <;> cases h <;> rfl

theorem try_transfer_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer to_ amount)) =
      .Ok (new_state, new_acts)) :
    transfer_balance_update_correct prev_state new_state ctx.ctx_from to_ amount =
      true := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact try_transfer_balance_correct_raw hraw

theorem try_transfer_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer to_ amount)) =
      .Ok (new_state, new_acts)) :
    prev_state.total_supply = new_state.total_supply := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact (try_transfer_preserves_total_supply_raw hraw).symm

theorem try_transfer_preserves_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer to_ amount)) =
      .Ok (new_state, new_acts)) :
    prev_state.allowances = new_state.allowances := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact (try_transfer_preserves_allowances_raw hraw).symm

theorem try_transfer_preserves_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer to_ amount)) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state = sum_balances new_state := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact try_transfer_preserves_balances_sum_raw hraw

theorem try_transfer_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer to_ amount)) =
      .Ok (new_state, new_acts))
    (h_sender : account ≠ ctx.ctx_from) (h_receiver : account ≠ to_) :
    FMap.find account prev_state.balances = FMap.find account new_state.balances := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  unfold try_transfer at hraw
  by_cases hlt :
      with_default 0 (AddressMap.find ctx.ctx_from prev_state.balances) < amount
  · simp [hlt, error] at hraw
  · simp [hlt] at hraw
    cases hraw
    simp [AddressMap.add, increment_balance_is_partial_alter_plus,
      FMap.find_partial_alter_ne to_ account _ _ (Ne.symm h_receiver),
      FMap.find_add_ne ctx.ctx_from account _ _ (Ne.symm h_sender)]

theorem try_transfer_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (to_ : Base.Address)
    (amount : TokenValue) :
    (ctx.ctx_amount ≤ 0 ∧
        amount ≤ with_default 0 (FMap.find ctx.ctx_from state.balances)) ↔
      isOk (receive chain ctx state (some (.transfer to_ amount))) = true := by
  constructor
  · intro h
    have hamount : ¬ ctx.ctx_amount > 0 := not_lt.mpr h.1
    have hlt :
        ¬ with_default 0 (AddressMap.find ctx.ctx_from state.balances) < amount := by
      exact not_lt.mpr (by simpa [AddressMap.find] using h.2)
    unfold receive
    simp [hamount]
    unfold try_transfer
    rw [if_neg hlt]
    simp [without_actions, isOk]
  · intro hok
    by_cases hamount : ctx.ctx_amount > 0
    · simp [receive, hamount, error, isOk] at hok
    · constructor
      · exact le_of_not_gt hamount
      · unfold receive at hok
        simp [hamount] at hok
        unfold try_transfer at hok
        by_cases hlt :
            with_default 0 (AddressMap.find ctx.ctx_from state.balances) < amount
        · simp [hlt, error, without_actions, isOk] at hok
        · exact by simpa [AddressMap.find] using Nat.le_of_not_gt hlt

theorem try_transfer_from_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer_from from_ to_ amount)) =
      .Ok (new_state, new_acts)) :
    prev_state.total_supply = new_state.total_supply := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact (try_transfer_from_preserves_total_supply_raw hraw).symm

theorem try_transfer_from_preserves_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer_from from_ to_ amount)) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state = sum_balances new_state := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact try_transfer_from_preserves_balances_sum_raw hraw

theorem try_transfer_from_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer_from from_ to_ amount)) =
      .Ok (new_state, new_acts)) :
    transfer_balance_update_correct prev_state new_state from_ to_ amount = true ∧
      transfer_from_allowances_update_correct
        prev_state new_state from_ ctx.ctx_from amount = true := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact try_transfer_from_balance_correct_raw hraw

theorem try_transfer_from_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer_from from_ to_ amount)) =
      .Ok (new_state, new_acts))
    (h_from : account ≠ from_) (h_to : account ≠ to_) :
    FMap.find account prev_state.balances = FMap.find account new_state.balances := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  unfold try_transfer_from at hraw
  cases hFrom : AddressMap.find from_ prev_state.allowances with
  | none =>
      simp [hFrom] at hraw
  | some from_allowances =>
      cases hDelegate : AddressMap.find ctx.ctx_from from_allowances with
      | none =>
          simp [hFrom, hDelegate] at hraw
      | some delegate_allowance =>
          let from_balance := with_default 0 (AddressMap.find from_ prev_state.balances)
          cases hBad : ((delegate_allowance < amount) || (from_balance < amount)) with
          | true =>
              simp [hFrom, hDelegate, from_balance, hBad, error] at hraw
          | false =>
              simp [hFrom, hDelegate, from_balance, hBad] at hraw
              cases hraw
              simp [AddressMap.add, increment_balance_is_partial_alter_plus,
                FMap.find_partial_alter_ne to_ account _ _ (Ne.symm h_to),
                FMap.find_add_ne from_ account _ _ (Ne.symm h_from)]

theorem try_transfer_from_preserves_other_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer_from from_ to_ amount)) =
      .Ok (new_state, new_acts))
    (h_from : account ≠ from_) :
    FMap.find account prev_state.allowances = FMap.find account new_state.allowances := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  unfold try_transfer_from at hraw
  cases hFrom : AddressMap.find from_ prev_state.allowances with
  | none =>
      simp [hFrom] at hraw
  | some from_allowances =>
      cases hDelegate : AddressMap.find ctx.ctx_from from_allowances with
      | none =>
          simp [hFrom, hDelegate] at hraw
      | some delegate_allowance =>
          let from_balance := with_default 0 (AddressMap.find from_ prev_state.balances)
          cases hBad : ((delegate_allowance < amount) || (from_balance < amount)) with
          | true =>
              simp [hFrom, hDelegate, from_balance, hBad, error] at hraw
          | false =>
              simp [hFrom, hDelegate, from_balance, hBad] at hraw
              cases hraw
              simp [AddressMap.add,
                FMap.find_add_ne from_ account _ _ (Ne.symm h_from)]

theorem try_transfer_from_preserves_other_allowance
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.transfer_from from_ to_ amount)) =
      .Ok (new_state, new_acts))
    (h_delegate : account ≠ ctx.ctx_from) :
    get_allowance prev_state from_ account =
      get_allowance new_state from_ account := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  unfold try_transfer_from at hraw
  cases hFrom : AddressMap.find from_ prev_state.allowances with
  | none =>
      simp [hFrom] at hraw
  | some from_allowances =>
      cases hDelegate : AddressMap.find ctx.ctx_from from_allowances with
      | none =>
          simp [hFrom, hDelegate] at hraw
      | some delegate_allowance =>
          let from_balance := with_default 0 (AddressMap.find from_ prev_state.balances)
          cases hBad : ((delegate_allowance < amount) || (from_balance < amount)) with
          | true =>
              simp [hFrom, hDelegate, from_balance, hBad, error] at hraw
          | false =>
              simp [hFrom, hDelegate, from_balance, hBad] at hraw
              cases hraw
              unfold AddressMap.find at hFrom hDelegate
              simp [get_allowance, AddressMap.add, hFrom,
                FMap.find_add,
                FMap.find_add_ne ctx.ctx_from account _ _ (Ne.symm h_delegate),
                with_default, withDefault]

theorem try_transfer_from_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (from_ to_ : Base.Address)
    (amount : TokenValue) :
    let get_allowance_ account :=
      FMap.find account
        (with_default
          (FMap.empty : FMap Base.Address TokenValue)
          (FMap.find from_ state.allowances))
    (ctx.ctx_amount ≤ 0 ∧
        (FMap.find from_ state.allowances).isSome = true ∧
        (get_allowance_ ctx.ctx_from).isSome = true ∧
        amount ≤ with_default 0 (FMap.find from_ state.balances) ∧
        amount ≤ with_default 0 (get_allowance_ ctx.ctx_from)) ↔
      isOk (receive chain ctx state (some (.transfer_from from_ to_ amount))) =
        true := by
  dsimp
  constructor
  · intro h
    rcases h with
      ⟨hAmount, hFromSome, hDelegateSome, hBalance, hAllowance⟩
    have hamount : ¬ ctx.ctx_amount > 0 := not_lt.mpr hAmount
    unfold receive
    simp [hamount]
    unfold try_transfer_from
    cases hFrom : AddressMap.find from_ state.allowances with
    | none =>
        unfold AddressMap.find at hFrom
        simp [hFrom] at hFromSome
    | some from_allowances =>
        cases hDelegate : AddressMap.find ctx.ctx_from from_allowances with
        | none =>
            unfold AddressMap.find at hFrom hDelegate
            simp [hFrom, hDelegate, with_default, withDefault] at hDelegateSome
        | some delegate_allowance =>
            let from_balance :=
              with_default 0 (AddressMap.find from_ state.balances)
            have hDelegateNot : ¬ delegate_allowance < amount := by
              exact not_lt.mpr
                (by
                  unfold AddressMap.find at hFrom hDelegate
                  simpa [hFrom, hDelegate, with_default, withDefault]
                    using hAllowance)
            have hBalanceNot : ¬ from_balance < amount := by
              exact not_lt.mpr
                (by simpa [from_balance, AddressMap.find] using hBalance)
            have hBad :
                ((delegate_allowance < amount) || (from_balance < amount)) =
                  false := by
              simp [hDelegateNot, hBalanceNot]
            simp [hDelegate, from_balance, hBad, without_actions, isOk]
  · intro hok
    by_cases hamount : ctx.ctx_amount > 0
    · simp [receive, hamount, error, isOk] at hok
    · constructor
      · exact le_of_not_gt hamount
      · unfold receive at hok
        simp [hamount] at hok
        unfold try_transfer_from at hok
        cases hFrom : AddressMap.find from_ state.allowances with
        | none =>
            simp [hFrom, without_actions, isOk] at hok
        | some from_allowances =>
            cases hDelegate : AddressMap.find ctx.ctx_from from_allowances with
            | none =>
                simp [hFrom, hDelegate, without_actions, isOk] at hok
            | some delegate_allowance =>
                let from_balance :=
                  with_default 0 (AddressMap.find from_ state.balances)
                cases hBad :
                    ((delegate_allowance < amount) || (from_balance < amount)) with
                | true =>
                    simp [hFrom, hDelegate, from_balance, hBad, error,
                      without_actions, isOk] at hok
                | false =>
                    have hDelegateNot : ¬ delegate_allowance < amount := by
                      intro hlt
                      simp [hlt] at hBad
                    have hBalanceNot : ¬ from_balance < amount := by
                      intro hlt
                      simp [hlt] at hBad
                    unfold AddressMap.find at hFrom hDelegate
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · simp [hFrom]
                    · simp [hFrom, hDelegate, with_default, withDefault]
                    · exact by
                        simpa [from_balance, AddressMap.find]
                          using Nat.le_of_not_gt hBalanceNot
                    · simpa [hFrom, hDelegate, with_default, withDefault]
                        using Nat.le_of_not_gt hDelegateNot

theorem try_approve_allowance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve delegate amount)) =
      .Ok (new_state, new_acts)) :
    approve_allowance_update_correct new_state ctx.ctx_from delegate amount = true := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  unfold try_approve at hraw
  cases hCaller : AddressMap.find ctx.ctx_from prev_state.allowances with
  | some caller_allowances =>
      simp [hCaller] at hraw
      cases hraw
      simp [approve_allowance_update_correct, get_allowance,
        AddressMap.add, FMap.find_add, with_default, withDefault]
  | none =>
      simp [hCaller] at hraw
      cases hraw
      simp [approve_allowance_update_correct, get_allowance,
        AddressMap.add, FMap.find_add, with_default, withDefault]

theorem try_approve_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve delegate amount)) =
      .Ok (new_state, new_acts)) :
    prev_state.total_supply = new_state.total_supply := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact (try_approve_preserves_total_supply_raw hraw).symm

theorem try_approve_preserves_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve delegate amount)) =
      .Ok (new_state, new_acts)) :
    prev_state.balances = new_state.balances := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  exact (try_approve_preserves_balances_raw hraw).symm

theorem try_approve_preserves_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve delegate amount)) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state = sum_balances new_state := by
  unfold sum_balances
  rw [try_approve_preserves_balances h]

theorem outgoing_acts_nil
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))) :
    outgoing_acts bstate caddr = [] := by
  exact
    lift_outgoing_acts_nil
      (contract :=
        (contract :
          @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))
      bstate caddr hr
      (by
        intro chain ctx cstate msg new_cstate acts hreceive
        exact EIP20_no_acts
          (chain := chain) (ctx := ctx) (msg := msg)
          (new_acts := acts) hreceive)
      hdeployed

theorem try_approve_preserves_other_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve delegate amount)) =
      .Ok (new_state, new_acts))
    (h_sender : account ≠ ctx.ctx_from) :
    FMap.find account prev_state.allowances = FMap.find account new_state.allowances := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  unfold try_approve at hraw
  cases hCaller : AddressMap.find ctx.ctx_from prev_state.allowances with
  | some caller_allowances =>
      simp [hCaller] at hraw
      cases hraw
      simp [AddressMap.add,
        FMap.find_add_ne ctx.ctx_from account _ _ (Ne.symm h_sender)]
  | none =>
      simp [hCaller] at hraw
      cases hraw
      simp [AddressMap.add,
        FMap.find_add_ne ctx.ctx_from account _ _ (Ne.symm h_sender)]

theorem try_approve_preserves_other_allowance
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.approve delegate amount)) =
      .Ok (new_state, new_acts))
    (h_delegate : account ≠ delegate) :
    get_allowance prev_state ctx.ctx_from account =
      get_allowance new_state ctx.ctx_from account := by
  have hraw := without_actions_ok_state (Base := Base) (receive_not_payable h)
  unfold try_approve at hraw
  cases hCaller : AddressMap.find ctx.ctx_from prev_state.allowances with
  | some caller_allowances =>
      simp [hCaller] at hraw
      cases hraw
      unfold AddressMap.find at hCaller
      simp [get_allowance, AddressMap.add, hCaller, with_default, withDefault,
        FMap.find_add, FMap.find_add_ne delegate account _ _ (Ne.symm h_delegate)]
  | none =>
      simp [hCaller] at hraw
      cases hraw
      unfold AddressMap.find at hCaller
      simp [get_allowance, AddressMap.add, hCaller, with_default, withDefault,
        FMap.find_add,
        FMap.find_add_ne delegate account _ _ (Ne.symm h_delegate),
        FMap.find_empty, AddressMap.empty]

theorem try_approve_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (delegate : Base.Address)
    (amount : TokenValue) :
    ctx.ctx_amount ≤ 0 ↔
      isOk (receive chain ctx state (some (.approve delegate amount))) = true := by
  constructor
  · intro h
    have hamount : ¬ ctx.ctx_amount > 0 := not_lt.mpr h
    unfold receive
    simp [hamount]
    unfold try_approve
    cases AddressMap.find ctx.ctx_from state.allowances <;>
      simp [without_actions, isOk]
  · intro hok
    by_cases hamount : ctx.ctx_amount > 0
    · simp [receive, hamount, error, isOk] at hok
    · exact le_of_not_gt hamount

theorem init_preserves_balances_sum
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base}
    (h : init chain ctx setup = .Ok state) :
    state.total_supply = sum_balances state := by
  simp [init] at h
  cases h
  unfold sum_balances
  change
    setup.init_amount =
      fmap_nat_sum
        (FMap.add setup.owner setup.init_amount
          (FMap.empty : FMap Base.Address Nat))
  rw [fmap_nat_sum_add_new]
  · simp [fmap_nat_sum, FMap.elements_empty]
  · exact FMap.find_empty setup.owner

theorem total_supply_eq_init_supply
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate) :
    bstate.env_contracts caddr =
      some (contract_to_weak_contract (contract : @Contract Base _ _ _ _ _ _ _ _)) →
    ∃ deploy_info cstate,
      deployment_info (@Setup Base) trace caddr = some deploy_info ∧
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr = some cstate ∧
      deploy_info.deployment_setup.init_amount = cstate.total_supply := by
  intro hdeployed
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base (@Setup Base) →
          @State Base → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ dep cstate _ _ _ _ =>
      dep.deployment_setup.init_amount = cstate.total_supply
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
      simp [P, contract, init] at hinit ⊢
      cases hinit
      rfl
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
      exact ih
    · intro chain ctx _ prev_state msg _ _ _ new_state new_acts
        _ _ ih hreceive _
      simp [P] at ih ⊢
      cases msg with
      | none =>
          simp [contract, receive, error] at hreceive
      | some msg =>
          cases msg with
          | transfer to_ amount =>
              have hp := try_transfer_preserves_total_supply
                (chain := chain) (ctx := ctx) (to_ := to_) (amount := amount)
                (new_acts := new_acts) hreceive
              rw [← hp]
              exact ih
          | transfer_from from_ to_ amount =>
              have hp := try_transfer_from_preserves_total_supply
                (chain := chain) (ctx := ctx) (from_ := from_) (to_ := to_)
                (amount := amount) (new_acts := new_acts) hreceive
              rw [← hp]
              exact ih
          | approve delegate amount =>
              have hp := try_approve_preserves_total_supply
                (chain := chain) (ctx := ctx) (delegate := delegate)
                (amount := amount) (new_acts := new_acts) hreceive
              rw [← hp]
              exact ih
    · intro chain ctx _ prev_state msg _ _ _ _ new_state new_acts
        _ _ ih _ hreceive _
      simp [P] at ih ⊢
      cases msg with
      | none =>
          simp [contract, receive, error] at hreceive
      | some msg =>
          cases msg with
          | transfer to_ amount =>
              have hp := try_transfer_preserves_total_supply
                (chain := chain) (ctx := ctx) (to_ := to_) (amount := amount)
                (new_acts := new_acts) hreceive
              rw [← hp]
              exact ih
          | transfer_from from_ to_ amount =>
              have hp := try_transfer_from_preserves_total_supply
                (chain := chain) (ctx := ctx) (from_ := from_) (to_ := to_)
                (amount := amount) (new_acts := new_acts) hreceive
              rw [← hp]
              exact ih
          | approve delegate amount =>
              have hp := try_approve_preserves_total_supply
                (chain := chain) (ctx := ctx) (delegate := delegate)
                (amount := amount) (new_acts := new_acts) hreceive
              rw [← hp]
              exact ih
    · intro _ _ _ _ _ _ _ _ _ _ _ ih _ _
      exact ih
  obtain ⟨dep, cstate, _inc_calls, hdep, hstate, _hcalls, hP⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  exact ⟨dep, cstate, hdep, hstate, hP⟩

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
          (state := result) (chain := chain) (ctx := ctx)
          (setup := setup) hinit)
      (by
        intro chain ctx cstate msg new_cstate acts hQ hreceive
        simp [Q] at hQ ⊢
        cases msg with
        | none =>
            simp [contract, receive, error] at hreceive
        | some msg =>
            cases msg with
            | transfer to_ amount =>
                have hsum := try_transfer_preserves_balances_sum
                  (chain := chain) (ctx := ctx) (to_ := to_)
                  (amount := amount) (new_acts := acts) hreceive
                have htotal := try_transfer_preserves_total_supply
                  (chain := chain) (ctx := ctx) (to_ := to_)
                  (amount := amount) (new_acts := acts) hreceive
                rw [← htotal, ← hsum]
                exact hQ
            | transfer_from from_ to_ amount =>
                have hsum := try_transfer_from_preserves_balances_sum
                  (chain := chain) (ctx := ctx) (from_ := from_) (to_ := to_)
                  (amount := amount) (new_acts := acts) hreceive
                have htotal := try_transfer_from_preserves_total_supply
                  (chain := chain) (ctx := ctx) (from_ := from_) (to_ := to_)
                  (amount := amount) (new_acts := acts) hreceive
                rw [← htotal, ← hsum]
                exact hQ
            | approve delegate amount =>
                have hsum := try_approve_preserves_balances_sum
                  (chain := chain) (ctx := ctx) (delegate := delegate)
                  (amount := amount) (new_acts := acts) hreceive
                have htotal := try_approve_preserves_total_supply
                  (chain := chain) (ctx := ctx) (delegate := delegate)
                  (amount := amount) (new_acts := acts) hreceive
                rw [← htotal, ← hsum]
                exact hQ)
      hr hdeployed
  exact ⟨cstate, hstate, hQ⟩

end ConCert.Examples.EIP20.EIP20Token
