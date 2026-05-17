/- Port of the entrypoint-level lemmas from
examples/dexter2/Dexter2FA12Correct.v. -/

import ConCert.Examples.Dexter2.Dexter2FA12

namespace ConCert.Examples.Dexter2.FA12.Correct

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Utils.Extras

variable [Base : ChainBase]

private theorem without_actions_ok
    {r : Result (@State Base) Error} {state : @State Base}
    {acts : List (@ActionBody Base)}
    (h : without_actions (Base := Base) r = .Ok (state, acts)) :
    r = .Ok state ∧ acts = [] := by
  cases r with
  | Ok st =>
      simp [without_actions] at h
      exact ⟨by cases h.1; rfl, h.2⟩
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

private theorem receive_transfer_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
      .Ok (new_state, new_acts)) :
    try_transfer ctx.ctx_from param prev_state = .Ok new_state ∧
      new_acts = [] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  have hnot : ¬ 0 < ctx.ctx_amount := hpos
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact without_actions_ok (Base := Base) h

private theorem receive_approve_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {param : @ApproveParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_approve param)) =
      .Ok (new_state, new_acts)) :
    try_approve ctx.ctx_from param prev_state = .Ok new_state ∧
      new_acts = [] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  have hnot : ¬ 0 < ctx.ctx_amount := hpos
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact without_actions_ok (Base := Base) h

private theorem receive_mint_or_burn_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {param : @MintOrBurnParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_mint_or_burn param)) =
      .Ok (new_state, new_acts)) :
    try_mint_or_burn ctx.ctx_from param prev_state = .Ok new_state ∧
      new_acts = [] := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  have hnot : ¬ 0 < ctx.ctx_amount := hpos
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact without_actions_ok (Base := Base) h

theorem contract_not_payable
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Option (@Msg Base)}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    ctx.ctx_amount ≤ 0 := by
  by_cases hpos : 0 < ctx.ctx_amount
  · unfold receive at h
    simp [non_zero_amount, hpos] at h
  · exact le_of_not_gt hpos

theorem contract_not_payable'
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (msg : Option (@Msg Base))
    (hpos : 0 < ctx.ctx_amount) :
    receive chain ctx prev_state msg = .Err default_error := by
  unfold receive
  simp [non_zero_amount, hpos]

theorem default_entrypoint_none
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) :
    receive chain ctx prev_state none = .Err default_error := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos]
  · simp [receive, non_zero_amount, hpos]

def transfer_balance_update_correct
    (old_state new_state : @State Base)
    (from_ to_ : Base.Address) (amount : Nat) : Bool :=
  let get_balance_ addr state :=
    with_default 0 (FMap.find addr state.tokens)
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
  let get_allowance_ owner spender state :=
    with_default 0 (FMap.find (owner, spender) state.allowances)
  let allowance_before := get_allowance_ from_ sender old_state
  let allowance_after := get_allowance_ from_ sender new_state
  if Base.address_eqb sender from_ then
    allowance_before == allowance_after
  else
    allowance_before == allowance_after + amount

private theorem try_transfer_admin_constant
    {sender : Base.Address} {param : @TransferParam Base}
    {prev_state new_state : @State Base}
    (h : try_transfer sender param prev_state = .Ok new_state) :
    prev_state.admin = new_state.admin := by
  unfold try_transfer at h
  by_cases hsender : Base.address_eqb sender param.from_ = true
  · simp [hsender] at h
    by_cases hbal :
        with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
          param.value
    · simp [hbal] at h
    · simp [hbal] at h
      cases h
      rfl
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
        rfl

private theorem try_approve_admin_constant
    {sender : Base.Address} {param : @ApproveParam Base}
    {prev_state new_state : @State Base}
    (h : try_approve sender param prev_state = .Ok new_state) :
    prev_state.admin = new_state.admin := by
  unfold try_approve at h
  by_cases hbad :
      (decide
          (0 <
            with_default 0
              (find_allowance (sender, param.spender) prev_state.allowances)) &&
        decide (0 < param.value_)) = true
  · simp [hbad] at h
  · simp [hbad] at h
    cases h
    rfl

private theorem try_mint_or_burn_admin_constant
    {sender : Base.Address} {param : @MintOrBurnParam Base}
    {prev_state new_state : @State Base}
    (h : try_mint_or_burn sender param prev_state = .Ok new_state) :
    prev_state.admin = new_state.admin := by
  unfold try_mint_or_burn at h
  by_cases hadmin : Base.address_eqb sender prev_state.admin = true
  · simp [hadmin] at h
    split at h
    · simp at h
    · simp at h
      cases h
      rfl
  · simp [hadmin] at h

theorem admin_constant
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Option (@Msg Base)}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    prev_state.admin = new_state.admin := by
  by_cases hpos : 0 < ctx.ctx_amount
  · simp [receive, non_zero_amount, hpos] at h
  have hnot : ¬ 0 < ctx.ctx_amount := hpos
  cases msg with
  | none =>
      simp [receive, non_zero_amount, hnot] at h
  | some msg =>
      cases msg with
      | msg_transfer param =>
          exact try_transfer_admin_constant
            (receive_transfer_ok (Base := Base) h).1
      | msg_approve param =>
          exact try_approve_admin_constant
            (receive_approve_ok (Base := Base) h).1
      | msg_mint_or_burn param =>
          exact try_mint_or_burn_admin_constant
            (receive_mint_or_burn_ok (Base := Base) h).1
      | msg_get_allowance param =>
          simp [receive, non_zero_amount, hnot] at h
          cases h.1
          rfl
      | msg_get_balance param =>
          simp [receive, non_zero_amount, hnot] at h
          cases h.1
          rfl
      | msg_get_total_supply param =>
          simp [receive, non_zero_amount, hnot] at h
          cases h.1
          rfl

private theorem try_transfer_preserves_total_supply_raw
    {sender : Base.Address} {param : @TransferParam Base}
    {prev_state new_state : @State Base}
    (h : try_transfer sender param prev_state = .Ok new_state) :
    prev_state.total_supply = new_state.total_supply := by
  unfold try_transfer at h
  by_cases hsender : Base.address_eqb sender param.from_ = true
  · simp [hsender] at h
    by_cases hbal :
        with_default 0 (AddressMap.find param.from_ prev_state.tokens) <
          param.value
    · simp [hbal] at h
    · simp [hbal] at h
      cases h
      rfl
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
        rfl

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

theorem try_transfer_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
      .Ok (new_state, new_acts)) :
    new_acts = [] :=
  (receive_transfer_ok (Base := Base) h).2

theorem try_transfer_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
      .Ok (new_state, new_acts)) :
    prev_state.total_supply = new_state.total_supply :=
  try_transfer_preserves_total_supply_raw
    (Base := Base) (receive_transfer_ok (Base := Base) h).1

theorem try_transfer_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @TransferParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
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
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
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
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
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
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
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
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
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
    (h : receive chain ctx prev_state (some (.msg_transfer param)) =
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
          rcases maybe_cases
              (with_default 0
                  (AddressMap.find param.to_
                    (AddressMap.update param.from_
                      (maybe
                        (with_default 0
                            (AddressMap.find param.from_ prev_state.tokens) -
                          param.value))
                      prev_state.tokens)) +
                param.value) with hnone | hsome
          · rcases hnone with ⟨hnone, _⟩
            simp [AddressMap.update, hft] at hnone
            simp [hnone] at h_find
          · rcases hsome with ⟨hsome, hpos⟩
            simp [AddressMap.update, hft] at hsome
            simp [hsome] at h_find
            cases h_find
            simpa [AddressMap.update, hft] using hpos
        · simp [AddressMap.update,
            FMap.find_update_ne param.from_ param.to_ _ _ hft,
            FMap.find_update_eq] at h_find
          rcases maybe_cases
              (with_default 0
                  (AddressMap.find param.from_ prev_state.tokens) -
                param.value) with hnone | hsome
          · rcases hnone with ⟨hnone, _⟩
            simp [hnone] at h_find
          · rcases hsome with ⟨hsome, hpos⟩
            simp [hsome] at h_find
            cases h_find
            exact hpos
      · intro h_find
        simp [AddressMap.update, FMap.find_update_eq] at h_find
        rcases maybe_cases
            (with_default 0
                (AddressMap.find param.to_
                  (AddressMap.update param.from_
                    (maybe
                      (with_default 0
                          (AddressMap.find param.from_ prev_state.tokens) -
                        param.value))
                    prev_state.tokens)) +
              param.value) with hnone | hsome
        · rcases hnone with ⟨hnone, _⟩
          simp [AddressMap.update] at hnone
          simp [hnone] at h_find
        · rcases hsome with ⟨hsome, hpos⟩
          simp [AddressMap.update] at hsome
          simp [hsome] at h_find
          cases h_find
          exact hpos
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
            rcases maybe_cases
                (with_default 0
                    (AddressMap.find param.to_
                      (AddressMap.update param.from_
                        (maybe
                          (with_default 0
                              (AddressMap.find param.from_ prev_state.tokens) -
                            param.value))
                        prev_state.tokens)) +
                  param.value) with hnone | hsome
            · rcases hnone with ⟨hnone, _⟩
              simp [AddressMap.update, hft] at hnone
              simp [hnone] at h_find
            · rcases hsome with ⟨hsome, hpos⟩
              simp [AddressMap.update, hft] at hsome
              simp [hsome] at h_find
              cases h_find
              simpa [AddressMap.update, hft] using hpos
          · simp [AddressMap.update,
              FMap.find_update_ne param.from_ param.to_ _ _ hft,
              FMap.find_update_eq] at h_find
            rcases maybe_cases
                (with_default 0
                    (AddressMap.find param.from_ prev_state.tokens) -
                  param.value) with hnone | hsome
            · rcases hnone with ⟨hnone, _⟩
              simp [hnone] at h_find
            · rcases hsome with ⟨hsome, hpos⟩
              simp [hsome] at h_find
              cases h_find
              exact hpos
        · intro h_find
          simp [AddressMap.update, FMap.find_update_eq] at h_find
          rcases maybe_cases
              (with_default 0
                  (AddressMap.find param.to_
                    (AddressMap.update param.from_
                      (maybe
                        (with_default 0
                            (AddressMap.find param.from_ prev_state.tokens) -
                          param.value))
                      prev_state.tokens)) +
                param.value) with hnone | hsome
          · rcases hnone with ⟨hnone, _⟩
            simp [AddressMap.update] at hnone
            simp [hnone] at h_find
          · rcases hsome with ⟨hsome, hpos⟩
            simp [AddressMap.update] at hsome
            simp [hsome] at h_find
            cases h_find
            exact hpos

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
        receive chain ctx prev_state (some (.msg_transfer param)) =
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

private theorem try_approve_preserves_total_supply_raw
    {sender : Base.Address} {param : @ApproveParam Base}
    {prev_state new_state : @State Base}
    (h : try_approve sender param prev_state = .Ok new_state) :
    prev_state.total_supply = new_state.total_supply := by
  unfold try_approve at h
  by_cases hbad :
      (decide
          (0 <
            with_default 0
              (find_allowance (sender, param.spender) prev_state.allowances)) &&
        decide (0 < param.value_)) = true
  · simp [hbad] at h
  · simp [hbad] at h
    cases h
    rfl

private theorem try_approve_preserves_balances_raw
    {sender : Base.Address} {param : @ApproveParam Base}
    {prev_state new_state : @State Base}
    (h : try_approve sender param prev_state = .Ok new_state) :
    prev_state.tokens = new_state.tokens := by
  unfold try_approve at h
  by_cases hbad :
      (decide
          (0 <
            with_default 0
              (find_allowance (sender, param.spender) prev_state.allowances)) &&
        decide (0 < param.value_)) = true
  · simp [hbad] at h
  · simp [hbad] at h
    cases h
    rfl

theorem try_approve_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @ApproveParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_approve param)) =
      .Ok (new_state, new_acts)) :
    new_acts = [] :=
  (receive_approve_ok (Base := Base) h).2

theorem try_approve_allowance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @ApproveParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_approve param)) =
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

theorem try_approve_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @ApproveParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_approve param)) =
      .Ok (new_state, new_acts)) :
    prev_state.total_supply = new_state.total_supply :=
  try_approve_preserves_total_supply_raw
    (Base := Base) (receive_approve_ok (Base := Base) h).1

theorem try_approve_preserves_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @ApproveParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_approve param)) =
      .Ok (new_state, new_acts)) :
    prev_state.tokens = new_state.tokens :=
  try_approve_preserves_balances_raw
    (Base := Base) (receive_approve_ok (Base := Base) h).1

theorem try_approve_preserves_other_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @ApproveParam Base} {allowance_key : Base.Address × Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_approve param)) =
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
    (h : receive chain ctx prev_state (some (.msg_approve param)) =
      .Ok (new_state, new_acts))
    {n : Nat}
    (hfind :
      FMap.find (ctx.ctx_from, param.spender) new_state.allowances =
        some n) :
    0 < n := by
  rw [try_approve_allowance_correct (Base := Base) h] at hfind
  rcases maybe_cases param.value_ with ⟨hm, hzero⟩ | ⟨hm, hpos⟩
  · rw [hm] at hfind
    cases hfind
  · rw [hm] at hfind
    cases hfind
    exact hpos

theorem try_approve_is_some
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @ApproveParam Base) :
    (ctx.ctx_amount ≤ 0 ∧
        ¬(0 <
            with_default 0
              (find_allowance (ctx.ctx_from, param.spender)
                prev_state.allowances) ∧
          0 < param.value_)) ↔
      ∃ new_state new_acts,
        receive chain ctx prev_state (some (.msg_approve param)) =
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
      by_cases hprev : 0 < previous_value
      · by_cases hval : 0 < param.value_
        · exact False.elim (hvalid ⟨hprev, hval⟩)
        · simp [hprev, hval]
      · simp [hprev]
    unfold receive try_approve
    simp [non_zero_amount, hnot, allowance_key, previous_value, new_state,
      hbad, without_actions]
  · rintro ⟨new_state, new_acts, h⟩
    constructor
    · exact contract_not_payable (Base := Base) h
    · intro hbadProp
      rcases hbadProp with ⟨hprev, hval⟩
      rcases receive_approve_ok (Base := Base) h with ⟨hraw, _⟩
      unfold try_approve at hraw
      have hbad :
          (decide
              (0 <
                with_default 0
                  (find_allowance (ctx.ctx_from, param.spender)
                    prev_state.allowances)) &&
            decide (0 < param.value_)) = true := by
        simp [hprev, hval]
      simp [hbad] at hraw

theorem try_mint_or_burn_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @MintOrBurnParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_mint_or_burn param)) =
      .Ok (new_state, new_acts)) :
    new_acts = [] :=
  (receive_mint_or_burn_ok (Base := Base) h).2

private theorem try_mint_or_burn_preserves_allowances_raw
    {sender : Base.Address} {param : @MintOrBurnParam Base}
    {prev_state new_state : @State Base}
    (h : try_mint_or_burn sender param prev_state = .Ok new_state) :
    prev_state.allowances = new_state.allowances := by
  unfold try_mint_or_burn at h
  by_cases hadmin : Base.address_eqb sender prev_state.admin = true
  · simp [hadmin] at h
    split at h
    · simp at h
    · simp at h
      cases h
      rfl
  · simp [hadmin] at h

theorem try_mint_or_burn_preserves_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @MintOrBurnParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_mint_or_burn param)) =
      .Ok (new_state, new_acts)) :
    prev_state.allowances = new_state.allowances :=
  try_mint_or_burn_preserves_allowances_raw
    (Base := Base) (receive_mint_or_burn_ok (Base := Base) h).1

private theorem try_mint_or_burn_ok_shape
    {sender : Base.Address} {param : @MintOrBurnParam Base}
    {prev_state new_state : @State Base}
    (h : try_mint_or_burn sender param prev_state = .Ok new_state) :
    sender = prev_state.admin ∧
      0 ≤
        Int.ofNat
            (with_default 0
              (AddressMap.find param.target prev_state.tokens)) +
          param.quantity ∧
      new_state =
        { prev_state with
          tokens :=
            AddressMap.update param.target
              (maybe
                (Int.ofNat
                    (with_default 0
                      (AddressMap.find param.target prev_state.tokens)) +
                  param.quantity).toNat)
              prev_state.tokens,
          total_supply :=
            (Int.ofNat prev_state.total_supply + param.quantity).natAbs } := by
  unfold try_mint_or_burn at h
  by_cases hadmin : Base.address_eqb sender prev_state.admin = true
  · have hsender := (Base.address_eqb_spec _ _).mp hadmin
    simp [hadmin] at h
    split at h
    · simp at h
    · rename_i hnonneg
      simp at h
      cases h
      exact ⟨hsender, le_of_not_gt hnonneg, rfl⟩
  · simp [hadmin] at h

theorem try_mint_or_burn_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @MintOrBurnParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_mint_or_burn param)) =
      .Ok (new_state, new_acts)) :
    get_balance param.target new_state =
      (Int.ofNat (get_balance param.target prev_state) +
        param.quantity).toNat := by
  rcases receive_mint_or_burn_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_mint_or_burn_ok_shape (Base := Base) hraw with
    ⟨_, _, hstate⟩
  rw [hstate]
  simp [get_balance, AddressMap.find, AddressMap.update, FMap.find_update_eq,
    with_default_maybe]

theorem try_mint_or_burn_total_supply_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @MintOrBurnParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_mint_or_burn param)) =
      .Ok (new_state, new_acts)) :
    new_state.total_supply =
      (Int.ofNat prev_state.total_supply + param.quantity).natAbs := by
  rcases receive_mint_or_burn_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_mint_or_burn_ok_shape (Base := Base) hraw with
    ⟨_, _, hstate⟩
  rw [hstate]

theorem try_mint_or_burn_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {account : Base.Address}
    {param : @MintOrBurnParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_mint_or_burn param)) =
      .Ok (new_state, new_acts))
    (h_account : account ≠ param.target) :
    FMap.find account prev_state.tokens =
      FMap.find account new_state.tokens := by
  rcases receive_mint_or_burn_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_mint_or_burn_ok_shape (Base := Base) hraw with
    ⟨_, _, hstate⟩
  rw [hstate]
  simp [AddressMap.update,
    FMap.find_update_ne account param.target _ prev_state.tokens h_account]

theorem try_mint_or_burn_remove_empty_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @MintOrBurnParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_mint_or_burn param)) =
      .Ok (new_state, new_acts))
    {n : Nat}
    (h_find : FMap.find param.target new_state.tokens = some n) :
    0 < n := by
  rcases receive_mint_or_burn_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_mint_or_burn_ok_shape (Base := Base) hraw with
    ⟨_, _, hstate⟩
  rw [hstate] at h_find
  simp [AddressMap.update, FMap.find_update_eq] at h_find
  exact maybe_some_pos h_find

theorem try_mint_or_burn_is_some
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @MintOrBurnParam Base) :
    (ctx.ctx_amount ≤ 0 ∧
        ctx.ctx_from = prev_state.admin ∧
        0 ≤
          Int.ofNat
              (with_default 0
                (AddressMap.find param.target prev_state.tokens)) +
            param.quantity) ↔
      ∃ new_state new_acts,
        receive chain ctx prev_state (some (.msg_mint_or_burn param)) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro h
    rcases h with ⟨hamount, hsender, hnonneg⟩
    let new_state :=
      { prev_state with
        tokens :=
          AddressMap.update param.target
            (maybe
              (Int.ofNat
                  (with_default 0
                    (AddressMap.find param.target prev_state.tokens)) +
                param.quantity).toNat)
          prev_state.tokens,
        total_supply :=
          (Int.ofNat prev_state.total_supply + param.quantity).natAbs }
    refine ⟨new_state, [], ?_⟩
    have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
    have hadmin :
        Base.address_eqb ctx.ctx_from prev_state.admin = true :=
      (Base.address_eqb_spec _ _).mpr hsender
    have hneg :
        ¬ Int.ofNat
              (with_default 0
                (AddressMap.find param.target prev_state.tokens)) +
            param.quantity <
          0 := by
      exact not_lt.mpr hnonneg
    unfold receive try_mint_or_burn
    have hif :
        (if ((with_default 0
                (AddressMap.find param.target prev_state.tokens) : Nat) : Int) +
              param.quantity <
            0 then
            (.Err default_error : Result (@State Base) Error)
          else
            .Ok
              { prev_state with
                tokens := AddressMap.update param.target
                  (maybe
                    (((with_default 0
                          (AddressMap.find param.target prev_state.tokens) :
                        Nat) : Int) +
                      param.quantity).toNat)
                  prev_state.tokens,
                total_supply :=
                  (((prev_state.total_supply : Nat) : Int) +
                    param.quantity).natAbs }) =
          .Ok
            { prev_state with
              tokens := AddressMap.update param.target
                (maybe
                  (((with_default 0
                        (AddressMap.find param.target prev_state.tokens) :
                      Nat) : Int) +
                    param.quantity).toNat)
                prev_state.tokens,
              total_supply :=
                (((prev_state.total_supply : Nat) : Int) +
                  param.quantity).natAbs } := by
      exact if_neg hneg
    simp [non_zero_amount, hnot, hadmin, new_state, without_actions]
    rw [hif]
  · rintro ⟨new_state, new_acts, h⟩
    rcases receive_mint_or_burn_ok (Base := Base) h with ⟨hraw, _⟩
    constructor
    · exact contract_not_payable (Base := Base) h
    constructor
    · unfold try_mint_or_burn at hraw
      by_cases hadmin :
          Base.address_eqb ctx.ctx_from prev_state.admin = true
      · exact (Base.address_eqb_spec _ _).mp hadmin
      · simp [hadmin] at hraw
    · unfold try_mint_or_burn at hraw
      by_cases hadmin :
          Base.address_eqb ctx.ctx_from prev_state.admin = true
      · simp [hadmin] at hraw
        split at hraw
        · simp at hraw
        · rename_i hnonneg
          exact le_of_not_gt hnonneg
      · simp [hadmin] at hraw

theorem try_get_allowance_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @GetAllowanceParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_get_allowance param)) =
      .Ok (new_state, new_acts)) :
    new_acts = try_get_allowance ctx.ctx_from param prev_state := by
  have hamount := contract_not_payable (Base := Base) h
  have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact h.2.symm

theorem try_get_allowance_preserves_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @GetAllowanceParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_get_allowance param)) =
      .Ok (new_state, new_acts)) :
    new_state = prev_state := by
  have hamount := contract_not_payable (Base := Base) h
  have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact h.1.symm

theorem try_get_allowance_is_some
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @GetAllowanceParam Base) :
    ctx.ctx_amount ≤ 0 ↔
      ∃ new_state new_acts,
        receive chain ctx prev_state (some (.msg_get_allowance param)) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro hamount
    refine ⟨prev_state, try_get_allowance ctx.ctx_from param prev_state, ?_⟩
    have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
    simp [receive, non_zero_amount, hnot]
  · rintro ⟨new_state, new_acts, h⟩
    exact contract_not_payable (Base := Base) h

theorem try_get_balance_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @GetBalanceParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_get_balance param)) =
      .Ok (new_state, new_acts)) :
    new_acts = try_get_balance ctx.ctx_from param prev_state := by
  have hamount := contract_not_payable (Base := Base) h
  have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact h.2.symm

theorem try_get_balance_preserves_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @GetBalanceParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_get_balance param)) =
      .Ok (new_state, new_acts)) :
    new_state = prev_state := by
  have hamount := contract_not_payable (Base := Base) h
  have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact h.1.symm

theorem try_get_balance_is_some
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @GetBalanceParam Base) :
    ctx.ctx_amount ≤ 0 ↔
      ∃ new_state new_acts,
        receive chain ctx prev_state (some (.msg_get_balance param)) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro hamount
    refine ⟨prev_state, try_get_balance ctx.ctx_from param prev_state, ?_⟩
    have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
    simp [receive, non_zero_amount, hnot]
  · rintro ⟨new_state, new_acts, h⟩
    exact contract_not_payable (Base := Base) h

theorem try_get_total_supply_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @GetTotalSupplyParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_get_total_supply param)) =
      .Ok (new_state, new_acts)) :
    new_acts = try_get_total_supply ctx.ctx_from param prev_state := by
  have hamount := contract_not_payable (Base := Base) h
  have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact h.2.symm

theorem try_get_total_supply_preserves_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {param : @GetTotalSupplyParam Base}
    {new_acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state (some (.msg_get_total_supply param)) =
      .Ok (new_state, new_acts)) :
    new_state = prev_state := by
  have hamount := contract_not_payable (Base := Base) h
  have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
  unfold receive at h
  simp [non_zero_amount, hnot] at h
  exact h.1.symm

theorem try_get_total_supply_is_some
    (prev_state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (param : @GetTotalSupplyParam Base) :
    ctx.ctx_amount ≤ 0 ↔
      ∃ new_state new_acts,
        receive chain ctx prev_state (some (.msg_get_total_supply param)) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro hamount
    refine ⟨prev_state, try_get_total_supply ctx.ctx_from param prev_state, ?_⟩
    have hnot : ¬ 0 < ctx.ctx_amount := not_lt.mpr hamount
    simp [receive, non_zero_amount, hnot]
  · rintro ⟨new_state, new_acts, h⟩
    exact contract_not_payable (Base := Base) h

theorem init_balances_correct
    {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base} {state : @State Base}
    (h : init chain ctx setup = .Ok state) :
    state.tokens =
      AddressMap.add setup.lqt_provider setup.initial_pool AddressMap.empty := by
  unfold init at h
  cases h
  rfl

theorem init_allowances_correct
    {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base} {state : @State Base}
    (h : init chain ctx setup = .Ok state) :
    state.allowances = FMap.empty := by
  unfold init at h
  cases h
  rfl

theorem init_admin_correct
    {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base} {state : @State Base}
    (h : init chain ctx setup = .Ok state) :
    state.admin = setup.admin_ := by
  unfold init at h
  cases h
  rfl

theorem init_total_supply_correct
    {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base} {state : @State Base}
    (h : init chain ctx setup = .Ok state) :
    state.total_supply = setup.initial_pool := by
  unfold init at h
  cases h
  rfl

theorem init_is_some
    (chain : Chain) (ctx : @ContractCallContext Base) (setup : @Setup Base) :
    ∃ state, init chain ctx setup = .Ok state := by
  refine ⟨{ tokens := AddressMap.add setup.lqt_provider setup.initial_pool
              AddressMap.empty,
            allowances := empty_allowance,
            admin := setup.admin_,
            total_supply := setup.initial_pool }, ?_⟩
  rfl

end ConCert.Examples.Dexter2.FA12.Correct
