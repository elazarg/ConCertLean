/- Functional-correctness lemmas for examples/bat/BATAltFixCorrect.v. -/

import ConCert.Examples.BAT.BATCommon
import ConCert.Execution.BlockchainInduction
import ConCert.Examples.EIP20.EIP20TokenCorrect
import Mathlib.Tactic.Linarith

namespace ConCert.Examples.BAT

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.ResultMonad
open ConCert.Utils.Extras

namespace AltFixCorrect

variable [Base : ChainBase]

@[simp] private theorem isOk_receive_token_lift
    (state : @State Base)
    (r : Result
      (@ConCert.Examples.EIP20.EIP20Token.State Base × List (@ActionBody Base))
      Error) :
    isOk
        (match r with
         | .Err e => .Err e
         | .Ok (token_state, acts) =>
             .Ok ({ state with token_state := token_state }, acts)) =
      isOk r := by
  cases r with
  | Err e => rfl
  | Ok pair =>
      rcases pair with ⟨token_state, acts⟩
      rfl

private theorem alt_token_receive_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {msg : ConCert.Examples.EIP20.EIP20Token.Msg}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (.tokenMsg msg)) =
      .Ok (new_state, new_acts)) :
    ∃ token_state token_acts,
      ConCert.Examples.EIP20.EIP20Token.receive chain ctx prev_state.token_state
          (some msg) = .Ok (token_state, token_acts) ∧
        new_state = { prev_state with token_state := token_state } ∧
        new_acts = token_acts := by
  unfold AltFix.receive receive_token at h
  cases htok :
      ConCert.Examples.EIP20.EIP20Token.receive chain ctx prev_state.token_state
        (some msg) with
  | Err e =>
      simp [htok] at h
  | Ok pair =>
      rcases pair with ⟨token_state, token_acts⟩
      simp [htok] at h
      rcases h with ⟨hstate, hacts⟩
      exact ⟨token_state, token_acts, rfl, hstate.symm, hacts.symm⟩

theorem try_transfer_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (transfer to_ amount)) =
      .Ok (new_state, new_acts)) :
    ConCert.Examples.EIP20.EIP20Token.transfer_balance_update_correct
      prev_state.token_state new_state.token_state ctx.ctx_from to_ amount =
        true := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_balance_correct htok

theorem try_transfer_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (transfer to_ amount)) =
      .Ok (new_state, new_acts)) :
    total_supply prev_state = total_supply new_state := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_preserves_total_supply htok

theorem try_transfer_preserves_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (transfer to_ amount)) =
      .Ok (new_state, new_acts)) :
    allowances prev_state = allowances new_state := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_preserves_allowances htok

theorem try_transfer_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {to_ account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (transfer to_ amount)) =
      .Ok (new_state, new_acts))
    (h_sender : account ≠ ctx.ctx_from) (h_receiver : account ≠ to_) :
    FMap.find account (balances prev_state) =
      FMap.find account (balances new_state) := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_preserves_other_balances
    htok h_sender h_receiver

theorem try_transfer_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (to_ : Base.Address)
    (amount : TokenValue) :
    (ctx.ctx_amount ≤ 0 ∧
        amount ≤ with_default 0 (FMap.find ctx.ctx_from (balances state))) ↔
      isOk (AltFix.receive chain ctx state (some (transfer to_ amount))) =
        true := by
  constructor
  · intro h
    have hok :=
      (ConCert.Examples.EIP20.EIP20Token.try_transfer_is_some
        state.token_state chain ctx to_ amount).mp (by
          simpa [balances] using h)
    unfold AltFix.receive receive_token
    simp [transfer]
    cases htok :
        ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
          (some (ConCert.Examples.EIP20.EIP20Token.Msg.transfer to_ amount)) <;>
      simp [htok, isOk] at hok ⊢
  · intro h
    have hok :
        isOk
          (ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
            (some (ConCert.Examples.EIP20.EIP20Token.Msg.transfer to_ amount))) =
          true := by
      unfold AltFix.receive receive_token at h
      simp [transfer] at h
      cases htok :
          ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
            (some (ConCert.Examples.EIP20.EIP20Token.Msg.transfer to_ amount)) <;>
        simp [htok, isOk] at h ⊢
    simpa [balances] using
      (ConCert.Examples.EIP20.EIP20Token.try_transfer_is_some
        state.token_state chain ctx to_ amount).mpr hok

theorem try_transfer_from_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state
      (some (transfer_from from_ to_ amount)) = .Ok (new_state, new_acts)) :
    ConCert.Examples.EIP20.EIP20Token.transfer_balance_update_correct
        prev_state.token_state new_state.token_state from_ to_ amount = true ∧
      ConCert.Examples.EIP20.EIP20Token.transfer_from_allowances_update_correct
        prev_state.token_state new_state.token_state from_ ctx.ctx_from amount =
          true := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_from_balance_correct htok

theorem try_transfer_from_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state
      (some (transfer_from from_ to_ amount)) = .Ok (new_state, new_acts)) :
    total_supply prev_state = total_supply new_state := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_from_preserves_total_supply htok

theorem try_transfer_from_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state
      (some (transfer_from from_ to_ amount)) = .Ok (new_state, new_acts))
    (h_from : account ≠ from_) (h_to : account ≠ to_) :
    FMap.find account (balances prev_state) =
      FMap.find account (balances new_state) := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_from_preserves_other_balances
    htok h_from h_to

theorem try_transfer_from_preserves_other_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state
      (some (transfer_from from_ to_ amount)) = .Ok (new_state, new_acts))
    (h_from : account ≠ from_) :
    FMap.find account (allowances prev_state) =
      FMap.find account (allowances new_state) := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_from_preserves_other_allowances
    htok h_from

theorem try_transfer_from_preserves_other_allowance
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {from_ to_ account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state
      (some (transfer_from from_ to_ amount)) = .Ok (new_state, new_acts))
    (h_delegate : account ≠ ctx.ctx_from) :
    get_allowance from_ account prev_state =
      get_allowance from_ account new_state := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_transfer_from_preserves_other_allowance
    htok h_delegate

theorem try_transfer_from_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (from_ to_ : Base.Address)
    (amount : TokenValue) :
    let get_allowance_ account :=
      FMap.find account
        (with_default
          (FMap.empty : FMap Base.Address TokenValue)
          (FMap.find from_ (allowances state)))
    (ctx.ctx_amount ≤ 0 ∧
        (FMap.find from_ (allowances state)).isSome = true ∧
        (get_allowance_ ctx.ctx_from).isSome = true ∧
        amount ≤ with_default 0 (FMap.find from_ (balances state)) ∧
        amount ≤ with_default 0 (get_allowance_ ctx.ctx_from)) ↔
      isOk
        (AltFix.receive chain ctx state
          (some (transfer_from from_ to_ amount))) = true := by
  dsimp
  constructor
  · intro h
    have hok :=
      (ConCert.Examples.EIP20.EIP20Token.try_transfer_from_is_some
        state.token_state chain ctx from_ to_ amount).mp (by
          simpa [balances, allowances] using h)
    unfold AltFix.receive receive_token
    simp [transfer_from]
    cases htok :
        ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
          (some
            (ConCert.Examples.EIP20.EIP20Token.Msg.transfer_from from_ to_ amount)) <;>
      simp [htok, isOk] at hok ⊢
  · intro h
    have hok :
        isOk
          (ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
            (some
              (ConCert.Examples.EIP20.EIP20Token.Msg.transfer_from from_ to_ amount))) =
          true := by
      unfold AltFix.receive receive_token at h
      simp [transfer_from] at h
      cases htok :
          ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
            (some
              (ConCert.Examples.EIP20.EIP20Token.Msg.transfer_from from_ to_ amount)) <;>
        simp [htok, isOk] at h ⊢
    simpa [balances, allowances] using
      (ConCert.Examples.EIP20.EIP20Token.try_transfer_from_is_some
        state.token_state chain ctx from_ to_ amount).mpr hok

theorem try_approve_allowance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (approve delegate amount)) =
      .Ok (new_state, new_acts)) :
    ConCert.Examples.EIP20.EIP20Token.approve_allowance_update_correct
      new_state.token_state ctx.ctx_from delegate amount = true := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_approve_allowance_correct htok

theorem try_approve_preserves_total_supply
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (approve delegate amount)) =
      .Ok (new_state, new_acts)) :
    total_supply prev_state = total_supply new_state := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_approve_preserves_total_supply htok

theorem try_approve_preserves_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (approve delegate amount)) =
      .Ok (new_state, new_acts)) :
    balances prev_state = balances new_state := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_approve_preserves_balances htok

theorem try_approve_preserves_other_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (approve delegate amount)) =
      .Ok (new_state, new_acts))
    (h_sender : account ≠ ctx.ctx_from) :
    FMap.find account (allowances prev_state) =
      FMap.find account (allowances new_state) := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_approve_preserves_other_allowances
    htok h_sender

theorem try_approve_preserves_other_allowance
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate account : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (approve delegate amount)) =
      .Ok (new_state, new_acts))
    (h_delegate : account ≠ delegate) :
    get_allowance ctx.ctx_from account prev_state =
      get_allowance ctx.ctx_from account new_state := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  exact ConCert.Examples.EIP20.EIP20Token.try_approve_preserves_other_allowance
    htok h_delegate

theorem try_approve_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) (delegate : Base.Address)
    (amount : TokenValue) :
    ctx.ctx_amount ≤ 0 ↔
      isOk (AltFix.receive chain ctx state (some (approve delegate amount))) =
        true := by
  constructor
  · intro h
    have hok :=
      (ConCert.Examples.EIP20.EIP20Token.try_approve_is_some
        state.token_state chain ctx delegate amount).mp h
    unfold AltFix.receive receive_token
    simp [approve]
    cases htok :
        ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
          (some (ConCert.Examples.EIP20.EIP20Token.Msg.approve delegate amount)) <;>
      simp [htok, isOk] at hok ⊢
  · intro h
    have hok :
        isOk
          (ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
            (some (ConCert.Examples.EIP20.EIP20Token.Msg.approve delegate amount))) =
          true := by
      unfold AltFix.receive receive_token at h
      simp [approve] at h
      cases htok :
          ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state
            (some (ConCert.Examples.EIP20.EIP20Token.Msg.approve delegate amount)) <;>
        simp [htok, isOk] at h ⊢
    exact (ConCert.Examples.EIP20.EIP20Token.try_approve_is_some
      state.token_state chain ctx delegate amount).mpr hok

theorem eip_only_changes_token_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {msg : ConCert.Examples.EIP20.EIP20Token.Msg}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (.tokenMsg msg)) =
      .Ok (new_state, new_acts)) :
    { prev_state with token_state := new_state.token_state } = new_state := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, hstate, _⟩
  subst hstate
  rfl

theorem eip20_not_payable
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {msg : ConCert.Examples.EIP20.EIP20Token.Msg}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (.tokenMsg msg)) =
      .Ok (new_state, new_acts)) :
    ctx.ctx_amount ≤ 0 := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, _, _⟩
  exact ConCert.Examples.EIP20.EIP20Token.EIP20_not_payable htok

theorem eip20_new_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {msg : ConCert.Examples.EIP20.EIP20Token.Msg}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (.tokenMsg msg)) =
      .Ok (new_state, new_acts)) :
    new_acts = [] := by
  rcases alt_token_receive_ok (Base := Base) h with
    ⟨token_state, token_acts, htok, _, hacts⟩
  rw [hacts]
  exact ConCert.Examples.EIP20.EIP20Token.EIP20_no_acts htok

private theorem without_actions_ok
    {T E : Type} {r : Result T E} {new_state : T}
    {new_acts : List (@ActionBody Base)}
    (h : without_actions (Base := Base) r = .Ok (new_state, new_acts)) :
    r = .Ok new_state ∧ new_acts = [] := by
  cases r with
  | Ok st =>
      simp [without_actions] at h
      exact ⟨by cases h.1; rfl, h.2⟩
  | Err e =>
      simp [without_actions] at h

private theorem alt_create_tokens_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts)) :
    try_create_tokens false ctx.ctx_from ctx.ctx_amount chain.current_slot
        prev_state = .Ok new_state ∧
      new_acts = [] := by
  unfold AltFix.receive receive_bat_original at h
  simpa using without_actions_ok (Base := Base) h

private theorem try_create_tokens_ok_shape
    {state new_state : @State Base} {sender : Base.Address}
    {payload : Amount} {slot : Nat}
    (h : try_create_tokens false sender payload slot state = .Ok new_state) :
    0 < payload ∧
      new_state =
        { state with
          token_state :=
            { total_supply :=
                total_supply state + payload.toNat * state.tokenExchangeRate,
              balances :=
                FMap.partial_alter
                  (fun balance =>
                    some
                      (with_default 0 balance +
                        payload.toNat * state.tokenExchangeRate))
                  sender (balances state),
              allowances := allowances state } } := by
  unfold try_create_tokens at h
  by_cases hbad :
      ((state.isFinalized = true ∨ slot < state.fundingStart) ∨
        state.fundingEnd < slot)
  · simp [hbad] at h
  · by_cases hpayload : payload <= 0
    · simp [hbad, hpayload] at h
    · let tokens := payload.toNat * state.tokenExchangeRate
      by_cases hcap : state.tokenCreationCap < total_supply state + tokens
      · simp [hbad, hpayload, tokens, hcap] at h
      · simp [hbad, hpayload, tokens, hcap] at h
        cases h
        exact ⟨lt_of_not_ge hpayload, rfl⟩

private theorem try_create_tokens_ok_requirements
    {state new_state : @State Base} {sender : Base.Address}
    {payload : Amount} {slot : Nat}
    (h : try_create_tokens false sender payload slot state = .Ok new_state) :
    0 < payload ∧
      state.isFinalized = false ∧
      state.fundingStart ≤ slot ∧
      slot ≤ state.fundingEnd ∧
      total_supply state + payload.toNat * state.tokenExchangeRate ≤
        state.tokenCreationCap := by
  unfold try_create_tokens at h
  by_cases hbad :
      ((state.isFinalized = true ∨ slot < state.fundingStart) ∨
        state.fundingEnd < slot)
  · simp [hbad] at h
  · by_cases hpayload : payload <= 0
    · simp [hbad, hpayload] at h
    · let tokens := payload.toNat * state.tokenExchangeRate
      by_cases hcap : state.tokenCreationCap < total_supply state + tokens
      · simp [hbad, hpayload, tokens, hcap] at h
      · refine ⟨lt_of_not_ge hpayload, ?_, ?_, ?_, ?_⟩
        · cases hfin : state.isFinalized
          · rfl
          · exfalso
            exact hbad (Or.inl (Or.inl hfin))
        · exact le_of_not_gt
            (fun hlt => hbad (Or.inl (Or.inr hlt)))
        · exact le_of_not_gt
            (fun hlt => hbad (Or.inr hlt))
        · exact le_of_not_gt (by simpa [tokens] using hcap)

theorem try_create_tokens_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts)) :
    with_default 0 (FMap.find ctx.ctx_from (balances prev_state)) =
      with_default 0 (FMap.find ctx.ctx_from (balances new_state)) -
        (ctx.ctx_amount.toNat * prev_state.tokenExchangeRate) := by
  rcases alt_create_tokens_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_create_tokens_ok_shape (Base := Base) hraw with ⟨_, hstate⟩
  subst hstate
  simp [balances, FMap.find_partial_alter, with_default, withDefault]

theorem try_create_tokens_total_supply_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts)) :
    total_supply prev_state +
        (ctx.ctx_amount.toNat * prev_state.tokenExchangeRate) =
      total_supply new_state := by
  rcases alt_create_tokens_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_create_tokens_ok_shape (Base := Base) hraw with ⟨_, hstate⟩
  subst hstate
  rfl

theorem try_create_tokens_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {account : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts))
    (h_account : account ≠ ctx.ctx_from) :
    FMap.find account (balances prev_state) =
      FMap.find account (balances new_state) := by
  rcases alt_create_tokens_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_create_tokens_ok_shape (Base := Base) hraw with ⟨_, hstate⟩
  subst hstate
  simp [balances,
    FMap.find_partial_alter_ne ctx.ctx_from account _ _ (Ne.symm h_account)]

theorem try_create_tokens_preserves_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts)) :
    allowances prev_state = allowances new_state := by
  rcases alt_create_tokens_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_create_tokens_ok_shape (Base := Base) hraw with ⟨_, hstate⟩
  subst hstate
  rfl

theorem try_create_tokens_only_change_token_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts)) :
    { prev_state with token_state := new_state.token_state } = new_state := by
  rcases alt_create_tokens_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_create_tokens_ok_shape (Base := Base) hraw with ⟨_, hstate⟩
  subst hstate
  rfl

theorem try_create_tokens_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts)) :
    new_acts = [] :=
  (alt_create_tokens_ok (Base := Base) h).2

theorem try_create_tokens_amount_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts)) :
    0 < ctx.ctx_amount := by
  rcases alt_create_tokens_ok (Base := Base) h with ⟨hraw, _⟩
  exact (try_create_tokens_ok_shape (Base := Base) hraw).1

theorem try_create_tokens_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) :
    (0 < ctx.ctx_amount ∧
        state.isFinalized = false ∧
        state.fundingStart ≤ chain.current_slot ∧
        chain.current_slot ≤ state.fundingEnd ∧
        total_supply state +
            ctx.ctx_amount.toNat * state.tokenExchangeRate ≤
          state.tokenCreationCap) ↔
      ∃ new_state new_acts,
        AltFix.receive chain ctx state (some .create_tokens) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro h
    rcases h with
      ⟨hAmount, hFinalized, hStart, hEnd, hCap⟩
    let tokens := ctx.ctx_amount.toNat * state.tokenExchangeRate
    let new_token_state : @ConCert.Examples.EIP20.EIP20Token.State Base :=
      { total_supply := total_supply state + tokens,
        balances :=
          FMap.partial_alter
            (fun balance => some (with_default 0 balance + tokens))
            ctx.ctx_from (balances state),
        allowances := allowances state }
    let new_state := { state with token_state := new_token_state }
    refine ⟨new_state, [], ?_⟩
    have hbad :
        ¬((state.isFinalized = true ∨
              chain.current_slot < state.fundingStart) ∨
            state.fundingEnd < chain.current_slot) := by
      rintro ((hfin | hlt) | hlt)
      · rw [hFinalized] at hfin
        cases hfin
      · exact (not_lt.mpr hStart) hlt
      · exact (not_lt.mpr hEnd) hlt
    have hpayload : ¬ ctx.ctx_amount ≤ 0 := not_le.mpr hAmount
    have hcap : ¬ state.tokenCreationCap < total_supply state + tokens :=
      not_lt.mpr hCap
    unfold AltFix.receive receive_bat_original try_create_tokens
    simp [hbad, hpayload, hcap, tokens, new_token_state, new_state,
      without_actions]
  · rintro ⟨new_state, new_acts, h⟩
    exact try_create_tokens_ok_requirements (Base := Base)
      (alt_create_tokens_ok (Base := Base) h).1

private theorem alt_finalize_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .finalize) =
      .Ok (new_state, new_acts)) :
    try_finalize true ctx.ctx_from chain.current_slot ctx.ctx_contract_balance
        prev_state = .Ok (new_state, new_acts) := by
  unfold AltFix.receive receive_bat_original at h
  by_cases hamount : ctx.ctx_amount > 0
  · simp [hamount] at h
  · simpa [hamount] using h

private theorem try_finalize_ok_shape
    {state new_state : @State Base} {sender : Base.Address}
    {slot : Nat} {contract_balance : Amount}
    {new_acts : List (@ActionBody Base)}
    (h : try_finalize true sender slot contract_balance state =
      .Ok (new_state, new_acts)) :
    new_state =
        { state with
          isFinalized := true,
          token_state :=
            { total_supply := total_supply state + state.initSupply,
              balances :=
                FMap.partial_alter
                  (fun balance =>
                    some (with_default 0 balance + state.initSupply))
                  state.batFundDeposit (balances state),
              allowances := allowances state } } ∧
      new_acts = [.act_transfer state.fundDeposit contract_balance] := by
  unfold try_finalize at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp at h
      rcases h with ⟨hstate, hacts⟩
      exact ⟨hstate.symm, hacts.symm⟩

private theorem try_finalize_ok_requirements
    {state new_state : @State Base} {sender : Base.Address}
    {slot : Nat} {contract_balance : Amount}
    {new_acts : List (@ActionBody Base)}
    (h : try_finalize true sender slot contract_balance state =
      .Ok (new_state, new_acts)) :
    state.isFinalized = false ∧
      sender = state.fundDeposit ∧
      state.tokenCreationMin ≤ total_supply state ∧
      (state.fundingEnd < slot ∨
        state.tokenCreationCap = total_supply state) := by
  unfold try_finalize at h
  split at h
  · simp at h
  · rename_i hnotBad
    split at h
    · simp at h
    · rename_i hnotEarly
      refine ⟨?_, ?_, ?_, ?_⟩
      · cases hfinal : state.isFinalized
        · rfl
        · exfalso
          apply hnotBad
          simp [hfinal]
      · have heqb : Base.address_eqb sender state.fundDeposit = true := by
          cases heq : Base.address_eqb sender state.fundDeposit
          · exfalso
            apply hnotBad
            simp [heq]
          · rfl
        exact (Base.address_eqb_spec _ _).mp heqb
      · exact le_of_not_gt
          (fun hlt => hnotBad (by simp [hlt]))
      · by_cases hslot : slot ≤ state.fundingEnd
        · right
          have heqb :
              (total_supply state == state.tokenCreationCap) = true := by
            cases heq : (total_supply state == state.tokenCreationCap)
            · exfalso
              apply hnotEarly
              simp [hslot, heq]
            · rfl
          have heq : total_supply state = state.tokenCreationCap := by
            simpa using heqb
          exact heq.symm
        · left
          exact Nat.lt_of_not_ge hslot

theorem try_finalize_isFinalized_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .finalize) =
      .Ok (new_state, new_acts)) :
    prev_state.isFinalized = false ∧ new_state.isFinalized = true := by
  have hraw := alt_finalize_ok (Base := Base) h
  have hshape := (try_finalize_ok_shape (Base := Base) hraw).1
  constructor
  · unfold try_finalize at hraw
    split at hraw
    · simp at hraw
    · rename_i hnotBad
      cases hfinal : prev_state.isFinalized
      · rfl
      · exfalso
        apply hnotBad
        simp [hfinal]
  · rw [hshape]

theorem try_finalize_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .finalize) =
      .Ok (new_state, new_acts)) :
    with_default 0
        (FMap.find prev_state.batFundDeposit (balances prev_state)) =
      with_default 0
          (FMap.find new_state.batFundDeposit (balances new_state)) -
        new_state.initSupply := by
  have hraw := alt_finalize_ok (Base := Base) h
  rw [(try_finalize_ok_shape (Base := Base) hraw).1]
  rw [ConCert.Examples.EIP20.EIP20Token.add_is_partial_alter_plus]
  simp [balances, FMap.find_add, with_default, withDefault]

theorem try_finalize_total_supply_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .finalize) =
      .Ok (new_state, new_acts)) :
    total_supply prev_state + prev_state.initSupply =
      total_supply new_state := by
  have hraw := alt_finalize_ok (Base := Base) h
  rw [(try_finalize_ok_shape (Base := Base) hraw).1]
  rfl

theorem try_finalize_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {account : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .finalize) =
      .Ok (new_state, new_acts))
    (h_account : account ≠ prev_state.batFundDeposit) :
    FMap.find account (balances prev_state) =
      FMap.find account (balances new_state) := by
  have hraw := alt_finalize_ok (Base := Base) h
  rw [(try_finalize_ok_shape (Base := Base) hraw).1]
  rw [ConCert.Examples.EIP20.EIP20Token.add_is_partial_alter_plus]
  simp [balances,
    FMap.find_add_ne prev_state.batFundDeposit account _ _ (Ne.symm h_account)]

theorem try_finalize_preserves_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .finalize) =
      .Ok (new_state, new_acts)) :
    allowances prev_state = allowances new_state := by
  have hraw := alt_finalize_ok (Base := Base) h
  rw [(try_finalize_ok_shape (Base := Base) hraw).1]
  rfl

theorem try_finalize_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .finalize) =
      .Ok (new_state, new_acts)) :
    new_acts = [.act_transfer prev_state.fundDeposit ctx.ctx_contract_balance] := by
  have hraw := alt_finalize_ok (Base := Base) h
  exact (try_finalize_ok_shape (Base := Base) hraw).2

theorem try_finalize_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) :
    (ctx.ctx_amount ≤ 0 ∧
        state.isFinalized = false ∧
        ctx.ctx_from = state.fundDeposit ∧
        state.tokenCreationMin ≤ total_supply state ∧
        (state.fundingEnd < chain.current_slot ∨
          state.tokenCreationCap = total_supply state)) ↔
      ∃ new_state new_acts,
        AltFix.receive chain ctx state (some .finalize) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro h
    rcases h with
      ⟨hAmount, hFinalized, hSender, hMin, hDone⟩
    let new_token_state : @ConCert.Examples.EIP20.EIP20Token.State Base :=
      { total_supply := total_supply state + state.initSupply,
        balances :=
          FMap.partial_alter
            (fun balance =>
              some (with_default 0 balance + state.initSupply))
            state.batFundDeposit (balances state),
        allowances := allowances state }
    let new_state :=
      { state with isFinalized := true, token_state := new_token_state }
    refine ⟨new_state,
      [.act_transfer state.fundDeposit ctx.ctx_contract_balance], ?_⟩
    have hamount : ¬ ctx.ctx_amount > 0 := not_lt.mpr hAmount
    have hbad :
        ¬(state.isFinalized ||
            !Base.address_eqb ctx.ctx_from state.fundDeposit ||
            decide (total_supply state < state.tokenCreationMin)) = true := by
      intro hbad
      rw [Bool.or_eq_true, Bool.or_eq_true] at hbad
      rcases hbad with (hfin | hsender) | hlt
      · rw [hFinalized] at hfin
        cases hfin
      · have heqb : Base.address_eqb ctx.ctx_from state.fundDeposit = true := by
          exact (Base.address_eqb_spec _ _).mpr hSender
        simp [heqb] at hsender
      · exact (not_lt.mpr hMin) (of_decide_eq_true hlt)
    have hearly :
        ¬(decide (chain.current_slot ≤ state.fundingEnd) &&
            !(total_supply state == state.tokenCreationCap)) = true := by
      intro hearly
      rw [Bool.and_eq_true] at hearly
      rcases hearly with ⟨hslotBool, hcapBool⟩
      rcases hDone with hslot | hcap
      · exact (not_lt.mpr (of_decide_eq_true hslotBool)) hslot
      · have hcapBool' :
            (total_supply state == state.tokenCreationCap) = true := by
          simp [hcap]
        simp [hcapBool'] at hcapBool
    unfold AltFix.receive receive_bat_original try_finalize
    simp [hamount, hbad, hearly, new_token_state, new_state]
  · rintro ⟨new_state, new_acts, h⟩
    have hraw := alt_finalize_ok (Base := Base) h
    have hreq := try_finalize_ok_requirements (Base := Base) hraw
    have hamount : ctx.ctx_amount ≤ 0 := by
      by_cases hgt : ctx.ctx_amount > 0
      · unfold AltFix.receive receive_bat_original at h
        simp [hgt] at h
      · exact le_of_not_gt hgt
    exact ⟨hamount, hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2⟩

private theorem alt_refund_ok
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .refund) =
      .Ok (new_state, new_acts)) :
    try_refund_alt ctx.ctx_from chain.current_slot prev_state =
      .Ok (new_state, new_acts) := by
  unfold AltFix.receive receive_bat_original at h
  by_cases hamount : ctx.ctx_amount > 0
  · simp [hamount] at h
  · simpa [hamount] using h

private theorem try_refund_ok_shape
    {state new_state : @State Base} {sender : Base.Address}
    {slot : Nat} {new_acts : List (@ActionBody Base)}
    (h : try_refund_alt sender slot state =
      .Ok (new_state, new_acts)) :
    ∃ sender_bats,
      FMap.find sender (balances state) = some sender_bats ∧
        sender_bats ≠ 0 ∧
        new_state =
          { state with
            token_state :=
              { total_supply :=
                  total_supply state - sender_bats +
                    sender_bats % state.tokenExchangeRate,
                balances :=
                  FMap.add sender
                    (sender_bats % state.tokenExchangeRate)
                    (balances state),
                allowances := allowances state } } ∧
        new_acts =
          [.act_transfer sender
            (Int.ofNat (sender_bats / state.tokenExchangeRate))] := by
  unfold try_refund_alt at h
  split at h
  · simp at h
  · cases hfind : FMap.find sender (balances state) with
    | none =>
        simp [hfind] at h
    | some sender_bats =>
        cases hzero : (sender_bats == 0)
        · simp [hfind, hzero] at h
          rcases h with ⟨hstate, hacts⟩
          have hne : sender_bats ≠ 0 := by
            intro hz
            subst hz
            simp at hzero
          exact ⟨sender_bats, rfl, hne, hstate.symm, hacts.symm⟩
        · simp [hfind, hzero] at h

private theorem try_refund_ok_requirements
    {state new_state : @State Base} {sender : Base.Address}
    {slot : Nat} {new_acts : List (@ActionBody Base)}
    (h : try_refund_alt sender slot state =
      .Ok (new_state, new_acts)) :
    state.isFinalized = false ∧
      state.fundingEnd < slot ∧
      total_supply state < state.tokenCreationMin ∧
      0 < with_default 0 (FMap.find sender (balances state)) := by
  unfold try_refund_alt at h
  split at h
  · simp at h
  · rename_i hnotBad
    cases hfind : FMap.find sender (balances state) with
    | none =>
        simp [hfind] at h
    | some sender_bats =>
        cases hzero : (sender_bats == 0)
        · simp [hfind, hzero] at h
          refine ⟨?_, ?_, ?_, ?_⟩
          · cases hfinal : state.isFinalized
            · rfl
            · exfalso
              apply hnotBad
              simp [hfinal]
          · exact Nat.lt_of_not_ge
              (fun hle => hnotBad (by simp [hle]))
          · exact Nat.lt_of_not_ge
              (fun hle => hnotBad (by simp [hle]))
          · have hne : sender_bats ≠ 0 := by
              intro hz
              subst hz
              simp at hzero
            simp [with_default, withDefault, Nat.pos_of_ne_zero hne]
        · simp [hfind, hzero] at h

theorem try_refund_balance_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .refund) =
      .Ok (new_state, new_acts)) :
    with_default 0 (FMap.find ctx.ctx_from (balances new_state)) =
      with_default 0 (FMap.find ctx.ctx_from (balances prev_state)) %
        prev_state.tokenExchangeRate := by
  have hraw := alt_refund_ok (Base := Base) h
  rcases try_refund_ok_shape (Base := Base) hraw with
    ⟨sender_bats, hfind, hne, hstate, hacts⟩
  subst hstate
  rw [hfind]
  simp [balances, FMap.find_add, with_default, withDefault]

theorem try_refund_total_supply_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .refund) =
      .Ok (new_state, new_acts)) :
    total_supply prev_state -
        with_default 0 (FMap.find ctx.ctx_from (balances prev_state)) +
        with_default 0 (FMap.find ctx.ctx_from (balances prev_state)) %
          prev_state.tokenExchangeRate =
      total_supply new_state := by
  have hraw := alt_refund_ok (Base := Base) h
  rcases try_refund_ok_shape (Base := Base) hraw with
    ⟨sender_bats, hfind, hne, hstate, hacts⟩
  subst hstate
  rw [hfind]
  rfl

theorem try_refund_preserves_other_balances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {account : Base.Address}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .refund) =
      .Ok (new_state, new_acts))
    (h_account : account ≠ ctx.ctx_from) :
    FMap.find account (balances prev_state) =
      FMap.find account (balances new_state) := by
  have hraw := alt_refund_ok (Base := Base) h
  rcases try_refund_ok_shape (Base := Base) hraw with
    ⟨sender_bats, hfind, hne, hstate, hacts⟩
  subst hstate
  simp [balances, FMap.find_add_ne ctx.ctx_from account _ _ (Ne.symm h_account)]

theorem try_refund_preserves_allowances
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .refund) =
      .Ok (new_state, new_acts)) :
    allowances prev_state = allowances new_state := by
  have hraw := alt_refund_ok (Base := Base) h
  rcases try_refund_ok_shape (Base := Base) hraw with
    ⟨sender_bats, hfind, hne, hstate, hacts⟩
  subst hstate
  rfl

theorem try_refund_only_change_token_state
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .refund) =
      .Ok (new_state, new_acts)) :
    { prev_state with token_state := new_state.token_state } = new_state := by
  have hraw := alt_refund_ok (Base := Base) h
  rcases try_refund_ok_shape (Base := Base) hraw with
    ⟨sender_bats, hfind, hne, hstate, hacts⟩
  subst hstate
  rfl

theorem try_refund_acts_correct
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .refund) =
      .Ok (new_state, new_acts)) :
    new_acts =
      [.act_transfer ctx.ctx_from
        (Int.ofNat
          (with_default 0
              (FMap.find ctx.ctx_from (balances prev_state)) /
            prev_state.tokenExchangeRate))] := by
  have hraw := alt_refund_ok (Base := Base) h
  rcases try_refund_ok_shape (Base := Base) hraw with
    ⟨sender_bats, hfind, hne, hstate, hacts⟩
  rw [hacts, hfind]
  simp [with_default, withDefault]

theorem try_refund_is_some
    (state : @State Base) (chain : Chain)
    (ctx : @ContractCallContext Base) :
    (ctx.ctx_amount ≤ 0 ∧
        state.isFinalized = false ∧
        state.fundingEnd < chain.current_slot ∧
        total_supply state < state.tokenCreationMin ∧
        0 < with_default 0 (FMap.find ctx.ctx_from (balances state))) ↔
      ∃ new_state new_acts,
        AltFix.receive chain ctx state (some .refund) =
          .Ok (new_state, new_acts) := by
  constructor
  · intro h
    rcases h with
      ⟨hAmount, hFinalized, hEnd, hMin, hBalance⟩
    have hamount : ¬ ctx.ctx_amount > 0 := not_lt.mpr hAmount
    have hbad :
        ¬(state.isFinalized ||
            decide (chain.current_slot ≤ state.fundingEnd) ||
            decide (state.tokenCreationMin ≤ total_supply state)) = true := by
      intro hbad
      rw [Bool.or_eq_true, Bool.or_eq_true] at hbad
      rcases hbad with (hfin | hend) | hmin
      · rw [hFinalized] at hfin
        cases hfin
      · exact (not_lt.mpr (of_decide_eq_true hend)) hEnd
      · exact (not_lt.mpr (of_decide_eq_true hmin)) hMin
    cases hfind : FMap.find ctx.ctx_from (balances state) with
    | none =>
        simp [hfind, with_default, withDefault] at hBalance
    | some sender_bats =>
        have hne : sender_bats ≠ 0 := by
          intro hz
          subst hz
          simp [hfind, with_default, withDefault] at hBalance
        have hzero : (sender_bats == 0) = false := by
          simp [hne]
        let remainder := sender_bats % state.tokenExchangeRate
        let new_token_state : @ConCert.Examples.EIP20.EIP20Token.State Base :=
          { total_supply := total_supply state - sender_bats + remainder,
            balances := FMap.add ctx.ctx_from remainder (balances state),
            allowances := allowances state }
        let new_state := { state with token_state := new_token_state }
        refine ⟨new_state,
          [.act_transfer ctx.ctx_from
            (Int.ofNat (sender_bats / state.tokenExchangeRate))], ?_⟩
        unfold AltFix.receive receive_bat_original try_refund_alt
        simp [hamount, hfind, hzero, remainder, new_token_state, new_state,
          hFinalized, hEnd, hMin]
  · rintro ⟨new_state, new_acts, h⟩
    have hraw := alt_refund_ok (Base := Base) h
    have hreq := try_refund_ok_requirements (Base := Base) hraw
    have hamount : ctx.ctx_amount ≤ 0 := by
      by_cases hgt : ctx.ctx_amount > 0
      · unfold AltFix.receive receive_bat_original at h
        simp [hgt] at h
      · exact le_of_not_gt hgt
    exact ⟨hamount, hreq.1, hreq.2.1, hreq.2.2.1,
      hreq.2.2.2⟩

private theorem alt_init_ok_shape
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base}
    (h : AltFix.init chain ctx setup = .Ok state) :
    state =
      mk_state setup
        (base_token_state 0 FMap.empty) := by
  unfold AltFix.init init_alt at h
  by_cases hvalid : valid_fixed_setup chain ctx setup false
  · simp [hvalid] at h
  · simp [hvalid] at h
    exact h.symm

theorem init_bat_balances_correct
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base}
    (h : AltFix.init chain ctx setup = .Ok state) :
    balances state = FMap.empty := by
  rw [alt_init_ok_shape (Base := Base) h]
  rfl

theorem init_other_balances_correct
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base} {account : Base.Address}
    (h : AltFix.init chain ctx setup = .Ok state)
    (h_account : account ≠ state.batFundDeposit) :
    with_default 0 (FMap.find account (balances state)) = 0 := by
  have hshape := alt_init_ok_shape (Base := Base) h
  subst hshape
  simp [mk_state, base_token_state, balances, with_default, withDefault,
    FMap.find_empty]

theorem init_allowances_correct
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base}
    (h : AltFix.init chain ctx setup = .Ok state) :
    allowances state = FMap.empty := by
  rw [alt_init_ok_shape (Base := Base) h]
  rfl

theorem init_isFinalized_correct
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base}
    (h : AltFix.init chain ctx setup = .Ok state) :
    state.isFinalized = false := by
  rw [alt_init_ok_shape (Base := Base) h]
  rfl

theorem init_total_supply_correct
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base}
    (h : AltFix.init chain ctx setup = .Ok state) :
    total_supply state = 0 := by
  rw [alt_init_ok_shape (Base := Base) h]
  rfl

theorem init_constants_correct
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base}
    (h : AltFix.init chain ctx setup = .Ok state) :
    state.fundDeposit = setup.fundDeposit_ ∧
      state.batFundDeposit = setup.batFundDeposit_ ∧
      state.fundingStart = setup.fundingStart_ ∧
      state.fundingEnd = setup.fundingEnd_ ∧
      state.tokenExchangeRate = setup.tokenExchangeRate_ ∧
      state.tokenCreationCap = setup.tokenCreationCap_ ∧
      state.tokenCreationMin = setup.tokenCreationMin_ ∧
      state.initSupply = setup.batFund := by
  rw [alt_init_ok_shape (Base := Base) h]
  simp [mk_state]

theorem try_approve_preserves_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {delegate : Base.Address}
    {amount : TokenValue} {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some (approve delegate amount)) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state = sum_balances new_state := by
  have hbalances := try_approve_preserves_balances (Base := Base) h
  unfold sum_balances ConCert.Examples.EIP20.EIP20Token.sum_balances
  simp [balances] at hbalances
  rw [hbalances]

theorem try_create_tokens_update_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .create_tokens) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state +
        (ctx.ctx_amount.toNat * prev_state.tokenExchangeRate) =
      sum_balances new_state := by
  rcases alt_create_tokens_ok (Base := Base) h with ⟨hraw, _⟩
  rcases try_create_tokens_ok_shape (Base := Base) hraw with
    ⟨_, hstate⟩
  let tokens := ctx.ctx_amount.toNat * prev_state.tokenExchangeRate
  subst hstate
  unfold sum_balances ConCert.Examples.EIP20.EIP20Token.sum_balances
  change
    ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum (balances prev_state) +
        tokens =
      ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum
        (FMap.partial_alter
          (fun balance => some (with_default 0 balance + tokens))
          ctx.ctx_from (balances prev_state))
  rw [ConCert.Examples.EIP20.EIP20Token.add_is_partial_alter_plus]
  cases hfind : FMap.find ctx.ctx_from (balances prev_state) with
  | none =>
      rw [ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum_add_new
        ctx.ctx_from (with_default 0 none + tokens)
        (balances prev_state) hfind]
      simp [with_default, withDefault]
      omega
  | some old =>
      rw [ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum_add_existing
        ctx.ctx_from old (with_default 0 (some old) + tokens)
        (balances prev_state) hfind]
      simp [with_default, withDefault]
      have hfind' :
          FMap.find ctx.ctx_from prev_state.token_state.balances =
            some old := by
        simpa [balances] using hfind
      have hold :
          old ≤
            ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum
              (balances prev_state) := by
        simpa [sum_balances, ConCert.Examples.EIP20.EIP20Token.sum_balances,
          ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum, balances, hfind',
          with_default, withDefault] using
          balance_le_sum_balances (Base := Base) ctx.ctx_from prev_state
      rw [← Nat.add_assoc, Nat.sub_add_cancel hold]

theorem try_finalize_preserves_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .finalize) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state + prev_state.initSupply =
      sum_balances new_state := by
  have hraw := alt_finalize_ok (Base := Base) h
  rw [(try_finalize_ok_shape (Base := Base) hraw).1]
  unfold sum_balances ConCert.Examples.EIP20.EIP20Token.sum_balances
  change
    ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum (balances prev_state) +
        prev_state.initSupply =
      ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum
        (FMap.partial_alter
          (fun balance =>
            some (with_default 0 balance + prev_state.initSupply))
          prev_state.batFundDeposit (balances prev_state))
  rw [ConCert.Examples.EIP20.EIP20Token.add_is_partial_alter_plus]
  cases hfind : FMap.find prev_state.batFundDeposit (balances prev_state) with
  | none =>
      rw [ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum_add_new
        prev_state.batFundDeposit
        (with_default 0 none + prev_state.initSupply)
        (balances prev_state) hfind]
      simp [with_default, withDefault]
      omega
  | some old =>
      rw [ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum_add_existing
        prev_state.batFundDeposit old
        (with_default 0 (some old) + prev_state.initSupply)
        (balances prev_state) hfind]
      simp [with_default, withDefault]
      have hfind' :
          FMap.find prev_state.batFundDeposit
              prev_state.token_state.balances =
            some old := by
        simpa [balances] using hfind
      have hold :
          old ≤
            ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum
              (balances prev_state) := by
        simpa [sum_balances, ConCert.Examples.EIP20.EIP20Token.sum_balances,
          ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum, balances, hfind',
          with_default, withDefault] using
          balance_le_sum_balances (Base := Base)
            prev_state.batFundDeposit prev_state
      rw [← Nat.add_assoc, Nat.sub_add_cancel hold]

theorem try_refund_update_balances_sum
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state (some .refund) =
      .Ok (new_state, new_acts)) :
    sum_balances prev_state =
      sum_balances new_state +
        with_default 0 (FMap.find ctx.ctx_from (balances prev_state)) -
        with_default 0 (FMap.find ctx.ctx_from (balances prev_state)) %
          prev_state.tokenExchangeRate := by
  have hraw := alt_refund_ok (Base := Base) h
  rcases try_refund_ok_shape (Base := Base) hraw with
    ⟨sender_bats, hfind, hne, hstate, hacts⟩
  subst hstate
  unfold sum_balances ConCert.Examples.EIP20.EIP20Token.sum_balances
  change
    ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum (balances prev_state) =
      ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum
          (FMap.add ctx.ctx_from
            (sender_bats % prev_state.tokenExchangeRate)
            (balances prev_state)) +
        with_default 0 (FMap.find ctx.ctx_from (balances prev_state)) -
        with_default 0 (FMap.find ctx.ctx_from (balances prev_state)) %
          prev_state.tokenExchangeRate
  rw [ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum_add_existing
    ctx.ctx_from sender_bats
      (sender_bats % prev_state.tokenExchangeRate)
      (balances prev_state) hfind]
  rw [hfind]
  simp [with_default, withDefault]
  have hfind' :
      FMap.find ctx.ctx_from prev_state.token_state.balances =
        some sender_bats := by
    simpa [balances] using hfind
  have hold :
      sender_bats ≤
        ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum (balances prev_state) := by
    simpa [sum_balances, ConCert.Examples.EIP20.EIP20Token.sum_balances,
      ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum, balances, hfind',
      with_default, withDefault] using
      balance_le_sum_balances (Base := Base) ctx.ctx_from prev_state
  let S := ConCert.Examples.EIP20.EIP20Token.fmap_nat_sum (balances prev_state)
  change
    S =
      S - sender_bats + sender_bats % prev_state.tokenExchangeRate +
          sender_bats -
        sender_bats % prev_state.tokenExchangeRate
  have holdS : sender_bats ≤ S := by
    simpa [S] using hold
  rw [Nat.add_right_comm
    (S - sender_bats)
    (sender_bats % prev_state.tokenExchangeRate)
    sender_bats]
  rw [Nat.sub_add_cancel holdS]
  rw [Nat.add_sub_cancel]

theorem init_preserves_balances_sum
    {state : @State Base} {chain : Chain} {ctx : @ContractCallContext Base}
    {setup : @Setup Base}
    (h : AltFix.init chain ctx setup = .Ok state) :
    sum_balances state = total_supply state := by
  rw [alt_init_ok_shape (Base := Base) h]
  unfold sum_balances ConCert.Examples.EIP20.EIP20Token.sum_balances
  rfl

theorem receive_preserves_constants
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    (h : AltFix.receive chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    prev_state.fundDeposit = new_state.fundDeposit ∧
      prev_state.batFundDeposit = new_state.batFundDeposit ∧
      prev_state.fundingStart = new_state.fundingStart ∧
      prev_state.fundingEnd = new_state.fundingEnd ∧
      prev_state.tokenExchangeRate = new_state.tokenExchangeRate ∧
      prev_state.tokenCreationCap = new_state.tokenCreationCap ∧
      prev_state.tokenCreationMin = new_state.tokenCreationMin ∧
      prev_state.initSupply = new_state.initSupply := by
  cases msg with
  | none =>
      unfold AltFix.receive receive_bat_original at h
      simp at h
  | some msg =>
      cases msg with
      | tokenMsg token_msg =>
          have hchange := eip_only_changes_token_state (Base := Base) h
          rw [← hchange]
          simp
      | create_tokens =>
          have hchange := try_create_tokens_only_change_token_state
            (Base := Base) h
          rw [← hchange]
          simp
      | finalize =>
          have hraw := alt_finalize_ok (Base := Base) h
          rw [(try_finalize_ok_shape (Base := Base) hraw).1]
          simp
      | refund =>
          have hchange := try_refund_only_change_token_state
            (Base := Base) h
          rw [← hchange]
          simp

theorem constants_are_constant
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (AltFix.contract :
            @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))) :
    ∃ deploy_info cstate,
      deployment_info (@Setup Base) trace caddr = some deploy_info ∧
        @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
          some cstate ∧
        (let setup := deploy_info.deployment_setup
         cstate.fundDeposit = setup.fundDeposit_ ∧
          cstate.batFundDeposit = setup.batFundDeposit_ ∧
          cstate.fundingStart = setup.fundingStart_ ∧
          cstate.fundingEnd = setup.fundingEnd_ ∧
          cstate.tokenExchangeRate = setup.tokenExchangeRate_ ∧
          cstate.tokenCreationCap = setup.tokenCreationCap_ ∧
          cstate.tokenCreationMin = setup.tokenCreationMin_ ∧
          cstate.initSupply = setup.batFund) := by
  let Q : @DeploymentInfo Base (@Setup Base) → @State Base → Prop :=
    fun deploy_info cstate =>
      let setup := deploy_info.deployment_setup
      cstate.fundDeposit = setup.fundDeposit_ ∧
        cstate.batFundDeposit = setup.batFundDeposit_ ∧
        cstate.fundingStart = setup.fundingStart_ ∧
        cstate.fundingEnd = setup.fundingEnd_ ∧
        cstate.tokenExchangeRate = setup.tokenExchangeRate_ ∧
        cstate.tokenCreationCap = setup.tokenCreationCap_ ∧
        cstate.tokenCreationMin = setup.tokenCreationMin_ ∧
        cstate.initSupply = setup.batFund
  obtain ⟨deploy_info, cstate, hdep, hstate, hQ⟩ :=
    lift_dep_info_contract_state_prop
      (contract :=
        (AltFix.contract :
          @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _))
      (Q := Q)
      bstate caddr trace
      (by
        intro chain ctx setup result hinit
        exact init_constants_correct (Base := Base)
          (state := result) (chain := chain) (ctx := ctx)
          (setup := setup) hinit)
      (by
        intro chain ctx cstate msg new_cstate acts dep hQ hreceive
        rcases hQ with
          ⟨hfund, hbat, hstart, hend, hrate, hcap, hmin, hsupply⟩
        rcases receive_preserves_constants (Base := Base) hreceive with
          ⟨hfund', hbat', hstart', hend', hrate', hcap', hmin', hsupply'⟩
        exact
          ⟨hfund'.symm.trans hfund,
           hbat'.symm.trans hbat,
           hstart'.symm.trans hstart,
           hend'.symm.trans hend,
           hrate'.symm.trans hrate,
           hcap'.symm.trans hcap,
           hmin'.symm.trans hmin,
           hsupply'.symm.trans hsupply⟩)
      hdeployed
  exact ⟨deploy_info, cstate, hdep, hstate, hQ⟩

theorem final_is_final
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    (h_final : prev_state.isFinalized = true)
    (h : AltFix.receive chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    new_state.isFinalized = true := by
  cases msg with
  | none =>
      unfold AltFix.receive receive_bat_original at h
      simp at h
  | some msg =>
      cases msg with
      | tokenMsg token_msg =>
          have hchange := eip_only_changes_token_state (Base := Base) h
          rw [← hchange]
          exact h_final
      | create_tokens =>
          have hchange := try_create_tokens_only_change_token_state
            (Base := Base) h
          rw [← hchange]
          exact h_final
      | finalize =>
          exact (try_finalize_isFinalized_correct (Base := Base) h).2
      | refund =>
          have hchange := try_refund_only_change_token_state
            (Base := Base) h
          rw [← hchange]
          exact h_final

theorem receive_total_supply_increasing
    {prev_state new_state : @State Base} {chain : Chain}
    {ctx : @ContractCallContext Base} {msg : Option Msg}
    {new_acts : List (@ActionBody Base)}
    (hfunding :
      chain.current_slot ≤ prev_state.fundingEnd ∨
        prev_state.tokenCreationMin ≤ total_supply prev_state)
    (h : AltFix.receive chain ctx prev_state msg = .Ok (new_state, new_acts)) :
    total_supply prev_state ≤ total_supply new_state := by
  cases msg with
  | none =>
      unfold AltFix.receive receive_bat_original at h
      simp at h
  | some msg =>
      cases msg with
      | tokenMsg token_msg =>
          cases token_msg with
          | transfer to_ amount =>
              exact le_of_eq
                (try_transfer_preserves_total_supply (Base := Base) h)
          | transfer_from from_ to_ amount =>
              exact le_of_eq
                (try_transfer_from_preserves_total_supply (Base := Base) h)
          | approve delegate amount =>
              exact le_of_eq
                (try_approve_preserves_total_supply (Base := Base) h)
      | create_tokens =>
          have hsupply :=
            try_create_tokens_total_supply_correct (Base := Base) h
          rw [← hsupply]
          exact Nat.le_add_right _ _
      | finalize =>
          have hsupply := try_finalize_total_supply_correct (Base := Base) h
          rw [← hsupply]
          exact Nat.le_add_right _ _
      | refund =>
          have hreq :=
            (try_refund_is_some (Base := Base) prev_state chain ctx).mpr
              ⟨new_state, new_acts, h⟩
          rcases hreq with
            ⟨_, _, hafterEnd, hbelowMin, _⟩
          rcases hfunding with hactive | hgoal
          · exact False.elim ((not_lt.mpr hactive) hafterEnd)
          · exact False.elim ((not_lt.mpr hgoal) hbelowMin)

end AltFixCorrect

end ConCert.Examples.BAT
