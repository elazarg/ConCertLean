/- Port of examples/bat/BATCommon.v, BAT.v, BATFixed.v, and BATAltFix.v
for executable contract behavior. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Examples.EIP20.EIP20Token
import ConCert.Utils.Extras

set_option maxHeartbeats 800000

namespace ConCert.Examples.BAT

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Utils.Extras

variable [Base : ChainBase]

abbrev TokenValue : Type := ConCert.Examples.EIP20.EIP20Token.TokenValue

inductive Msg where
  | tokenMsg (msg : ConCert.Examples.EIP20.EIP20Token.Msg)
  | create_tokens
  | finalize
  | refund
  deriving Serializable

structure State where
  token_state : @ConCert.Examples.EIP20.EIP20Token.State Base
  initSupply : Nat
  fundDeposit : Base.Address
  batFundDeposit : Base.Address
  isFinalized : Bool
  fundingStart : Nat
  fundingEnd : Nat
  tokenExchangeRate : Nat
  tokenCreationCap : Nat
  tokenCreationMin : Nat
  deriving Serializable

structure Setup where
  batFund : Nat
  fundDeposit_ : Base.Address
  batFundDeposit_ : Base.Address
  fundingStart_ : Nat
  fundingEnd_ : Nat
  tokenExchangeRate_ : Nat
  tokenCreationCap_ : Nat
  tokenCreationMin_ : Nat
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

def total_supply (state : @State Base) : Nat := state.token_state.total_supply
def balances (state : @State Base) := state.token_state.balances
def allowances (state : @State Base) := state.token_state.allowances

def transfer (to_ : Base.Address) (amount : TokenValue) : Msg :=
  .tokenMsg (.transfer to_ amount)

def transfer_from
    (from_ to_ : Base.Address) (amount : TokenValue) : Msg :=
  .tokenMsg (.transfer_from from_ to_ amount)

def approve (delegate : Base.Address) (amount : TokenValue) : Msg :=
  .tokenMsg (.approve delegate amount)

def base_token_state (initial_supply : Nat)
    (initial_balances : AddressMap.AddrMap (Base := Base) Nat) :
    @ConCert.Examples.EIP20.EIP20Token.State Base :=
  { total_supply := initial_supply,
    balances := initial_balances,
    allowances := FMap.empty }

def mk_state
    (setup : @Setup Base) (token_state : @ConCert.Examples.EIP20.EIP20Token.State Base) :
    @State Base :=
  { token_state := token_state,
    initSupply := setup.batFund,
    fundDeposit := setup.fundDeposit_,
    batFundDeposit := setup.batFundDeposit_,
    isFinalized := false,
    fundingStart := setup.fundingStart_,
    fundingEnd := setup.fundingEnd_,
    tokenExchangeRate := setup.tokenExchangeRate_,
    tokenCreationCap := setup.tokenCreationCap_,
    tokenCreationMin := setup.tokenCreationMin_ }

def valid_fixed_setup
    (chain : Chain) (ctx : @ContractCallContext Base) (setup : @Setup Base)
    (check_bat_fund_cap : Bool) : Bool :=
  (setup.fundingEnd_ <= setup.fundingStart_) ||
    (setup.fundingStart_ < chain.current_slot) ||
    (setup.tokenCreationCap_ < setup.tokenCreationMin_) ||
    (check_bat_fund_cap && setup.tokenCreationCap_ < setup.batFund) ||
    (setup.tokenExchangeRate_ == 0) ||
    (setup.tokenCreationCap_ - setup.tokenCreationMin_ < setup.tokenExchangeRate_) ||
    Base.address_eqb setup.batFundDeposit_ ctx.ctx_contract_address ||
    Base.address_eqb setup.fundDeposit_ ctx.ctx_contract_address

def init_original
    (_chain : Chain) (_ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  let token_state :=
    base_token_state setup.batFund
      (FMap.add setup.batFundDeposit_ setup.batFund FMap.empty)
  .Ok (mk_state setup token_state)

def init_fixed
    (chain : Chain) (ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  if valid_fixed_setup chain ctx setup true then
    .Err default_error
  else
    init_original chain ctx setup

def init_alt
    (chain : Chain) (ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  if valid_fixed_setup chain ctx setup false then
    .Err default_error
  else
    .Ok (mk_state setup (base_token_state 0 FMap.empty))

def try_create_tokens
    (reject_bat_fund_sender : Bool) (sender : Base.Address)
    (sender_payload : Amount) (current_slot : Nat) (state : @State Base) :
    Result (@State Base) Error :=
  if state.isFinalized ||
      current_slot < state.fundingStart ||
      state.fundingEnd < current_slot ||
      (reject_bat_fund_sender && Base.address_eqb sender state.batFundDeposit) then
    .Err default_error
  else if sender_payload <= 0 then
    .Err default_error
  else
    let tokens := sender_payload.toNat * state.tokenExchangeRate
    let checkedSupply := total_supply state + tokens
    if state.tokenCreationCap < checkedSupply then
      .Err default_error
    else
      let new_token_state : @ConCert.Examples.EIP20.EIP20Token.State Base :=
        { total_supply := checkedSupply,
          balances :=
            FMap.partial_alter
              (fun balance => some (with_default 0 balance + tokens))
              sender (balances state),
          allowances := allowances state }
      .Ok { state with token_state := new_token_state }

def try_refund_original
    (reject_bat_fund_sender : Bool) (sender : Base.Address)
    (current_slot : Nat) (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  if state.isFinalized ||
      current_slot <= state.fundingEnd ||
      state.tokenCreationMin <= total_supply state ||
      (reject_bat_fund_sender && Base.address_eqb sender state.batFundDeposit) then
    .Err default_error
  else
    match FMap.find sender (balances state) with
    | none => .Err default_error
    | some sender_bats =>
        if sender_bats == 0 then
          .Err default_error
        else
          let new_total_supply := total_supply state - sender_bats
          let amount_to_send := Int.ofNat (sender_bats / state.tokenExchangeRate)
          let new_token_state : @ConCert.Examples.EIP20.EIP20Token.State Base :=
            { total_supply := new_total_supply,
              balances := FMap.add sender 0 (balances state),
              allowances := allowances state }
          let new_state := { state with token_state := new_token_state }
          .Ok (new_state, [.act_transfer sender amount_to_send])

def try_refund_alt
    (sender : Base.Address) (current_slot : Nat) (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  if state.isFinalized ||
      current_slot <= state.fundingEnd ||
      state.tokenCreationMin <= total_supply state then
    .Err default_error
  else
    match FMap.find sender (balances state) with
    | none => .Err default_error
    | some sender_bats =>
        if sender_bats == 0 then
          .Err default_error
        else
          let remainder := sender_bats % state.tokenExchangeRate
          let amount_to_send := Int.ofNat (sender_bats / state.tokenExchangeRate)
          let new_total_supply := total_supply state - sender_bats + remainder
          let new_token_state : @ConCert.Examples.EIP20.EIP20Token.State Base :=
            { total_supply := new_total_supply,
              balances := FMap.add sender remainder (balances state),
              allowances := allowances state }
          let new_state := { state with token_state := new_token_state }
          .Ok (new_state, [.act_transfer sender amount_to_send])

def try_finalize
    (mint_initial_supply : Bool) (sender : Base.Address) (current_slot : Nat)
    (contract_balance : Amount) (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  if state.isFinalized ||
      !(Base.address_eqb sender state.fundDeposit) ||
      total_supply state < state.tokenCreationMin then
    .Err default_error
  else if current_slot <= state.fundingEnd &&
      !(total_supply state == state.tokenCreationCap) then
    .Err default_error
  else
    let token_state :=
      if mint_initial_supply then
        { total_supply := total_supply state + state.initSupply,
          balances :=
            FMap.partial_alter
              (fun balance => some (with_default 0 balance + state.initSupply))
              state.batFundDeposit (balances state),
          allowances := allowances state }
      else
        state.token_state
    .Ok
      ({ state with isFinalized := true, token_state := token_state },
        [.act_transfer state.fundDeposit contract_balance])

def receive_bat_original
    (reject_bat_fund_sender : Bool) (mint_initial_supply : Bool)
    (refund_alt : Bool) (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let sender := ctx.ctx_from
  let slot := chain.current_slot
  match maybe_msg with
  | some .create_tokens =>
      without_actions (Base := Base)
        (try_create_tokens reject_bat_fund_sender sender ctx.ctx_amount slot state)
  | some .refund =>
      if ctx.ctx_amount > 0 then
        .Err default_error
      else if refund_alt then
        try_refund_alt sender slot state
      else
        try_refund_original reject_bat_fund_sender sender slot state
  | some .finalize =>
      if ctx.ctx_amount > 0 then
        .Err default_error
      else
        try_finalize mint_initial_supply sender slot ctx.ctx_contract_balance state
  | _ =>
      .Err default_error

def receive_token
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (msg : ConCert.Examples.EIP20.EIP20Token.Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match ConCert.Examples.EIP20.EIP20Token.receive chain ctx state.token_state (some msg) with
  | .Err e => .Err e
  | .Ok (token_state, acts) => .Ok ({ state with token_state := token_state }, acts)

namespace Original

def init := @init_original

def receive
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match maybe_msg with
  | some (.tokenMsg msg) => receive_token chain ctx state msg
  | _ => receive_bat_original false false false chain ctx state maybe_msg

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init_original, receive := receive }

end Original

namespace Fixed

def init := @init_fixed

def receive
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match maybe_msg with
  | some (.tokenMsg msg) =>
      if !state.isFinalized then .Err default_error
      else receive_token chain ctx state msg
  | _ => receive_bat_original true false false chain ctx state maybe_msg

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init_fixed, receive := receive }

end Fixed

namespace AltFix

def init := @init_alt

def receive
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match maybe_msg with
  | some (.tokenMsg msg) => receive_token chain ctx state msg
  | _ => receive_bat_original false true true chain ctx state maybe_msg

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init_alt, receive := receive }

end AltFix

def get_balance (addr : Base.Address) (state : @State Base) : Nat :=
  with_default 0 (FMap.find addr state.token_state.balances)

def get_allowance
    (owner spender : Base.Address) (state : @State Base) : Nat :=
  ConCert.Examples.EIP20.EIP20Token.get_allowance state.token_state owner spender

def sum_balances (state : @State Base) : Nat :=
  ConCert.Examples.EIP20.EIP20Token.sum_balances state.token_state

end ConCert.Examples.BAT
