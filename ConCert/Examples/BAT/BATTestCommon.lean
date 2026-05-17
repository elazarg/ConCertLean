/- Port of examples/bat/BATTestCommon.v over the local-chain backend. -/

import ConCert.Examples.BAT.BATGens

namespace ConCert.Examples.BAT.TestCommon

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ChainedList
open ConCert.Execution.Containers
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.BAT

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction
abbrev TestLocalChainBuilder := ConCert.Execution.Test.TraceGens.TestLocalChainBuilder

local instance : ChainBase := TestBase

def contract_base_addr : TestAddress := Gens.bat_contract_addr
def ethFund : TestAddress := Gens.fund_addr
def batFund : TestAddress := Gens.bat_fund_addr
def initSupply_ : Nat := 20
def exchangeRate_ : Nat := 3

def get_chain_finalized (cb : TestLocalChainBuilder) : Bool :=
  match Gens.get_bat_state cb with
  | some state => state.isFinalized
  | none => true

def get_chain_height (cb : TestLocalChainBuilder) : Nat :=
  cb.lcb_lc.lc_height

def action_is_msg (p : @Msg TestBase → Bool) (action : TestAction) : Bool :=
  match action.act_body with
  | .act_call to_ _ msg =>
      if TestBase.address_eqb to_ contract_base_addr then
        match (deserialize msg : Option (@Msg TestBase)) with
        | some m => p m
        | none => false
      else
        false
  | _ => false

def action_is_finalize (action : TestAction) : Bool :=
  action_is_msg (fun m => match m with | .finalize => true | _ => false) action

def action_is_refund (action : TestAction) : Bool :=
  action_is_msg (fun m => match m with | .refund => true | _ => false) action

def get_last_funding_state {fromState toState : @ChainState TestBase}
    (trace : ChainTrace fromState toState) (default : @ChainState TestBase) :
    @ChainState TestBase :=
  (trace_states_step_action trace).foldl
    (fun acc entry =>
      let (act, _newActs, prevState, _nextState) := entry
      if action_is_finalize act || action_is_refund act then
        prevState
      else
        acc)
    default

def get_chain_tokens (cb : TestLocalChainBuilder) : TokenValue :=
  let cs := get_last_funding_state cb.lcb_trace empty_state
  match ConCert.Execution.Test.TestUtils.get_contract_state
      (Base := TestBase) (S := @State TestBase)
      cs.toEnvironment contract_base_addr with
  | some state => total_supply state
  | none => 0

def fmap_subseteqb {A B : Type} [Ord A] [LawfulOrd A]
    (eqb : B → B → Bool) (m m' : FMap A B) : Bool :=
  (FMap.elements m).all
    (fun elem =>
      match FMap.find elem.1 m' with
      | some v => eqb elem.2 v
      | none => false)

def fmap_eqb {A B : Type} [Ord A] [LawfulOrd A]
    (eqb : B → B → Bool) (m m' : FMap A B) : Bool :=
  fmap_subseteqb eqb m m' && fmap_subseteqb eqb m' m

def remove_keys {A B : Type} [Ord A] [LawfulOrd A]
    (keys : List A) (m : FMap A B) : FMap A B :=
  keys.foldl (fun acc key => FMap.remove key acc) m

def fmap_filter_eqb {A B : Type} [Ord A] [LawfulOrd A]
    (excluded : List A) (eqb : B → B → Bool) (m m' : FMap A B) : Bool :=
  fmap_eqb eqb (remove_keys excluded m) (remove_keys excluded m')

def get_balance (state : @State TestBase) (addr : TestAddress) : TokenValue :=
  (FMap.find addr (balances state)).getD 0

def msg_is_eip_msg (_state : @State TestBase) : @Msg TestBase → Bool
  | .tokenMsg _ => true
  | _ => false

def msg_is_transfer (_state : @State TestBase) : @Msg TestBase → Bool
  | .tokenMsg (.transfer _ _) => true
  | _ => false

def msg_is_transfer_from (_state : @State TestBase) : @Msg TestBase → Bool
  | .tokenMsg (.transfer_from _ _ _) => true
  | _ => false

def msg_is_approve (_state : @State TestBase) : @Msg TestBase → Bool
  | .tokenMsg (.approve _ _) => true
  | _ => false

def msg_is_create_tokens (_state : @State TestBase) : @Msg TestBase → Bool
  | .create_tokens => true
  | _ => false

def msg_is_finalize (_state : @State TestBase) : @Msg TestBase → Bool
  | .finalize => true
  | _ => false

def msg_is_refund (_state : @State TestBase) : @Msg TestBase → Bool
  | .refund => true
  | _ => false

def amount_is_zero
    (_chain : Chain) (ctx : @ContractCallContext TestBase)
    (_old_state : @State TestBase) (_msg : @Msg TestBase)
    (_result_opt : Option (@State TestBase × List (@ActionBody TestBase))) :
    Checker :=
  checker (ctx.ctx_amount == 0)

def amount_is_positive
    (_chain : Chain) (ctx : @ContractCallContext TestBase)
    (_old_state : @State TestBase) (_msg : @Msg TestBase)
    (_result_opt : Option (@State TestBase × List (@ActionBody TestBase))) :
    Checker :=
  checker (0 < ctx.ctx_amount)

def produces_no_actions
    (_chain : Chain) (_ctx : @ContractCallContext TestBase)
    (_old_state : @State TestBase) (_msg : @Msg TestBase)
    (result_opt : Option (@State TestBase × List (@ActionBody TestBase))) :
    Checker :=
  match result_opt with
  | some (_, []) => checker true
  | _ => checker false

def produces_one_action
    (_chain : Chain) (_ctx : @ContractCallContext TestBase)
    (_old_state : @State TestBase) (_msg : @Msg TestBase)
    (result_opt : Option (@State TestBase × List (@ActionBody TestBase))) :
    Checker :=
  match result_opt with
  | some (_, [_]) => checker true
  | _ => checker false

def first_queued_call_msg (cs : @ChainState TestBase) :
    Option (TestAddress × @Msg TestBase) :=
  match cs.chain_state_queue with
  | [] => none
  | act :: _ =>
      match act.act_body with
      | .act_call _ _ ser_msg =>
          match (deserialize ser_msg : Option (@Msg TestBase)) with
          | some msg => some (act.act_from, msg)
          | none => none
      | _ => none

def no_transfers_from_bat_fund (cs : @ChainState TestBase) : Bool :=
  match first_queued_call_msg cs with
  | some (from_, .tokenMsg (.transfer _ _)) =>
      !(TestBase.address_eqb from_ batFund)
  | some (_, .tokenMsg (.transfer_from from_ _ _)) =>
      !(TestBase.address_eqb from_ batFund)
  | _ => true

def no_batfund_create_tokens (cs : @ChainState TestBase) : Bool :=
  match first_queued_call_msg cs with
  | some (from_, .create_tokens) => !(TestBase.address_eqb from_ batFund)
  | _ => true

def no_transfers_to_batfund (cs : @ChainState TestBase) : Bool :=
  match first_queued_call_msg cs with
  | some (_, .tokenMsg (.transfer to_ _)) =>
      !(TestBase.address_eqb to_ batFund)
  | some (_, .tokenMsg (.transfer_from _ to_ _)) =>
      !(TestBase.address_eqb to_ batFund)
  | _ => true

def is_fully_refunded (cs : @ChainState TestBase) : Bool :=
  let contract_balance := cs.env_account_balances contract_base_addr
  match ConCert.Execution.Test.TestUtils.get_contract_state
      (Base := TestBase) (S := @State TestBase)
      cs.toEnvironment contract_base_addr with
  | some state =>
      !state.isFinalized &&
        state.fundingEnd < cs.current_slot &&
        contract_balance == 0
  | none => false

def only_transfers_modulo_exchange_rate (cs : @ChainState TestBase) : Bool :=
  match first_queued_call_msg cs with
  | some (_, .tokenMsg (.transfer _ amount)) =>
      amount % exchangeRate_ == 0
  | some (_, .tokenMsg (.transfer_from _ _ amount)) =>
      amount % exchangeRate_ == 0
  | _ => true

def funding_period_not_over
    (setup : @Setup TestBase) (cb : TestLocalChainBuilder) : Bool :=
  let current_slot := (lc_to_env AddrSize cb.lcb_lc).current_slot + 1
  current_slot ≤ setup.fundingEnd_

def funding_period_non_empty (setup : @Setup TestBase) : Bool :=
  setup.fundingStart_ ≤ setup.fundingEnd_

def initial_supply_le_cap (setup : @Setup TestBase) : Bool :=
  setup.batFund ≤ setup.tokenCreationCap_

def exchange_rate_non_zero (setup : @Setup TestBase) : Bool :=
  0 < setup.tokenExchangeRate_

def is_finalized (cs : @ChainState TestBase) : Bool :=
  match ConCert.Execution.Test.TestUtils.get_contract_state
      (Base := TestBase) (S := @State TestBase)
      cs.toEnvironment contract_base_addr with
  | some state => state.isFinalized
  | none => false

end ConCert.Examples.BAT.TestCommon
