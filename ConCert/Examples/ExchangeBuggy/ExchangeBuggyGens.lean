/- Port of examples/exchangeBuggy/ExchangeBuggyGens.v over the local-chain backend. -/

import ConCert.Execution.Test.TraceGens
import ConCert.Examples.ExchangeBuggy.ExchangeBuggy

namespace ConCert.Examples.ExchangeBuggy.Gens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.ExchangeBuggy

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction
abbrev TestLocalChainBuilder := ConCert.Execution.Test.TraceGens.TestLocalChainBuilder
abbrev TestAddBlockError := ConCert.Execution.Test.TraceGens.TestAddBlockError

local instance : ChainBase := TestBase

def exchange_token_id : ConCert.Examples.FA2.TokenId := 0
def creator_addr : TestAddress := fixedUser10
def person_1 : TestAddress := fixedUser11
def person_2 : TestAddress := fixedLocalAddress 12 (by decide)
def fa2_caddr : TestAddress := fixedContractBase
def exchange_caddr : TestAddress :=
  fixedLocalAddress (ConCert.Execution.Test.TestUtils.ContractAddrBase + 1)
    (by decide)
def exploit_caddr : TestAddress :=
  fixedLocalAddress (ConCert.Execution.Test.TestUtils.ContractAddrBase + 2)
    (by decide)

def policy_all : ConCert.Examples.FA2.PermissionsDescriptor :=
  { descr_self := .self_transfer_permitted,
    descr_operator := .operator_transfer_permitted,
    descr_sender := .owner_no_op,
    descr_receiver := .owner_no_op,
    descr_custom := none }

def token_metadata_0 : ConCert.Examples.FA2.TokenMetadata :=
  { metadata_token_id := exchange_token_id, metadata_decimals := 8 }

def token_setup : @ConCert.Examples.FA2.Setup TestBase :=
  { transfer_hook_addr_ := none,
    setup_total_supply := [],
    setup_tokens := FMap.add exchange_token_id token_metadata_0 FMap.empty,
    initial_permission_policy := policy_all }

def exchange_setup : @Setup TestBase :=
  { fa2_caddr_ := fa2_caddr }

def exchange_other_msg (msg : @ExchangeMsg TestBase) : @Msg TestBase :=
  .other_msg msg

def add_operator_all (owner operator : TestAddress) :
    ConCert.Examples.FA2.OperatorParam :=
  { op_param_owner := owner,
    op_param_operator := operator,
    op_param_tokens := .all_tokens }

def fa2_call (caller : TestAddress) (amount : Amount)
    (msg : @ConCert.Examples.FA2.Msg TestBase) : TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call fa2_caddr amount (serialize msg) }

def exchange_call (caller : TestAddress) (amount : Amount) (msg : @Msg TestBase) :
    TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call exchange_caddr amount (serialize msg) }

def initial_exchange_header : @BlockHeader TestBase :=
  nextBlockHeader (lc_initial AddrSize) creator_addr 200

def initial_exchange_actions
    (exploit_contract :
      @Contract TestBase Unit ConCert.Examples.FA2.FA2TokenSender Nat Unit
        _ _ _ _) : List TestAction :=
  [ transferAction creator_addr person_1 10,
    { act_origin := creator_addr,
      act_from := creator_addr,
      act_body := create_deployment 0
        (ConCert.Examples.FA2.contract (Base := TestBase)) token_setup },
    { act_origin := creator_addr,
      act_from := creator_addr,
      act_body := create_deployment 30 (contract (Base := TestBase))
        exchange_setup },
    { act_origin := creator_addr,
      act_from := creator_addr,
      act_body := create_deployment 0 exploit_contract () },
    fa2_call person_1 10 (.msg_create_tokens exchange_token_id),
    exchange_call creator_addr 10
      (exchange_other_msg (.add_to_tokens_reserve exchange_token_id)),
    fa2_call person_1 0
      (.msg_update_operators
        [ .add_operator (add_operator_all person_1 exploit_caddr),
          .add_operator (add_operator_all person_1 exchange_caddr) ]) ]

def exchange_chain_result
    (exploit_contract :
      @Contract TestBase Unit ConCert.Examples.FA2.FA2TokenSender Nat Unit
        _ _ _ _) : Result TestLocalChainBuilder TestAddBlockError :=
  add_block AddrSize DepthFirst (lcb_initial AddrSize)
    initial_exchange_header (initial_exchange_actions exploit_contract)

def get_exchange_state (cb : TestLocalChainBuilder) : Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) exchange_caddr

def get_fa2_state (cb : TestLocalChainBuilder) :
    Option (@ConCert.Examples.FA2.State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @ConCert.Examples.FA2.State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) fa2_caddr

def account_tokens (cb : TestLocalChainBuilder) (account : TestAddress) : Nat :=
  match get_fa2_state cb with
  | none => 0
  | some state =>
      match FMap.find exchange_token_id state.assets with
      | none => 0
      | some ledger => (FMap.find account ledger.balances).getD 0

def exchange_liquidity (cb : TestLocalChainBuilder) : Amount :=
  (lc_to_env AddrSize cb.lcb_lc).env_account_balances exchange_caddr

def account_balance (cb : TestLocalChainBuilder) (account : TestAddress) : Amount :=
  (lc_to_env AddrSize cb.lcb_lc).env_account_balances account

def gTokensToExchange (balance : Nat) : GOpt Nat := (do
  if _hzero : balance = 0 then
    return none
  else
    let amount ← chooseNatBetween 0 balance (Nat.zero_le balance)
    return some amount :
    G (Option Nat))

def gTokenExchange
    (state : @ConCert.Examples.FA2.State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  match FMap.find exchange_token_id state.assets with
  | none => return none
  | some ledger =>
      let nr_tokens := (FMap.find person_1 ledger.balances).getD 0
      match ← gTokensToExchange nr_tokens with
      | none => return none
      | some tokens_to_exchange =>
          let exchange_msg : @ExchangeParam TestBase :=
            { exchange_owner := person_1,
              exchange_token_id := exchange_token_id,
              tokens_sold := tokens_to_exchange,
              callback_addr := exploit_caddr }
          return some (person_1, .other_msg (.tokens_to_asset exchange_msg)) :
    G (Option (TestAddress × @Msg TestBase)))

def gAddTokensToReserve (cb : TestLocalChainBuilder) :
    GOpt (TestAddress × Amount × @Msg TestBase) := (do
  let balance := account_balance cb creator_addr
  let upper := if 0 ≤ balance then balance else 0
  have hupper : 0 ≤ upper := by
    unfold upper
    by_cases h : 0 ≤ balance <;> simp [h]
  let amount ← chooseAmountBetween 0 upper hupper
  return some
    (creator_addr, amount, exchange_other_msg (.add_to_tokens_reserve exchange_token_id)) :
    G (Option (TestAddress × Amount × @Msg TestBase)))

def gExchangeAction (cb : TestLocalChainBuilder) : GOpt TestAction := (do
  match get_fa2_state cb with
  | none => return none
  | some fa2_state =>
      let choice ← chooseNatBetween 0 2 (by decide)
      if choice == 0 then
        match ← gAddTokensToReserve cb with
        | none => return none
        | some (caller, amount, msg) =>
            return some (exchange_call caller amount msg)
      else
        match ← gTokenExchange fa2_state with
        | none => return none
        | some (caller, msg) =>
            return some (exchange_call caller 0 msg) :
    G (Option TestAction))

def addExchangeActionBlockResult (cb : TestLocalChainBuilder) (act : TestAction) :
    Result TestLocalChainBuilder TestAddBlockError :=
  let header := nextBlockHeader cb.lcb_lc creator_addr 0
  add_block AddrSize DepthFirst cb header [act]

def tryAddExchangeActionBlock (cb : TestLocalChainBuilder) (act : TestAction) :
    Option TestLocalChainBuilder :=
  match addExchangeActionBlockResult cb act with
  | .Ok cb' => some cb'
  | .Err _ => none

end ConCert.Examples.ExchangeBuggy.Gens
