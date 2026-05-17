/- Port of examples/exchangeBuggy/ExchangeBuggyTests.v as executable Lean checkers. -/

import ConCert.Examples.ExchangeBuggy.ExchangeBuggyGens
import ConCert.Examples.ExchangeBuggy.ExchangeBuggyPrinters

namespace ConCert.Examples.ExchangeBuggy.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.ExchangeBuggy
open ConCert.Examples.ExchangeBuggy.Gens

local instance : ChainBase := TestBase

abbrev ExploitContractMsg := @ConCert.Examples.FA2.FA2TokenSender TestBase
abbrev ExploitContractState := Nat
abbrev ExploitContractSetup := Unit
abbrev ExploitContractError := Unit

def exploit_init
    (_chain : Chain) (_ctx : @ContractCallContext TestBase)
    (_setup : ExploitContractSetup) :
    Result ExploitContractState ExploitContractError :=
  .Ok 1

def exploit_receive
    (_chain : Chain) (ctx : @ContractCallContext TestBase)
    (state : ExploitContractState) (maybe_msg : Option ExploitContractMsg) :
    Result (ExploitContractState × List (@ActionBody TestBase))
      ExploitContractError :=
  match maybe_msg with
  | some (.tokens_sent _) =>
      if 5 < state then
        .Ok (state, [])
      else
        let token_exchange_msg : @Msg TestBase :=
          .other_msg (.tokens_to_asset
            { exchange_owner := person_1,
              exchange_token_id := exchange_token_id,
              tokens_sold := 200,
              callback_addr := ctx.ctx_contract_address })
        .Ok (state + 1,
          [.act_call exchange_caddr 0 (serialize token_exchange_msg)])
  | _ => .Ok (state, [])

def exploit_contract :
    @Contract TestBase ExploitContractSetup ExploitContractMsg
      ExploitContractState ExploitContractError _ _ _ _ :=
  { init := exploit_init, receive := exploit_receive }

def call_exchange (owner_addr : TestAddress) : TestAction :=
  let dummy_descriptor : @ConCert.Examples.FA2.TransferDescriptorParam TestBase :=
    { transfer_descr_fa2 := fa2_caddr,
      transfer_descr_batch := [],
      transfer_descr_operator := exchange_caddr }
  { act_origin := owner_addr,
    act_from := owner_addr,
    act_body := .act_call exploit_caddr 0
      (serialize (ConCert.Examples.FA2.FA2TokenSender.tokens_sent
        dummy_descriptor)) }

def initial_chain_result : Result TestLocalChainBuilder TestAddBlockError :=
  exchange_chain_result exploit_contract

def exploitChainResult : Result TestLocalChainBuilder TestAddBlockError :=
  match initial_chain_result with
  | .Err err => .Err err
  | .Ok cb => addExchangeActionBlockResult cb (call_exchange person_1)

def exchange_price_consistency (old_cb new_cb : TestLocalChainBuilder) : Bool :=
  let old_tokens := (account_tokens old_cb exchange_caddr : Int)
  let new_tokens := (account_tokens new_cb exchange_caddr : Int)
  let tokens_received := new_tokens - old_tokens
  let expected_currency_sold :=
    getInputPrice tokens_received old_tokens (exchange_liquidity old_cb)
  let expected_exchange_balance :=
    exchange_liquidity old_cb - expected_currency_sold
  expected_exchange_balance <= exchange_liquidity new_cb

def reentrancyBugWitnessChecker : Checker :=
  checker <|
    match initial_chain_result, exploitChainResult with
    | .Ok old_cb, .Ok new_cb =>
        account_balance old_cb person_1 == 0 &&
          account_tokens old_cb person_1 == 1000 &&
          account_tokens old_cb exchange_caddr == 1000 &&
          account_balance new_cb person_1 == 16 &&
          exchange_liquidity new_cb == 14 &&
          account_tokens new_cb person_1 == 0 &&
          account_tokens new_cb exchange_caddr == 2000 &&
          !(exchange_price_consistency old_cb new_cb)
    | _, _ => false

def reentrancyPriceConsistencyChecker : Checker :=
  checker <|
    match initial_chain_result, exploitChainResult with
    | .Ok old_cb, .Ok new_cb => exchange_price_consistency old_cb new_cb
    | _, _ => false

end ConCert.Examples.ExchangeBuggy.Tests
