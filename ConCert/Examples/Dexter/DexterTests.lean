/- Port of examples/dexter/DexterTests.v as executable Lean checkers. -/

import ConCert.Examples.Dexter.DexterGens
import ConCert.Examples.Dexter.DexterPrinters

namespace ConCert.Examples.Dexter.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.Dexter
open ConCert.Examples.Dexter.Gens

local instance : ChainBase := TestBase

def dexter_token_pool (cb : TestLocalChainBuilder) : Nat :=
  match get_dexter_state cb with
  | none => 0
  | some state => state.token_pool

def dexter_pool_matches_token_balance (cb : TestLocalChainBuilder) : Bool :=
  dexter_token_pool cb == account_tokens cb dexter_caddr

def generatedPoolMatchesTokenBalanceChecker (length : Nat) : Checker :=
  forAllGen (gDexterChainBuilder length) dexter_pool_matches_token_balance

def singleTradeCorrect (tokens_sold : Nat) : Bool :=
  match dexter_chain_result, singleTradeChainResult tokens_sold with
  | .Ok old_cb, .Ok new_cb =>
      let old_liquidity := dexter_liquidity old_cb
      let old_token_pool := account_tokens old_cb dexter_caddr
      let expected_price :=
        getInputPrice tokens_sold old_token_pool old_liquidity
      account_balance new_cb person_1 ==
        account_balance old_cb person_1 + expected_price &&
      dexter_liquidity new_cb == old_liquidity - expected_price &&
      account_tokens new_cb person_1 ==
        account_tokens old_cb person_1 - tokens_sold &&
      account_tokens new_cb dexter_caddr == old_token_pool + tokens_sold &&
      dexter_token_pool new_cb == old_token_pool + tokens_sold &&
      dexter_pool_matches_token_balance new_cb
  | _, _ => false

def singleTradeCorrectChecker : Checker :=
  forAllGen (chooseNatBetween 1 40 (by decide)) singleTradeCorrect

end ConCert.Examples.Dexter.Tests
