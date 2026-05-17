/- Port of examples/iTokenBuggy/iTokenBuggyTests.v as executable Lean checkers. -/

import ConCert.Examples.ITokenBuggy.ITokenBuggyGens
import ConCert.Examples.ITokenBuggy.ITokenBuggyPrinters

namespace ConCert.Examples.ITokenBuggy.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.ITokenBuggy
open ConCert.Examples.ITokenBuggy.Gens

local instance : ChainBase := TestBase

def token_balance (addr : TestAddress) (state : @State TestBase) : Nat :=
  (FMap.find addr state.balances).getD 0

def sum_balances_eq_total_supply (state : @State TestBase) : Bool :=
  sum_balances state == state.total_supply

def token_chain_supply_invariant (cb : TestLocalChainBuilder) : Bool :=
  match get_iToken_state cb with
  | none => false
  | some state => sum_balances_eq_total_supply state

def generatedSupplyInvariantChecker (length : Nat) : Checker :=
  forAllGen (gITokenBuggyChainBuilder length) token_chain_supply_invariant

def selfTransferBugWitnessChecker : Checker :=
  checker <|
    match selfTransferBugChainResult with
    | .Err _ => false
    | .Ok cb =>
        match get_iToken_state cb with
        | none => false
        | some state =>
            token_balance token_owner state == 101 &&
              state.total_supply == 100 &&
              !(sum_balances_eq_total_supply state)

def selfTransferSupplyInvariantChecker : Checker :=
  checker <|
    match selfTransferBugChainResult with
    | .Err _ => false
    | .Ok cb => token_chain_supply_invariant cb

def nonSelfTransferFromPreservesSupplyChecker : Checker :=
  forAllGen (chooseNatBetween 0 100 (by decide)) (fun amount =>
    let recipient := token_holder2
    let allowance_map := FMap.add token_delegate 100 FMap.empty
    let state : @State TestBase :=
      { total_supply := 100,
        balances := FMap.add token_owner 100 FMap.empty,
        allowances := FMap.add token_owner allowance_map FMap.empty }
    match try_transfer_from_buggy token_delegate token_owner recipient amount state with
    | .Ok state' =>
        sum_balances_eq_total_supply state' &&
          state'.total_supply == state.total_supply
    | .Err _ => false)

def approvePreservesSupplyChecker : Checker :=
  forAllGen (chooseNatBetween 0 100 (by decide)) (fun amount =>
    let state : @State TestBase :=
      { total_supply := 100,
        balances := FMap.add token_owner 100 FMap.empty,
        allowances := FMap.empty }
    match try_approve token_owner token_delegate amount state with
    | .Ok state' =>
        sum_balances_eq_total_supply state' &&
          state'.total_supply == state.total_supply
    | .Err _ => false)

end ConCert.Examples.ITokenBuggy.Tests
