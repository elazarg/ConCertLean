/- Port of examples/EIP20/EIP20TokenTests.v as executable Lean checkers. -/

import ConCert.Examples.EIP20.EIP20TokenGens
import ConCert.Examples.EIP20.EIP20TokenPrinters
import ConCert.Utils.Extras

namespace ConCert.Examples.EIP20.EIP20Token.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.EIP20.EIP20Token
open ConCert.Examples.EIP20.EIP20Token.Gens

local instance : ChainBase := TestBase

def test_chain : Chain :=
  { chain_height := 0, current_slot := 0, finalized_height := 0 }

def token_context (sender : TestAddress) (amount balance : Amount) :
    @ContractCallContext TestBase :=
  { ctx_origin := sender,
    ctx_from := sender,
    ctx_contract_address := token_contract_addr,
    ctx_contract_balance := balance,
    ctx_amount := amount }

def get_balance (addr : TestAddress) (state : @State TestBase) : TokenValue :=
  (FMap.find addr state.balances).getD 0

def sum_balances_eq_total_supply (state : @State TestBase) : Bool :=
  sum_balances state == state.total_supply

def init_supply_eq_total_supply (state : @State TestBase) : Bool :=
  state.total_supply == init_supply

def token_chain_supply_invariant (cb : TestLocalChainBuilder) : Bool :=
  match get_eip20_state cb with
  | none => false
  | some state =>
      sum_balances_eq_total_supply state && init_supply_eq_total_supply state

def generatedSupplyInvariantChecker (length : Nat) : Checker :=
  forAllGen (gEIP20ChainBuilder length) token_chain_supply_invariant

def transfer_balance_update_correct
    (old_state new_state : @State TestBase)
    (from_ to_ : TestAddress) (tokens : TokenValue) : Bool :=
  let from_before := get_balance from_ old_state
  let to_before := get_balance to_ old_state
  let from_after := get_balance from_ new_state
  let to_after := get_balance to_ new_state
  if TestBase.address_eqb from_ to_ then
    from_before == from_after && to_before == to_after
  else
    from_before == from_after + tokens && to_before + tokens == to_after

def transfer_from_allowances_update_correct
    (old_state new_state : @State TestBase)
    (from_ delegate : TestAddress) (tokens : TokenValue) : Bool :=
  let before := get_allowance old_state from_ delegate
  let after := get_allowance new_state from_ delegate
  before == after + tokens

def approve_allowance_update_correct
    (new_state : @State TestBase)
    (from_ delegate : TestAddress) (tokens : TokenValue) : Bool :=
  get_allowance new_state from_ delegate == tokens

def receivePostconditionsChecker : Checker :=
  forAllGen (chooseNatBetween 0 init_supply (Nat.zero_le init_supply)) (fun amount =>
    let state : @State TestBase :=
      { total_supply := init_supply,
        balances := FMap.add token_owner init_supply FMap.empty,
        allowances := FMap.empty }
    let ctx := token_context token_owner 0 0
    match receive test_chain ctx state (some (.transfer token_holder2 amount)) with
    | .Ok (new_state, new_acts) =>
        ctx.ctx_amount == 0 && new_acts.isEmpty &&
          new_state.total_supply == state.total_supply
    | .Err _ => false)

def transferCorrectChecker : Checker :=
  forAllGen (chooseNatBetween 0 init_supply (Nat.zero_le init_supply)) (fun amount =>
    let state : @State TestBase :=
      { total_supply := init_supply,
        balances := FMap.add token_owner init_supply FMap.empty,
        allowances := FMap.empty }
    match try_transfer token_owner token_holder2 amount state with
    | .Ok state' =>
        transfer_balance_update_correct state state' token_owner token_holder2 amount &&
          sum_balances_eq_total_supply state'
    | .Err _ => false)

def selfTransferCorrectChecker : Checker :=
  forAllGen (chooseNatBetween 0 init_supply (Nat.zero_le init_supply)) (fun amount =>
    let state : @State TestBase :=
      { total_supply := init_supply,
        balances := FMap.add token_owner init_supply FMap.empty,
        allowances := FMap.empty }
    match try_transfer token_owner token_owner amount state with
    | .Ok state' =>
        transfer_balance_update_correct state state' token_owner token_owner amount &&
          sum_balances_eq_total_supply state'
    | .Err _ => false)

def transferFromCorrectChecker : Checker :=
  forAllGen (chooseNatBetween 0 80 (by decide)) (fun amount =>
    let allowance_map := FMap.add token_delegate 80 FMap.empty
    let state : @State TestBase :=
      { total_supply := init_supply,
        balances := FMap.add token_owner init_supply FMap.empty,
        allowances := FMap.add token_owner allowance_map FMap.empty }
    match try_transfer_from token_delegate token_owner token_holder2 amount state with
    | .Ok state' =>
        transfer_balance_update_correct state state' token_owner token_holder2 amount &&
          transfer_from_allowances_update_correct
            state state' token_owner token_delegate amount &&
          sum_balances_eq_total_supply state'
    | .Err _ => false)

def approveCorrectChecker : Checker :=
  forAllGen (chooseNatBetween 0 init_supply (Nat.zero_le init_supply)) (fun amount =>
    let state : @State TestBase :=
      { total_supply := init_supply,
        balances := FMap.add token_owner init_supply FMap.empty,
        allowances := FMap.empty }
    match try_approve token_owner token_delegate amount state with
    | .Ok state' =>
        approve_allowance_update_correct state' token_owner token_delegate amount &&
          sum_balances_eq_total_supply state' &&
          state'.total_supply == state.total_supply
    | .Err _ => false)

def sum_allowances (state : @State TestBase) : TokenValue :=
  let allowance_sums :=
    FMap.elements state.allowances |>.map
      (fun p => ((FMap.elements p.2).map (fun q : TestAddress × TokenValue => q.2)).sum)
  allowance_sums.sum

def sum_allowances_le_total_supply (state : @State TestBase) : Bool :=
  sum_allowances state <= state.total_supply

def allowancesExceedSupplyChecker : Checker :=
  checker <|
    match allowancesExceedSupplyChainResult with
    | .Err _ => false
    | .Ok cb =>
        match get_eip20_state cb with
        | none => false
        | some state => sum_allowances_le_total_supply state

def reapproveTransferFromSafetyChecker : Checker :=
  checker <|
    match reapproveRaceChainResult with
    | .Err _ => false
    | .Ok cb =>
        match get_eip20_state cb with
        | none => false
        | some state =>
            let remaining := get_allowance state token_owner token_delegate
            let spent := get_balance token_holder2 state
            spent <= remaining

end ConCert.Examples.EIP20.EIP20Token.Tests
