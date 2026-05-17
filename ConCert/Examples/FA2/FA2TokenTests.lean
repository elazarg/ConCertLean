/- Port of examples/fa2/FA2TokenTests.v as executable Lean checkers. -/

import ConCert.Examples.FA2.FA2Gens
import ConCert.Examples.FA2.FA2Printers

namespace ConCert.Examples.FA2.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.FA2
open ConCert.Examples.FA2.Gens

local instance : ChainBase := TestBase

def generatedSupplyInvariant (cb : TestLocalChainBuilder) : Bool :=
  match get_fa2_state cb with
  | none => false
  | some state => token0_total state == 2000

def generatedSupplyInvariantChecker (length : Nat) : Checker :=
  forAllGen (gFA2ChainBuilder length) generatedSupplyInvariant

def transfer_state_update_correct
    (prev_state next_state : @State TestBase)
    (from_ to_ : TestAddress) (amount : Nat) : Bool :=
  let from_before := address_balance token_id_0 from_ prev_state
  let to_before := address_balance token_id_0 to_ prev_state
  let from_after := address_balance token_id_0 from_ next_state
  let to_after := address_balance token_id_0 to_ next_state
  if TestBase.address_eqb from_ to_ then
    from_before == from_after && to_before == to_after
  else
    from_before == from_after + amount && to_before + amount == to_after

def directTransferUpdateChecker : Checker :=
  forAllGen (chooseNatBetween 1 1000 (by decide)) (fun amount =>
    let ledger : @TokenLedger TestBase :=
      { fungible := false,
        balances := FMap.add person_1 1000 FMap.empty }
    let state : @State TestBase :=
      { fa2_owner := creator_addr,
        assets := FMap.add token_id_0 ledger FMap.empty,
        operators := FMap.empty,
        permission_policy := policy_all,
        tokens := FMap.add token_id_0 token_metadata_0 FMap.empty,
        transfer_hook_addr := none }
    let transfer : @Transfer TestBase :=
      { from_ := person_1,
        txs := [{ to_ := person_2, dst_token_id := token_id_0, amount := amount }],
        sender_callback_addr := none }
    match try_transfer person_1 [transfer] state with
    | .Ok state' =>
        transfer_state_update_correct state state' person_1 person_2 amount &&
          token_id_balance token_id_0 state' == token_id_balance token_id_0 state
    | .Err _ => false)

def single_update_op_correct (new_state : @State TestBase)
    (op : @UpdateOperator TestBase) : Bool :=
  let (param, is_remove) :=
    match op with
    | .add_operator param => (param, false)
    | .remove_operator param => (param, true)
  match FMap.find param.op_param_owner new_state.operators with
  | some owners_map =>
      if is_remove then true
      else (FMap.find param.op_param_operator owners_map).isSome
  | none => is_remove

def lastUpdateOperatorOccurrenceChecker : Checker :=
  checker <|
    let param : @OperatorParam TestBase :=
      { op_param_owner := person_1,
        op_param_operator := person_2,
        op_param_tokens := .all_tokens }
    let ops : List (@UpdateOperator TestBase) :=
      [.remove_operator param, .add_operator param]
    let state : @State TestBase :=
      { fa2_owner := creator_addr,
        assets := FMap.empty,
        operators := FMap.empty,
        permission_policy := policy_all,
        tokens := FMap.add token_id_0 token_metadata_0 FMap.empty,
        transfer_hook_addr := none }
    match update_operators person_1 ops state with
    | .Ok state' =>
        single_update_op_correct state' (.add_operator param)
    | .Err _ => false

end ConCert.Examples.FA2.Tests
