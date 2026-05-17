/- Port of examples/fa2/FA2Gens.v over the local-chain backend. -/

import ConCert.Execution.Test.TraceGens
import ConCert.Examples.FA2.FA2Token
import ConCert.Examples.FA2.TestContracts

namespace ConCert.Examples.FA2.Gens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.FA2

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction
abbrev TestLocalChainBuilder := ConCert.Execution.Test.TraceGens.TestLocalChainBuilder
abbrev TestAddBlockError := ConCert.Execution.Test.TraceGens.TestAddBlockError

local instance : ChainBase := TestBase

def token_id_0 : TokenId := 0
def creator_addr : TestAddress := fixedUser10
def person_1 : TestAddress := fixedUser11
def person_2 : TestAddress := fixedLocalAddress 12 (by decide)
def person_3 : TestAddress := fixedLocalAddress 13 (by decide)
def token_contract_base_addr : TestAddress := fixedContractBase
def client_contract_addr : TestAddress :=
  fixedLocalAddress (ConCert.Execution.Test.TestUtils.ContractAddrBase + 1)
    (by decide)

def accounts : List TestAddress :=
  [person_1, person_2, person_3]

def policy_self_only : PermissionsDescriptor :=
  { descr_self := .self_transfer_permitted,
    descr_operator := .operator_transfer_denied,
    descr_sender := .owner_no_op,
    descr_receiver := .owner_no_op,
    descr_custom := none }

def policy_all : PermissionsDescriptor :=
  { descr_self := .self_transfer_permitted,
    descr_operator := .operator_transfer_permitted,
    descr_sender := .owner_no_op,
    descr_receiver := .owner_no_op,
    descr_custom := none }

def token_metadata_0 : TokenMetadata :=
  { metadata_token_id := token_id_0, metadata_decimals := 8 }

def token_setup : @Setup TestBase :=
  { setup_total_supply := [],
    setup_tokens := FMap.add token_id_0 token_metadata_0 FMap.empty,
    initial_permission_policy := policy_all,
    transfer_hook_addr_ := none }

def token_client_setup : @TestContracts.ClientSetup TestBase :=
  { fa2_caddr_ := token_contract_base_addr }

def fa2_call (caller : TestAddress) (amount : Amount) (msg : @Msg TestBase) :
    TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call token_contract_base_addr amount (serialize msg) }

def initial_fa2_header : @BlockHeader TestBase :=
  nextBlockHeader (lc_initial AddrSize) creator_addr 100

def initial_fa2_actions : List TestAction :=
  [ transferAction creator_addr person_1 10,
    transferAction creator_addr person_2 10,
    transferAction creator_addr person_3 10,
    { act_origin := creator_addr,
      act_from := creator_addr,
      act_body := create_deployment 0 (contract (Base := TestBase)) token_setup },
    { act_origin := creator_addr,
      act_from := creator_addr,
      act_body := create_deployment 0
        (TestContracts.client_contract (Base := TestBase)) token_client_setup },
    fa2_call person_1 10 (.msg_create_tokens token_id_0),
    fa2_call person_2 10 (.msg_create_tokens token_id_0) ]

def fa2_chain_result : Result TestLocalChainBuilder TestAddBlockError :=
  add_block AddrSize DepthFirst (lcb_initial AddrSize)
    initial_fa2_header initial_fa2_actions

def get_fa2_state (cb : TestLocalChainBuilder) : Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) token_contract_base_addr

def token0_balance (state : @State TestBase) (addr : TestAddress) : Nat :=
  address_balance token_id_0 addr state

def token0_total (state : @State TestBase) : Nat :=
  token_id_balance token_id_0 state

def accountCandidates : List TestAddress := accounts

def gAccount : G TestAddress :=
  Plausible.Gen.elements accountCandidates (by simp [accountCandidates, accounts])

def gAddrWithoutLocal (without : List TestAddress) : G TestAddress :=
  let addrs := accounts.filter
    (fun addr => !(without.any (fun blocked => TestBase.address_eqb addr blocked)))
  match addrs with
  | [] => gAccount
  | addr :: rest => Plausible.Gen.elements (addr :: rest) (by simp)

def gSelfTransfer (state : @State TestBase) : GOpt (TestAddress × @Msg TestBase) := (do
  match FMap.find token_id_0 state.assets with
  | none => return none
  | some ledger =>
      match ← sampleFMapOpt_filter ledger.balances (fun p => 0 < p.2) with
      | none => return none
      | some (from_, balance) =>
          let to_ ← gAddrWithoutLocal [from_]
          let amount ← chooseNatBetween 0 balance (Nat.zero_le balance)
          let transfer : @Transfer TestBase :=
            { from_ := from_,
              txs := [{ to_ := to_, dst_token_id := token_id_0, amount := amount }],
              sender_callback_addr := none }
          return some (from_, .msg_transfer [transfer]) :
    G (Option (TestAddress × @Msg TestBase)))

def gOperatorParam : GOpt (@OperatorParam TestBase) := (do
  let owner ← gAccount
  let operator ← gAddrWithoutLocal [owner]
  let useAll ← chooseBool
  let tokens := if useAll then .all_tokens else .some_tokens [token_id_0]
  return some
    ({ op_param_owner := owner, op_param_operator := operator,
       op_param_tokens := tokens } : @OperatorParam TestBase) :
    G (Option (@OperatorParam TestBase)))

def gUpdateOperators (maxSize : Nat) : GOpt (@Msg TestBase) := (do
  if hzero : maxSize = 0 then
    return none
  else
    let n ← chooseNatBetween 1 maxSize
      (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hzero))
    let updates ← optToVector n (do
      match ← gOperatorParam with
      | none => return none
      | some param =>
          let add ← chooseBool
          return some (if add then .add_operator param else .remove_operator param) :
      G (Option (@UpdateOperator TestBase)))
    if updates.isEmpty then
      return none
    else
      return some (.msg_update_operators updates) :
    G (Option (@Msg TestBase)))

def gFA2TokenAction (cb : TestLocalChainBuilder) : GOpt TestAction := (do
  match get_fa2_state cb with
  | none => return none
  | some state =>
      let choice ← chooseNatBetween 0 5 (by decide)
      let generated ←
        (if choice < 4 then
          gSelfTransfer state
        else
          (do
            match ← gUpdateOperators 2 with
            | none => return none
            | some msg =>
                let caller ← gAccount
                return some (caller, msg) :
            G (Option (TestAddress × @Msg TestBase))) :
          G (Option (TestAddress × @Msg TestBase)))
      match generated with
      | none => return none
      | some (caller, msg) => return some (fa2_call caller 0 msg) :
    G (Option TestAction))

def addFA2ActionBlockResult (cb : TestLocalChainBuilder) (act : TestAction) :
    Result TestLocalChainBuilder TestAddBlockError :=
  let header := nextBlockHeader cb.lcb_lc creator_addr 0
  add_block AddrSize DepthFirst cb header [act]

def tryAddFA2ActionBlock (cb : TestLocalChainBuilder) (act : TestAction) :
    Option TestLocalChainBuilder :=
  match addFA2ActionBlockResult cb act with
  | .Ok cb' => some cb'
  | .Err _ => none

def gFA2Trace (cb : TestLocalChainBuilder) : Nat → G TestLocalChainBuilder
  | 0 => return cb
  | n + 1 => do
      match ← gFA2TokenAction cb with
      | none => return cb
      | some act =>
          match tryAddFA2ActionBlock cb act with
          | some cb' => gFA2Trace cb' n
          | none => gFA2Trace cb n

def gFA2ChainBuilder (length : Nat) : G TestLocalChainBuilder := do
  match fa2_chain_result with
  | .Ok cb => gFA2Trace cb length
  | .Err _ => genFailure "initial FA2 chain deployment failed"

end ConCert.Examples.FA2.Gens
