/- Port of examples/iTokenBuggy/iTokenBuggyGens.v over the local-chain backend. -/

import ConCert.Execution.Test.TraceGens
import ConCert.Examples.ITokenBuggy.ITokenBuggy

namespace ConCert.Examples.ITokenBuggy.Gens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Execution.ResultMonad
open ConCert.Examples.ITokenBuggy

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction
abbrev TestLocalChainBuilder := ConCert.Execution.Test.TraceGens.TestLocalChainBuilder
abbrev TestAddBlockError := ConCert.Execution.Test.TraceGens.TestAddBlockError

local instance : ChainBase := TestBase

def token_owner : TestAddress := fixedUser10
def token_delegate : TestAddress := fixedUser11
def token_holder2 : TestAddress := fixedLocalAddress 12 (by decide)
def token_holder3 : TestAddress := fixedLocalAddress 13 (by decide)
def token_contract_addr : TestAddress := fixedContractBase

def token_setup : @Setup TestBase :=
  { owner := token_owner, init_amount := 100 }

def token_call (caller : TestAddress) (amount : Amount) (msg : @Msg TestBase) :
    TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call token_contract_addr amount (serialize msg) }

def initial_token_header : @BlockHeader TestBase :=
  nextBlockHeader (lc_initial AddrSize) token_owner 100

def initial_token_actions : List TestAction :=
  [ transferAction token_owner token_delegate 0,
    transferAction token_owner token_holder2 0,
    transferAction token_owner token_holder3 0,
    { act_origin := token_owner,
      act_from := token_owner,
      act_body := create_deployment 0 (contract (Base := TestBase)) token_setup } ]

def token_chain_result : Result TestLocalChainBuilder TestAddBlockError :=
  add_block AddrSize DepthFirst (lcb_initial AddrSize)
    initial_token_header initial_token_actions

def account_candidates : List TestAddress :=
  [token_owner, token_delegate, token_holder2, token_holder3]

def gAccount : G TestAddress :=
  Plausible.Gen.elements account_candidates (by simp [account_candidates])

def get_iToken_state (cb : TestLocalChainBuilder) : Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) token_contract_addr

def get_iToken_state_from_env
    (env : @Environment TestBase) : Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase) env token_contract_addr

def gApprove (state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  match ← sample2UniqueFMapOpt state.balances with
  | none => return none
  | some ((addr1, balance1), (addr2, balance2)) =>
      if 0 < balance1 then
        let amount ← chooseNatBetween 0 balance1 (Nat.zero_le balance1)
        return some (addr1, .approve addr2 amount)
      else if 0 < balance2 then
        let amount ← chooseNatBetween 0 balance2 (Nat.zero_le balance2)
        return some (addr2, .approve addr1 amount)
      else
        return none :
    G (Option (TestAddress × @Msg TestBase)))

def gTransferFrom (state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  match ← sampleFMapOpt state.allowances with
  | none => return none
  | some (allower, allowance_map) =>
      match ← sampleFMapOpt allowance_map with
      | none => return none
      | some (delegate, allowance) =>
          match ← sampleFMapOpt state.balances with
          | none => return none
          | some (receiver, _) =>
              let allower_balance := FMap_find_ allower state.balances 0
              let upper := Nat.min allowance allower_balance
              let amount ← chooseNatBetween 0 upper (Nat.zero_le upper)
              return some (delegate, .transfer_from allower receiver amount) :
    G (Option (TestAddress × @Msg TestBase)))

def gMint (_env : @Environment TestBase) (_state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  let addr ← gAccount
  let amount ← chooseNatBetween 0 2 (by decide)
  return some (addr, .mint amount) :
    G (Option (TestAddress × @Msg TestBase)))

def gBurn (state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  match ← sampleFMapOpt_filter state.balances (fun p => 0 < p.2) with
  | none => return none
  | some (addr, balance) =>
      let amount ← chooseNatBetween 0 (balance + 2) (Nat.zero_le _)
      return some (addr, .burn amount) :
    G (Option (TestAddress × @Msg TestBase)))

def gITokenBuggyAction (env : @Environment TestBase) : GOpt TestAction := (do
  match get_iToken_state_from_env env with
  | none => return none
  | some state =>
      let choice ← chooseNatBetween 0 7 (by decide)
      let generated ←
        match choice with
        | 0 => gMint env state
        | 1 => gBurn state
        | 2 | 3 | 4 | 5 => gTransferFrom state
        | _ => gApprove state
      match generated with
      | none =>
          let fallback ← gMint env state
          return fallback.map (fun p => token_call p.1 0 p.2)
      | some (caller, msg) =>
          return some (token_call caller 0 msg) :
    G (Option TestAction))

def addITokenActionBlockResult (cb : TestLocalChainBuilder) (act : TestAction) :
    Result TestLocalChainBuilder TestAddBlockError :=
  let header := nextBlockHeader cb.lcb_lc token_owner 0
  add_block AddrSize DepthFirst cb header [act]

def addITokenActionBlock (cb : TestLocalChainBuilder) (act : TestAction) :
    G TestLocalChainBuilder := do
  match addITokenActionBlockResult cb act with
  | .Ok cb' => return cb'
  | .Err _ => genFailure "generated iTokenBuggy action block was rejected"

def tryAddITokenActionBlock (cb : TestLocalChainBuilder) (act : TestAction) :
    Option TestLocalChainBuilder :=
  match addITokenActionBlockResult cb act with
  | .Ok cb' => some cb'
  | .Err _ => none

def gITokenBuggyTrace (cb : TestLocalChainBuilder) : Nat → G TestLocalChainBuilder
  | 0 => return cb
  | n + 1 => do
      match ← gITokenBuggyAction (lc_to_env AddrSize cb.lcb_lc) with
      | none => return cb
      | some act =>
          match tryAddITokenActionBlock cb act with
          | some cb' => gITokenBuggyTrace cb' n
          | none => gITokenBuggyTrace cb n

def gITokenBuggyChainBuilder (length : Nat) : G TestLocalChainBuilder := do
  match token_chain_result with
  | .Ok cb => gITokenBuggyTrace cb length
  | .Err _ => genFailure "initial iTokenBuggy chain deployment failed"

def selfTransferBugChainResult :
    Result TestLocalChainBuilder TestAddBlockError :=
  match token_chain_result with
  | .Err err => .Err err
  | .Ok cb0 =>
      match addITokenActionBlockResult cb0
          (token_call token_owner 0 (.approve token_delegate 0)) with
      | .Err err => .Err err
      | .Ok cb1 =>
          addITokenActionBlockResult cb1
            (token_call token_delegate 0
              (.transfer_from token_owner token_owner 1))

end ConCert.Examples.ITokenBuggy.Gens
