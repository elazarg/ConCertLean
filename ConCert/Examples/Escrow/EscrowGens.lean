/- Port of examples/escrow/tests/EscrowGens.v over the local-chain test backend. -/

import ConCert.Execution.Test.TraceGens
import ConCert.Examples.Escrow.Escrow

namespace ConCert.Examples.Escrow.Gens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Execution.ResultMonad
open ConCert.Examples.Escrow

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction
abbrev TestLocalChainBuilder := ConCert.Execution.Test.TraceGens.TestLocalChainBuilder
abbrev TestAddBlockError := ConCert.Execution.Test.TraceGens.TestAddBlockError

local instance : ChainBase := TestBase

def seller : TestAddress := fixedUser10
def buyer : TestAddress := fixedUser11
def escrow_contract_addr : TestAddress := fixedContractBase

def escrow_setup : @Setup TestBase :=
  { setup_buyer := buyer }

def escrow_call (caller : TestAddress) (amount : Amount) (msg : Msg) : TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call escrow_contract_addr amount (serialize msg) }

def initial_escrow_header :
    @BlockHeader TestBase :=
  nextBlockHeader (lc_initial AddrSize) seller 12

def initial_escrow_actions : List TestAction :=
  [ transferAction seller buyer 10,
    { act_origin := seller,
      act_from := seller,
      act_body := create_deployment 2 (contract (Base := TestBase)) escrow_setup } ]

def escrow_chain_result :
    Result TestLocalChainBuilder TestAddBlockError :=
  add_block AddrSize DepthFirst (lcb_initial AddrSize)
    initial_escrow_header initial_escrow_actions

def get_escrow_state (cb : TestLocalChainBuilder) : Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) escrow_contract_addr

def account_balance (cb : TestLocalChainBuilder) (addr : TestAddress) : Amount :=
  (lc_to_env AddrSize cb.lcb_lc).env_account_balances addr

def gEscrowMsg (cb : TestLocalChainBuilder) : GOpt TestAction := (do
  match get_escrow_state cb with
  | none => return none
  | some state =>
      let n ← chooseNatBetween 0 2 (by decide)
      match n with
      | 0 =>
          if account_balance cb state.buyer < 2 then
            return none
          else
            return some (escrow_call state.buyer 2 .commit_money)
      | 1 =>
          return some (escrow_call state.buyer 0 .confirm_item_received)
      | _ =>
          let withdrawer ← Plausible.Gen.elements [state.seller, state.buyer] (by simp)
          return some (escrow_call withdrawer 0 .withdraw) :
    G (Option TestAction))

def gEscrowMsgBetter (cb : TestLocalChainBuilder) : GOpt TestAction := (do
  match get_escrow_state cb with
  | none => return none
  | some state =>
      match state.next_step with
      | .buyer_commit =>
          let chooseCommit ← chooseBool
          if chooseCommit && !(account_balance cb state.buyer < 2) then
            return some (escrow_call state.buyer 2 .commit_money)
          else
            return some (escrow_call state.seller 0 .withdraw)
      | .buyer_confirm =>
          return some (escrow_call state.buyer 0 .confirm_item_received)
      | .withdrawals =>
          if 0 < state.buyer_withdrawable then
            return some (escrow_call state.buyer 0 .withdraw)
          else if 0 < state.seller_withdrawable then
            return some (escrow_call state.seller 0 .withdraw)
          else
            return none
      | .no_next_step =>
          return none :
    G (Option TestAction))

def addEscrowActionBlock (cb : TestLocalChainBuilder) (act : TestAction) :
    G TestLocalChainBuilder := do
  let header := nextBlockHeader cb.lcb_lc seller 0
  match add_block AddrSize DepthFirst cb header [act] with
  | .Ok cb' => return cb'
  | .Err _ => genFailure "generated escrow action block was rejected"

def tryAddEscrowActionBlock (cb : TestLocalChainBuilder) (act : TestAction) :
    Option TestLocalChainBuilder :=
  let header := nextBlockHeader cb.lcb_lc seller 0
  match add_block AddrSize DepthFirst cb header [act] with
  | .Ok cb' => some cb'
  | .Err _ => none

def gEscrowTrace (cb : TestLocalChainBuilder) : Nat → G TestLocalChainBuilder
  | 0 => return cb
  | n + 1 => do
      match ← gEscrowMsg cb with
      | none => return cb
      | some act =>
          match tryAddEscrowActionBlock cb act with
          | some cb' => gEscrowTrace cb' n
          | none => gEscrowTrace cb n

def gEscrowTraceBetter (cb : TestLocalChainBuilder) : Nat → G TestLocalChainBuilder
  | 0 => return cb
  | n + 1 => do
      match ← gEscrowMsgBetter cb with
      | none => return cb
      | some act =>
          let cb' ← addEscrowActionBlock cb act
          gEscrowTraceBetter cb' n

def gEscrowChainBuilder (length : Nat) : G TestLocalChainBuilder := do
  match escrow_chain_result with
  | .Ok cb => gEscrowTraceBetter cb length
  | .Err _ => genFailure "initial escrow chain deployment failed"

def forAllEscrowChainBuilder
    (length : Nat) (cb : TestLocalChainBuilder) (pf : TestLocalChainBuilder → Bool) :
    Checker :=
  forAllGen (gEscrowTraceBetter cb length) pf

end ConCert.Examples.Escrow.Gens
