/- Port of examples/dexter/DexterGens.v over the local-chain backend. -/

import ConCert.Execution.Test.TraceGens
import ConCert.Examples.Dexter.Dexter

namespace ConCert.Examples.Dexter.Gens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.Dexter

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction
abbrev TestLocalChainBuilder := ConCert.Execution.Test.TraceGens.TestLocalChainBuilder
abbrev TestAddBlockError := ConCert.Execution.Test.TraceGens.TestAddBlockError

local instance : ChainBase := TestBase

def token_pool_size : Nat := 100
def token_owner : TestAddress := fixedUser10
def person_1 : TestAddress := fixedUser11
def person_2 : TestAddress := fixedLocalAddress 12 (by decide)
def token_caddr : TestAddress := fixedContractBase
def dexter_caddr : TestAddress :=
  fixedLocalAddress (ConCert.Execution.Test.TestUtils.ContractAddrBase + 1)
    (by decide)
def dexter_initial_tokens : Nat := token_pool_size - 40

def token_setup : @ConCert.Examples.EIP20.EIP20Token.Setup TestBase :=
  { owner := token_owner, init_amount := token_pool_size }

def dexter_setup : @Setup TestBase :=
  { token_caddr_ := token_caddr, token_pool_ := dexter_initial_tokens }

def token_call (caller : TestAddress)
    (msg : @ConCert.Examples.EIP20.EIP20Token.Msg TestBase) : TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call token_caddr 0 (serialize msg) }

def dexter_call (caller : TestAddress) (amount : Amount) (msg : @Msg TestBase) :
    TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call dexter_caddr amount (serialize msg) }

def add_as_operator_act (owner operator : TestAddress) (tokens : Nat) : TestAction :=
  token_call owner (.approve operator tokens)

def exchange_tokens_to_money_act (owner : TestAddress) (amount : Nat) :
    TestAction :=
  dexter_call owner 0
    (.tokens_to_asset { exchange_owner := owner, tokens_sold := amount })

def initial_dexter_header : @BlockHeader TestBase :=
  nextBlockHeader (lc_initial AddrSize) token_owner 100

def initial_dexter_actions : List TestAction :=
  [ transferAction token_owner person_1 10,
    { act_origin := token_owner,
      act_from := token_owner,
      act_body :=
        create_deployment 0
          (ConCert.Examples.EIP20.EIP20Token.contract (Base := TestBase))
          token_setup },
    { act_origin := token_owner,
      act_from := token_owner,
      act_body := create_deployment 30 (contract (Base := TestBase)) dexter_setup },
    token_call token_owner (.transfer person_1 40),
    token_call token_owner (.transfer dexter_caddr dexter_initial_tokens),
    add_as_operator_act person_1 dexter_caddr token_pool_size,
    add_as_operator_act person_2 dexter_caddr token_pool_size ]

def dexter_chain_result : Result TestLocalChainBuilder TestAddBlockError :=
  add_block AddrSize DepthFirst (lcb_initial AddrSize)
    initial_dexter_header initial_dexter_actions

def get_dexter_state (cb : TestLocalChainBuilder) : Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) dexter_caddr

def get_token_state (cb : TestLocalChainBuilder) :
    Option (@ConCert.Examples.EIP20.EIP20Token.State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @ConCert.Examples.EIP20.EIP20Token.State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) token_caddr

def account_tokens (cb : TestLocalChainBuilder) (account : TestAddress) : Nat :=
  match get_token_state cb with
  | none => 0
  | some token_state =>
      (FMap.find account token_state.balances).getD 0

def dexter_liquidity (cb : TestLocalChainBuilder) : Amount :=
  (lc_to_env AddrSize cb.lcb_lc).env_account_balances dexter_caddr

def account_balance (cb : TestLocalChainBuilder) (account : TestAddress) : Amount :=
  (lc_to_env AddrSize cb.lcb_lc).env_account_balances account

def gTokensToExchange (balance : Nat) : GOpt Nat := (do
  if hzero : balance = 0 then
    return none
  else
    let amount ← chooseNatBetween 1 balance
      (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hzero))
    return some amount :
    G (Option Nat))

def gTokenExchange
    (state : @ConCert.Examples.EIP20.EIP20Token.State TestBase)
    (caller : TestAddress) : GOpt (@Msg TestBase) := (do
  let caller_tokens := (FMap.find caller state.balances).getD 0
  match ← gTokensToExchange caller_tokens with
  | none => return none
  | some tokens_to_exchange =>
      return some (.tokens_to_asset
        { exchange_owner := caller, tokens_sold := tokens_to_exchange }) :
    G (Option (@Msg TestBase)))

def gDexterAction (cb : TestLocalChainBuilder) : GOpt TestAction := (do
  match get_token_state cb with
  | none => return none
  | some token_state =>
      match ← gTokenExchange token_state person_1 with
      | none => return none
      | some msg => return some (dexter_call person_1 0 msg) :
    G (Option TestAction))

def addDexterActionBlockResult (cb : TestLocalChainBuilder) (act : TestAction) :
    Result TestLocalChainBuilder TestAddBlockError :=
  let header := nextBlockHeader cb.lcb_lc token_owner 0
  add_block AddrSize DepthFirst cb header [act]

def tryAddDexterActionBlock (cb : TestLocalChainBuilder) (act : TestAction) :
    Option TestLocalChainBuilder :=
  match addDexterActionBlockResult cb act with
  | .Ok cb' => some cb'
  | .Err _ => none

def gDexterTrace (cb : TestLocalChainBuilder) : Nat → G TestLocalChainBuilder
  | 0 => return cb
  | n + 1 => do
      match ← gDexterAction cb with
      | none => return cb
      | some act =>
          match tryAddDexterActionBlock cb act with
          | some cb' => gDexterTrace cb' n
          | none => gDexterTrace cb n

def gDexterChainBuilder (length : Nat) : G TestLocalChainBuilder := do
  match dexter_chain_result with
  | .Ok cb => gDexterTrace cb length
  | .Err _ => genFailure "initial Dexter chain deployment failed"

def singleTradeChainResult (tokens_sold : Nat) :
    Result TestLocalChainBuilder TestAddBlockError :=
  match dexter_chain_result with
  | .Err err => .Err err
  | .Ok cb => addDexterActionBlockResult cb
      (exchange_tokens_to_money_act person_1 tokens_sold)

end ConCert.Examples.Dexter.Gens
