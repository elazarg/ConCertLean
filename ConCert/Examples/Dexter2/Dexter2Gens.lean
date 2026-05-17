/- Port of examples/dexter2/Dexter2Gens.v over the local-chain backend. -/

import ConCert.Execution.Test.TraceGens
import ConCert.Examples.Dexter2.Dexter2CPMM
import ConCert.Examples.Dexter2.Dexter2Printers
import ConCert.Examples.FA2.FA2Token

namespace ConCert.Examples.Dexter2.Gens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.Dexter2.CPMM

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction

local instance : ChainBase := TestBase

def cpmm_contract_addr : TestAddress := fixedContractBase
def token_contract_addr : TestAddress :=
  fixedLocalAddress (ConCert.Execution.Test.TestUtils.ContractAddrBase + 1)
    (by decide)
def token_id : ConCert.Examples.FA2.TokenId := 0

def account1 : TestAddress := fixedUser10
def account2 : TestAddress := fixedUser11
def account3 : TestAddress := fixedLocalAddress 12 (by decide)

def accounts : List TestAddress := [account1, account2, account3]

def gAddr : G TestAddress :=
  Plausible.Gen.elements accounts (by simp [accounts])

def gNonBrokeAddr (env : @Environment TestBase) : GOpt TestAddress :=
  let funded := accounts.filter (fun addr => 0 < env.env_account_balances addr)
  elems_opt funded

def gUpdateTokenPool (_env : @Environment TestBase) :
    G (TestAddress × Amount × @Msg TestBase) := do
  let from_addr ← gAddr
  return (from_addr, 0, .other_msg .UpdateTokenPool)

def gXtzToToken (env : @Environment TestBase) :
    GOpt (TestAddress × Amount × @Msg TestBase) := (do
  match ← gNonBrokeAddr env with
  | none => return none
  | some from_addr =>
      let deadline ← chooseNatBetween
        (env.current_slot + 1) (env.current_slot + 10)
        (by omega)
      let balance := env.env_account_balances from_addr
      if hpos : 0 < balance then
        let amountNat ← chooseNatBetween 1 balance.toNat (by
          have hnotzero : balance.toNat ≠ 0 := by
            intro hz
            have hle : balance ≤ 0 := Int.toNat_eq_zero.mp hz
            exact (not_le_of_gt hpos) hle
          exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hnotzero))
        let param : @XtzToTokenParam TestBase :=
          { tokens_to := from_addr,
            minTokensBought := 1,
            xtt_deadline := deadline }
        return some (from_addr, Int.ofNat amountNat, .other_msg (.XtzToToken param))
      else
        return none :
    G (Option (TestAddress × Amount × @Msg TestBase)))

def gTokenToXtz (env : @Environment TestBase) :
    G (TestAddress × Amount × @Msg TestBase) := do
  let from_addr ← gAddr
  let deadline ← chooseNatBetween
    (env.current_slot + 1) (env.current_slot + 10)
    (by omega)
  let amount ← chooseNatBetween 30 50 (by decide)
  let param : @TokenToXtzParam TestBase :=
    { xtz_to := from_addr,
      tokensSold := amount,
      minXtzBought := 1,
      ttx_deadline := deadline }
  return (from_addr, 0, .other_msg (.TokenToXtz param))

def gBalanceOf (_env : @Environment TestBase) :
    G (TestAddress × Amount × @ConCert.Examples.FA2.Msg TestBase) := do
  let from_addr ← gAddr
  let request_addr ← gAddr
  let param : @ConCert.Examples.FA2.BalanceOfParam TestBase :=
    { bal_requests :=
        [{ owner := request_addr, bal_req_token_id := token_id }],
      bal_callback := { blob := none, return_addr := cpmm_contract_addr } }
  return (from_addr, 0, .msg_balance_of param)

def call (contract_addr caller_addr : TestAddress) (value : Amount)
    (msg : ConCert.Execution.SerializableBase.SerializedValue) : TestAction :=
  { act_origin := caller_addr,
    act_from := caller_addr,
    act_body := .act_call contract_addr value msg }

def call_cpmm (caller_addr : TestAddress) (value : Amount)
    (msg : @Msg TestBase) : TestAction :=
  call cpmm_contract_addr caller_addr value (serialize msg)

def call_token (caller_addr : TestAddress) (value : Amount)
    (msg : @ConCert.Examples.FA2.Msg TestBase) : TestAction :=
  call token_contract_addr caller_addr value (serialize msg)

def gAction (env : @Environment TestBase) : GOpt TestAction := (do
  let choice ← chooseNatBetween 0 3 (by decide)
  match choice with
  | 0 =>
      let (caller, value, msg) ← gUpdateTokenPool env
      return some (call_cpmm caller value msg)
  | 1 =>
      match ← gXtzToToken env with
      | some (caller, value, msg) => return some (call_cpmm caller value msg)
      | none => return none
  | 2 =>
      let (caller, value, msg) ← gTokenToXtz env
      return some (call_cpmm caller value msg)
  | _ =>
      let (caller, value, msg) ← gBalanceOf env
      return some (call_token caller value msg) :
    G (Option TestAction))

end ConCert.Examples.Dexter2.Gens
