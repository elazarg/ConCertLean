import ConCert

open ConCert.Execution.SerializableBase
open ConCert.Execution.SerializableInstances
open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainBuilder
open ConCert.Execution.ContractCommon
open ConCert.Execution.ResultMonad
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Utils.Env

#guard ConCert.Utils.StringExtra.to_upper "abZ9" == "ABZ9"
#guard ConCert.Utils.StringExtra.str_rev "abc" == "cba"
#guard ConCert.Utils.Extras.with_default 7 (none : Option Nat) == 7
#guard (deserialize (serialize (42 : Nat)) : Option Nat) == some 42
#guard (deserialize (serialize (true : Bool)) : Option Bool) == some true
#guard (LocalChain.lc_height (lc_initial 8)) == 0
#guard ((([] : Env Nat) # ["x" ~> 3]) # ("x")) == some 3
#guard
  (ConCert.Execution.Test.TestUtils.contract_base_addr
    (Base := LocalChainBase ConCert.Execution.Test.TestUtils.AddrSize)).val == 128
#guard
  ConCert.Execution.Test.TestUtils.split_at_first_satisfying
    (fun n : Nat => n == 3) [1, 2, 3, 4] == some ([1, 2, 3], [4])

example : (if true then (1 : Nat) else 0) = 1 := by
  destruct_match

example : throwIf false "err" = Ok () := by
  contract_simpl

example (xs : List Nat) : xs.length = xs.length := by
  trace_induction xs

namespace PiggyBankSmoke

local instance : ChainBase := LocalChainBase 8

private def addr0 : ConCert.Execution.BoundedN 8 := ⟨0, by decide⟩
private def addr1 : ConCert.Execution.BoundedN 8 := ⟨1, by decide⟩
private def contractAddr : ConCert.Execution.BoundedN 8 := ⟨4, by decide⟩

private def chain : Chain :=
  { chain_height := 0, current_slot := 0, finalized_height := 0 }

private def ctx (sender : ConCert.Execution.BoundedN 8) (amount : Amount) :
    @ContractCallContext (LocalChainBase 8) :=
  { ctx_origin := sender,
    ctx_from := sender,
    ctx_contract_address := contractAddr,
    ctx_contract_balance := amount,
    ctx_amount := amount }

private def intactState : @ConCert.Examples.PiggyBank.State (LocalChainBase 8) :=
  { balance := 5,
    owner := addr0,
    piggyState := ConCert.Examples.PiggyBank.PiggyState.Intact }

private def initSmoke :=
  ConCert.Examples.PiggyBank.init chain (ctx addr0 5) ()

#guard
  match initSmoke with
  | .Ok st =>
      st.balance == 5 &&
      (match st.piggyState with
       | ConCert.Examples.PiggyBank.PiggyState.Intact => true
       | _ => false)
  | _ => false

private def insertSmoke :=
  ConCert.Examples.PiggyBank.receive chain (ctx addr1 7) intactState
    (some ConCert.Examples.PiggyBank.Msg.Insert)

#guard
  match insertSmoke with
  | .Ok (st, acts) =>
      st.balance == 12 &&
      acts.isEmpty &&
      (match st.piggyState with
       | ConCert.Examples.PiggyBank.PiggyState.Intact => true
       | _ => false)
  | _ => false

private def smashSmoke :=
  ConCert.Examples.PiggyBank.receive chain (ctx addr0 2) intactState
    (some ConCert.Examples.PiggyBank.Msg.Smash)

#guard
  match smashSmoke with
  | .Ok (st, acts) =>
      st.balance == 0 &&
      (match st.piggyState with
       | ConCert.Examples.PiggyBank.PiggyState.Smashed => true
       | _ => false) &&
      (match acts with
       | [.act_transfer to_ amount] =>
           (LocalChainBase 8).address_eqb to_ addr0 && amount == 7
       | _ => false)
  | _ => false

end PiggyBankSmoke

def counterSafeSmoke [BaseTypes : ChainBase] :=
  ConCert.Examples.Counter.counter_safe (BaseTypes := BaseTypes)

def escrowCorrectSmoke [Base : ChainBase] {Cb : @ChainBuilderType Base} :=
  @ConCert.Examples.Escrow.EscrowCorrectness.escrow_correct Base Cb

def main : IO Unit := do
  IO.println "ConCert smoke tests passed"
