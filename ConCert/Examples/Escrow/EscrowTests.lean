/- Port of examples/escrow/tests/EscrowTests.v as executable Lean checkers. -/

import ConCert.Examples.Escrow.EscrowCorrect
import ConCert.Examples.Escrow.EscrowGens
import ConCert.Examples.Escrow.EscrowPrinters

namespace ConCert.Examples.Escrow.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.Escrow
open ConCert.Examples.Escrow.Gens

local instance : ChainBase := TestBase

def escrow_correct_bool {from_ to_ : @ChainState TestBase}
    (caddr : TestAddress)
    (cstate : @State TestBase)
    (trace : @ChainTrace TestBase from_ to_)
    (depinfo : @DeploymentInfo TestBase (@Setup TestBase))
    (inc_calls : List (@ContractCallInfo TestBase Msg)) : Bool :=
  let item_worth := depinfo.deployment_amount / 2
  let seller := depinfo.deployment_from
  let buyer := depinfo.deployment_setup.setup_buyer
  if ConCert.Examples.Escrow.EscrowCorrectness.is_escrow_finished cstate then
    (ConCert.Examples.Escrow.EscrowCorrectness.buyer_confirmed inc_calls buyer &&
      (ConCert.Examples.Escrow.EscrowCorrectness.net_balance_effect trace caddr seller ==
        item_worth) &&
      (ConCert.Examples.Escrow.EscrowCorrectness.net_balance_effect trace caddr buyer ==
        -item_worth)) ||
    (!(ConCert.Examples.Escrow.EscrowCorrectness.buyer_confirmed inc_calls buyer) &&
      (ConCert.Examples.Escrow.EscrowCorrectness.net_balance_effect trace caddr seller ==
        0) &&
      (ConCert.Examples.Escrow.EscrowCorrectness.net_balance_effect trace caddr buyer ==
        0))
  else
    true

def escrow_correct_P (cb : TestLocalChainBuilder) : Bool :=
  let trace := cb.lcb_trace
  let env := lc_to_env AddrSize cb.lcb_lc
  match deployment_info (@Setup TestBase) trace escrow_contract_addr,
      incoming_calls Msg trace escrow_contract_addr,
      @contract_state TestBase (@State TestBase) (inferInstance) env escrow_contract_addr with
  | some depinfo, some inc_calls, some cstate =>
      escrow_correct_bool escrow_contract_addr cstate trace depinfo inc_calls
  | _, _, _ => false

def trace_states :
    ∀ {from_ to_ : @ChainState TestBase},
      @ChainTrace TestBase from_ to_ → List (@ChainState TestBase)
  | _, _, .clnil => []
  | _, to_, .snoc trace' _ => trace_states trace' ++ [to_]

def append_next_step_if_changed (acc : List NextStep) (next : NextStep) :
    List NextStep :=
  match acc.getLast? with
  | none => [next]
  | some prev =>
      if prev = next then acc else acc ++ [next]

def escrow_next_states {from_ to_ : @ChainState TestBase}
    (trace : @ChainTrace TestBase from_ to_) : List NextStep :=
  (trace_states trace).foldl
    (fun acc state =>
      match @contract_state TestBase (@State TestBase) (inferInstance)
          state.toEnvironment escrow_contract_addr with
      | none => acc
      | some escrowState => append_next_step_if_changed acc escrowState.next_step)
    []

def is_valid_step_sequence_fix : List NextStep → Option NextStep → Bool
  | [], _ => true
  | step :: steps, none => is_valid_step_sequence_fix steps (some step)
  | step :: steps, some prev_step =>
      match prev_step, step with
      | .buyer_commit, .buyer_confirm
      | .buyer_commit, .no_next_step
      | .buyer_confirm, .withdrawals
      | .withdrawals, .no_next_step =>
          is_valid_step_sequence_fix steps (some step)
      | _, _ => false

def is_valid_step_sequence (steps : List NextStep) : Bool :=
  is_valid_step_sequence_fix steps none

def escrow_valid_steps_P (cb : TestLocalChainBuilder) : Bool :=
  is_valid_step_sequence (escrow_next_states cb.lcb_trace)

def escrowGeneratedCorrectnessChecker (length : Nat) : Checker :=
  forAllGen (gEscrowChainBuilder length) escrow_correct_P

def escrowGeneratedValidStepsChecker (length : Nat) : Checker :=
  forAllGen (gEscrowChainBuilder length) escrow_valid_steps_P

end ConCert.Examples.Escrow.Tests
