/- Port of execution/theories/BlockchainInduction.v. -/

import ConCert.Execution.ChainedList
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.BlockchainBase
import ConCert.Execution.BlockchainTheories

namespace ConCert.Execution.BlockchainInduction

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.SerializableBase
open ConCert.Execution.ResultMonad
open ConCert.Execution.ChainedList

variable [Base : ChainBase]

inductive TagFacts where | tag_facts
inductive TagAddBlock where | tag_add_block
inductive TagDeployment where | tag_deployment
inductive TagOutgoingAct where | tag_outgoing_act
inductive TagNonrecursiveCall where | tag_nonrecursive_call
inductive TagRecursiveCall where | tag_recursive_call
inductive TagPermuteQueue where | tag_permute_queue

/-- For a given step on a reachable trace, the appropriate facts predicate
    that must hold: `step_block ↦ AddBlockFacts`,
    `eval_deploy ↦ DeployFacts (ctx)`, `eval_call ↦ CallFacts (...)`,
    everything else `True`. -/
def stepFactsPred
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (AddBlockFacts : Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    {bstate_from bstate_to : @ChainState Base}
    (step : ChainStep bstate_from bstate_to)
    (from_reachable : ChainTrace empty_state bstate_from) : Prop :=
  match step with
  | .step_block hdr _ _ _ _ _ =>
    AddBlockFacts bstate_from.chain_height bstate_from.current_slot
                  bstate_from.finalized_height
                  hdr.block_height hdr.block_slot hdr.block_finalized_height
  | .step_action _ _ _ _ eval _ =>
    match eval with
    | .eval_deploy origin frm to_ amount _ _ _ _ _ _ _ _ _ _ _ =>
      DeployFacts
        (transfer_balance frm to_ amount bstate_from.toEnvironment).toChain
        { ctx_origin := origin, ctx_from := frm,
          ctx_contract_address := to_,
          ctx_contract_balance := amount, ctx_amount := amount }
    | .eval_call origin frm to_ amount _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      ∀ cstate : State,
        bstate_from.env_contracts to_ = some (contract_to_weak_contract contract) →
        @contract_state Base State _ bstate_from.toEnvironment to_ = some cstate →
        CallFacts
          (transfer_balance frm to_ amount bstate_from.toEnvironment).toChain
          { ctx_origin := origin, ctx_from := frm,
            ctx_contract_address := to_,
            ctx_contract_balance :=
              (transfer_balance frm to_ amount bstate_from.toEnvironment).env_account_balances to_,
            ctx_amount := amount }
          cstate
          (outgoing_acts bstate_from to_)
          (incoming_calls Msg from_reachable to_)
    | _ => True
  | _ => True

/-- Per-case witnesses of `contract_induction`. Bundled into a structure
    rather than flattened into seven nested `∀…→` premises. -/
structure ContractInductionCases
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (AddBlockFacts :
       Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    (P :
       Nat → Nat → Nat → Base.Address →
       @DeploymentInfo Base Setup → State → Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop) : Prop where
  /-- For every step on a reachable trace, the appropriate facts predicate
      holds. -/
  establish_facts :
    ∀ {bstate_from bstate_to : @ChainState Base}
      (step : ChainStep bstate_from bstate_to)
      (from_reachable : ChainTrace empty_state bstate_from)
      (_tag : TagFacts),
      stepFactsPred contract AddBlockFacts DeployFacts CallFacts step from_reachable
  /-- Adding a block preserves `P` with an empty outgoing-act queue. -/
  add_block_case :
    ∀ (old_h old_s old_f new_h new_s new_f : Nat)
      (caddr : Base.Address)
      (dep_info : @DeploymentInfo Base Setup)
      (state : State) (balance : Amount)
      (inc_calls : List (@ContractCallInfo Base Msg))
      (out_txs : List (@Tx Base)),
      AddBlockFacts old_h old_s old_f new_h new_s new_f →
      P old_h old_s old_f caddr dep_info state balance [] inc_calls out_txs →
      TagAddBlock →
      P new_h new_s new_f caddr dep_info state balance [] inc_calls out_txs
  /-- Deploying establishes `P` at the new state with an empty queue. -/
  init_case :
    ∀ (chain : Chain) (ctx : @ContractCallContext Base)
      (setup : Setup) (result : State),
      DeployFacts chain ctx →
      contract.init chain ctx setup = .Ok result →
      TagDeployment →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address
        { deployment_origin := ctx.ctx_origin,
          deployment_from   := ctx.ctx_from,
          deployment_amount := ctx.ctx_amount,
          deployment_setup  := setup }
        result ctx.ctx_amount [] [] []
  /-- Consuming a queued outgoing action records its `Tx` and decrements
      balance. -/
  outgoing_act_case :
    ∀ (height slot fin_height : Nat) (caddr : Base.Address)
      (dep_info : @DeploymentInfo Base Setup)
      (cstate : State) (balance : Amount)
      (out_act : @ActionBody Base) (out_acts : List (@ActionBody Base))
      (inc_calls : List (@ContractCallInfo Base Msg))
      (prev_out_txs : List (@Tx Base)) (tx : @Tx Base),
      P height slot fin_height caddr dep_info cstate balance
        (out_act :: out_acts) inc_calls prev_out_txs →
      tx.tx_from = caddr →
      tx.tx_amount = act_body_amount out_act →
      (match out_act with
       | .act_transfer to_ amount =>
           tx.tx_to = to_ ∧ tx.tx_amount = amount ∧
           (tx.tx_body = .tx_empty ∨ tx.tx_body = .tx_call none)
       | .act_deploy amount wc setup =>
           tx.tx_amount = amount ∧ tx.tx_body = .tx_deploy wc setup
       | .act_call to_ amount msg =>
           tx.tx_to = to_ ∧ tx.tx_amount = amount ∧
           tx.tx_body = .tx_call (some msg)) →
      TagOutgoingAct →
      P height slot fin_height caddr dep_info cstate
        (balance - act_body_amount out_act) out_acts inc_calls (tx :: prev_out_txs)
  /-- A call from a different address records the incoming-call and
      preserves balance. -/
  nonrecursive_call_case :
    ∀ (chain : Chain) (ctx : @ContractCallContext Base)
      (dep_info : @DeploymentInfo Base Setup)
      (prev_state : State) (msg : Option Msg)
      (prev_out_queue : List (@ActionBody Base))
      (prev_inc_calls : List (@ContractCallInfo Base Msg))
      (prev_out_txs : List (@Tx Base))
      (new_state : State) (new_acts : List (@ActionBody Base)),
      ctx.ctx_from ≠ ctx.ctx_contract_address →
      CallFacts chain ctx prev_state prev_out_queue (some prev_inc_calls) →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info prev_state
        (ctx.ctx_contract_balance - ctx.ctx_amount)
        prev_out_queue prev_inc_calls prev_out_txs →
      contract.receive chain ctx prev_state msg = .Ok (new_state, new_acts) →
      TagNonrecursiveCall →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info new_state
        ctx.ctx_contract_balance
        (new_acts ++ prev_out_queue)
        ({ call_origin := ctx.ctx_origin,
           call_from   := ctx.ctx_from,
           call_amount := ctx.ctx_amount,
           call_msg    := msg } :: prev_inc_calls)
        prev_out_txs
  /-- A call from self pops the head of the queue and records both an
      incoming call and an outgoing tx. -/
  recursive_call_case :
    ∀ (chain : Chain) (ctx : @ContractCallContext Base)
      (dep_info : @DeploymentInfo Base Setup)
      (prev_state : State) (msg : Option Msg)
      (head : @ActionBody Base) (prev_out_queue : List (@ActionBody Base))
      (prev_inc_calls : List (@ContractCallInfo Base Msg))
      (prev_out_txs : List (@Tx Base))
      (new_state : State) (new_acts : List (@ActionBody Base)),
      ctx.ctx_from = ctx.ctx_contract_address →
      CallFacts chain ctx prev_state (head :: prev_out_queue) (some prev_inc_calls) →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info prev_state
        ctx.ctx_contract_balance
        (head :: prev_out_queue) prev_inc_calls prev_out_txs →
      (match head with
       | .act_transfer to_ amount =>
           to_ = ctx.ctx_contract_address ∧ amount = ctx.ctx_amount ∧ msg = none
       | .act_call to_ amount msg_ser =>
           to_ = ctx.ctx_contract_address ∧ amount = ctx.ctx_amount ∧
           msg ≠ none ∧ deserialize msg_ser = msg
       | _ => False) →
      contract.receive chain ctx prev_state msg = .Ok (new_state, new_acts) →
      TagRecursiveCall →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info new_state
        ctx.ctx_contract_balance
        (new_acts ++ prev_out_queue)
        ({ call_origin := ctx.ctx_origin,
           call_from   := ctx.ctx_from,
           call_amount := ctx.ctx_amount,
           call_msg    := msg } :: prev_inc_calls)
        ({ tx_origin := ctx.ctx_origin,
           tx_from   := ctx.ctx_from,
           tx_to     := ctx.ctx_contract_address,
           tx_amount := ctx.ctx_amount,
           tx_body   := .tx_call
                          (match head with
                           | .act_call _ _ m => some m
                           | _ => none) } :: prev_out_txs)
  /-- Permuting the queue preserves `P`. -/
  permute_case :
    ∀ (height slot fin_height : Nat) (caddr : Base.Address)
      (dep_info : @DeploymentInfo Base Setup)
      (cstate : State) (balance : Amount)
      (out_queue : List (@ActionBody Base))
      (inc_calls : List (@ContractCallInfo Base Msg))
      (out_txs : List (@Tx Base))
      (out_queue' : List (@ActionBody Base)),
      P height slot fin_height caddr dep_info cstate balance
        out_queue inc_calls out_txs →
      List.Perm out_queue out_queue' →
      TagPermuteQueue →
      P height slot fin_height caddr dep_info cstate balance
        out_queue' inc_calls out_txs

/-- Non-recursive variant of `ContractInductionCases`: drops the
    `recursive_call_case` field. -/
structure NonRecursiveContractInductionCases
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (AddBlockFacts :
       Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    (P :
       Nat → Nat → Nat → Base.Address →
       @DeploymentInfo Base Setup → State → Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop) : Prop where
  establish_facts :
    ∀ {bstate_from bstate_to : @ChainState Base}
      (step : ChainStep bstate_from bstate_to)
      (from_reachable : ChainTrace empty_state bstate_from)
      (_tag : TagFacts),
      stepFactsPred contract AddBlockFacts DeployFacts CallFacts step from_reachable
  add_block_case :
    ∀ (old_h old_s old_f new_h new_s new_f : Nat)
      (caddr : Base.Address)
      (dep_info : @DeploymentInfo Base Setup)
      (state : State) (balance : Amount)
      (inc_calls : List (@ContractCallInfo Base Msg))
      (out_txs : List (@Tx Base)),
      AddBlockFacts old_h old_s old_f new_h new_s new_f →
      P old_h old_s old_f caddr dep_info state balance [] inc_calls out_txs →
      TagAddBlock →
      P new_h new_s new_f caddr dep_info state balance [] inc_calls out_txs
  init_case :
    ∀ (chain : Chain) (ctx : @ContractCallContext Base)
      (setup : Setup) (result : State),
      DeployFacts chain ctx →
      contract.init chain ctx setup = .Ok result →
      TagDeployment →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address
        { deployment_origin := ctx.ctx_origin,
          deployment_from   := ctx.ctx_from,
          deployment_amount := ctx.ctx_amount,
          deployment_setup  := setup }
        result ctx.ctx_amount [] [] []
  outgoing_act_case :
    ∀ (height slot fin_height : Nat) (caddr : Base.Address)
      (dep_info : @DeploymentInfo Base Setup)
      (cstate : State) (balance : Amount)
      (out_act : @ActionBody Base) (out_acts : List (@ActionBody Base))
      (inc_calls : List (@ContractCallInfo Base Msg))
      (prev_out_txs : List (@Tx Base)) (tx : @Tx Base),
      P height slot fin_height caddr dep_info cstate balance
        (out_act :: out_acts) inc_calls prev_out_txs →
      tx.tx_from = caddr →
      tx.tx_amount = act_body_amount out_act →
      (match out_act with
       | .act_transfer to_ amount =>
           tx.tx_to = to_ ∧ tx.tx_amount = amount ∧
           (tx.tx_body = .tx_empty ∨ tx.tx_body = .tx_call none)
       | .act_deploy amount wc setup =>
           tx.tx_amount = amount ∧ tx.tx_body = .tx_deploy wc setup
       | .act_call to_ amount msg =>
           tx.tx_to = to_ ∧ tx.tx_amount = amount ∧
           tx.tx_body = .tx_call (some msg)) →
      TagOutgoingAct →
      P height slot fin_height caddr dep_info cstate
        (balance - act_body_amount out_act) out_acts inc_calls (tx :: prev_out_txs)
  nonrecursive_call_case :
    ∀ (chain : Chain) (ctx : @ContractCallContext Base)
      (dep_info : @DeploymentInfo Base Setup)
      (prev_state : State) (msg : Option Msg)
      (prev_out_queue : List (@ActionBody Base))
      (prev_inc_calls : List (@ContractCallInfo Base Msg))
      (prev_out_txs : List (@Tx Base))
      (new_state : State) (new_acts : List (@ActionBody Base)),
      ctx.ctx_from ≠ ctx.ctx_contract_address →
      CallFacts chain ctx prev_state prev_out_queue (some prev_inc_calls) →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info prev_state
        (ctx.ctx_contract_balance - ctx.ctx_amount)
        prev_out_queue prev_inc_calls prev_out_txs →
      contract.receive chain ctx prev_state msg = .Ok (new_state, new_acts) →
      TagNonrecursiveCall →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info new_state
        ctx.ctx_contract_balance
        (new_acts ++ prev_out_queue)
        ({ call_origin := ctx.ctx_origin,
           call_from   := ctx.ctx_from,
           call_amount := ctx.ctx_amount,
           call_msg    := msg } :: prev_inc_calls)
        prev_out_txs
  permute_case :
    ∀ (height slot fin_height : Nat) (caddr : Base.Address)
      (dep_info : @DeploymentInfo Base Setup)
      (cstate : State) (balance : Amount)
      (out_queue : List (@ActionBody Base))
      (inc_calls : List (@ContractCallInfo Base Msg))
      (out_txs : List (@Tx Base))
      (out_queue' : List (@ActionBody Base)),
      P height slot fin_height caddr dep_info cstate balance
        out_queue inc_calls out_txs →
      List.Perm out_queue out_queue' →
      TagPermuteQueue →
      P height slot fin_height caddr dep_info cstate balance
        out_queue' inc_calls out_txs

/-- DFS variant of `ContractInductionCases`: drops the `permute_case`
    field. Used by `dfs_contract_induction`, which only quantifies over
    traces without permutation steps. -/
structure DFSContractInductionCases
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (AddBlockFacts :
       Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    (P :
       Nat → Nat → Nat → Base.Address →
       @DeploymentInfo Base Setup → State → Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop) : Prop where
  establish_facts :
    ∀ {bstate_from bstate_to : @ChainState Base}
      (step : ChainStep bstate_from bstate_to)
      (from_reachable : ChainTrace empty_state bstate_from)
      (_tag : TagFacts),
      stepFactsPred contract AddBlockFacts DeployFacts CallFacts step from_reachable
  add_block_case :
    ∀ (old_h old_s old_f new_h new_s new_f : Nat)
      (caddr : Base.Address)
      (dep_info : @DeploymentInfo Base Setup)
      (state : State) (balance : Amount)
      (inc_calls : List (@ContractCallInfo Base Msg))
      (out_txs : List (@Tx Base)),
      AddBlockFacts old_h old_s old_f new_h new_s new_f →
      P old_h old_s old_f caddr dep_info state balance [] inc_calls out_txs →
      TagAddBlock →
      P new_h new_s new_f caddr dep_info state balance [] inc_calls out_txs
  init_case :
    ∀ (chain : Chain) (ctx : @ContractCallContext Base)
      (setup : Setup) (result : State),
      DeployFacts chain ctx →
      contract.init chain ctx setup = .Ok result →
      TagDeployment →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address
        { deployment_origin := ctx.ctx_origin,
          deployment_from   := ctx.ctx_from,
          deployment_amount := ctx.ctx_amount,
          deployment_setup  := setup }
        result ctx.ctx_amount [] [] []
  outgoing_act_case :
    ∀ (height slot fin_height : Nat) (caddr : Base.Address)
      (dep_info : @DeploymentInfo Base Setup)
      (cstate : State) (balance : Amount)
      (out_act : @ActionBody Base) (out_acts : List (@ActionBody Base))
      (inc_calls : List (@ContractCallInfo Base Msg))
      (prev_out_txs : List (@Tx Base)) (tx : @Tx Base),
      P height slot fin_height caddr dep_info cstate balance
        (out_act :: out_acts) inc_calls prev_out_txs →
      tx.tx_from = caddr →
      tx.tx_amount = act_body_amount out_act →
      (match out_act with
       | .act_transfer to_ amount =>
           tx.tx_to = to_ ∧ tx.tx_amount = amount ∧
           (tx.tx_body = .tx_empty ∨ tx.tx_body = .tx_call none)
       | .act_deploy amount wc setup =>
           tx.tx_amount = amount ∧ tx.tx_body = .tx_deploy wc setup
       | .act_call to_ amount msg =>
           tx.tx_to = to_ ∧ tx.tx_amount = amount ∧
           tx.tx_body = .tx_call (some msg)) →
      TagOutgoingAct →
      P height slot fin_height caddr dep_info cstate
        (balance - act_body_amount out_act) out_acts inc_calls (tx :: prev_out_txs)
  nonrecursive_call_case :
    ∀ (chain : Chain) (ctx : @ContractCallContext Base)
      (dep_info : @DeploymentInfo Base Setup)
      (prev_state : State) (msg : Option Msg)
      (prev_out_queue : List (@ActionBody Base))
      (prev_inc_calls : List (@ContractCallInfo Base Msg))
      (prev_out_txs : List (@Tx Base))
      (new_state : State) (new_acts : List (@ActionBody Base)),
      ctx.ctx_from ≠ ctx.ctx_contract_address →
      CallFacts chain ctx prev_state prev_out_queue (some prev_inc_calls) →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info prev_state
        (ctx.ctx_contract_balance - ctx.ctx_amount)
        prev_out_queue prev_inc_calls prev_out_txs →
      contract.receive chain ctx prev_state msg = .Ok (new_state, new_acts) →
      TagNonrecursiveCall →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info new_state
        ctx.ctx_contract_balance
        (new_acts ++ prev_out_queue)
        ({ call_origin := ctx.ctx_origin,
           call_from   := ctx.ctx_from,
           call_amount := ctx.ctx_amount,
           call_msg    := msg } :: prev_inc_calls)
        prev_out_txs
  recursive_call_case :
    ∀ (chain : Chain) (ctx : @ContractCallContext Base)
      (dep_info : @DeploymentInfo Base Setup)
      (prev_state : State) (msg : Option Msg)
      (head : @ActionBody Base) (prev_out_queue : List (@ActionBody Base))
      (prev_inc_calls : List (@ContractCallInfo Base Msg))
      (prev_out_txs : List (@Tx Base))
      (new_state : State) (new_acts : List (@ActionBody Base)),
      ctx.ctx_from = ctx.ctx_contract_address →
      CallFacts chain ctx prev_state (head :: prev_out_queue) (some prev_inc_calls) →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info prev_state
        ctx.ctx_contract_balance
        (head :: prev_out_queue) prev_inc_calls prev_out_txs →
      (match head with
       | .act_transfer to_ amount =>
           to_ = ctx.ctx_contract_address ∧ amount = ctx.ctx_amount ∧ msg = none
       | .act_call to_ amount msg_ser =>
           to_ = ctx.ctx_contract_address ∧ amount = ctx.ctx_amount ∧
           msg ≠ none ∧ deserialize msg_ser = msg
       | _ => False) →
      contract.receive chain ctx prev_state msg = .Ok (new_state, new_acts) →
      TagRecursiveCall →
      P chain.chain_height chain.current_slot chain.finalized_height
        ctx.ctx_contract_address dep_info new_state
        ctx.ctx_contract_balance
        (new_acts ++ prev_out_queue)
        ({ call_origin := ctx.ctx_origin,
           call_from   := ctx.ctx_from,
           call_amount := ctx.ctx_amount,
           call_msg    := msg } :: prev_inc_calls)
        ({ tx_origin := ctx.ctx_origin,
           tx_from   := ctx.ctx_from,
           tx_to     := ctx.ctx_contract_address,
           tx_amount := ctx.ctx_amount,
           tx_body   := .tx_call
                          (match head with
                           | .act_call _ _ m => some m
                           | _ => none) } :: prev_out_txs)

/-- The general contract induction principle.

    Given a contract `c`, three "facts" predicates supplying premises for
    each step kind, and a property `P` over the full operational state,
    plus the seven `ContractInductionCases` witnesses, conclude that for
    every reachable state where `c` is deployed, there exist deployment
    info / state / incoming calls satisfying `P`. -/
axiom contract_induction :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (AddBlockFacts : Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    (P :
       Nat → Nat → Nat → Base.Address →
       @DeploymentInfo Base Setup → State → Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop),
    ContractInductionCases contract AddBlockFacts DeployFacts CallFacts P →
    ∀ (bstate : @ChainState Base) (caddr : Base.Address)
      (trace : ChainTrace empty_state bstate),
      bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
      ∃ (dep : @DeploymentInfo Base Setup) (cstate : State)
        (inc_calls : List (@ContractCallInfo Base Msg)),
        deployment_info Setup trace caddr = some dep ∧
        @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
        incoming_calls Msg trace caddr = some inc_calls ∧
        P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
          dep cstate (bstate.env_account_balances caddr)
          (outgoing_acts bstate caddr) inc_calls
          (outgoing_txs trace caddr)

/-- If a property `P` holds for every action produced by the receive
    function, then it holds for every action in the outgoing queue of any
    reachable state where the contract is deployed. -/
axiom lift_outgoing_acts_prop :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {Q : @ActionBody Base → Prop}
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base) (caddr : Base.Address),
    reachable bstate →
    (∀ (chain : Chain) (ctx : @ContractCallContext Base) (cstate : State)
       (msg : Option Msg) (new_cstate : State) (acts : List (@ActionBody Base)),
       contract.receive chain ctx cstate msg = .Ok (new_cstate, acts) →
       acts.Forall Q) →
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    (outgoing_acts bstate caddr).Forall Q

/-- If the receive function always returns an empty action list, the
    outgoing queue is always empty. -/
axiom lift_outgoing_acts_nil :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base) (caddr : Base.Address),
    reachable bstate →
    (∀ (chain : Chain) (ctx : @ContractCallContext Base) (cstate : State)
       (msg : Option Msg) (new_cstate : State) (acts : List (@ActionBody Base)),
       contract.receive chain ctx cstate msg = .Ok (new_cstate, acts) →
       acts = []) →
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    outgoing_acts bstate caddr = []

/-- If a property `P` is preserved by both `init` (initial result satisfies
    `P`) and `receive` (`P` on input cstate ⇒ `P` on output cstate), then
    `P` holds for the contract's state at every reachable point. -/
axiom lift_contract_state_prop :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {Q : State → Prop}
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base) (caddr : Base.Address),
    (∀ (chain : Chain) (ctx : @ContractCallContext Base) (setup : Setup)
       (result : State),
       contract.init chain ctx setup = .Ok result → Q result) →
    (∀ (chain : Chain) (ctx : @ContractCallContext Base) (cstate : State)
       (msg : Option Msg) (new_cstate : State) (acts : List (@ActionBody Base)),
       Q cstate →
       contract.receive chain ctx cstate msg = .Ok (new_cstate, acts) →
       Q new_cstate) →
    reachable bstate →
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    ∃ cstate, @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
              Q cstate

/-- Same as `lift_contract_state_prop` but carrying the deployment info
    alongside the state. -/
axiom lift_dep_info_contract_state_prop :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {Q : @DeploymentInfo Base Setup → State → Prop}
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate),
    (∀ (chain : Chain) (ctx : @ContractCallContext Base) (setup : Setup)
       (result : State),
       contract.init chain ctx setup = .Ok result →
       Q { deployment_origin := ctx.ctx_origin,
           deployment_from   := ctx.ctx_from,
           deployment_amount := ctx.ctx_amount,
           deployment_setup  := setup } result) →
    (∀ (chain : Chain) (ctx : @ContractCallContext Base) (cstate : State)
       (msg : Option Msg) (new_cstate : State) (acts : List (@ActionBody Base))
       (dep : @DeploymentInfo Base Setup),
       Q dep cstate →
       contract.receive chain ctx cstate msg = .Ok (new_cstate, acts) →
       Q dep new_cstate) →
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    ∃ dep cstate,
      deployment_info Setup trace caddr = some dep ∧
      @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
      Q dep cstate

end ConCert.Execution.BlockchainInduction
