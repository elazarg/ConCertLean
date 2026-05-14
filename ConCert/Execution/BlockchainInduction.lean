/- Port of execution/theories/BlockchainInduction.v. -/

import ConCert.Execution.ChainedList
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.BlockchainBase
import ConCert.Execution.BlockchainTheories
import ConCert.Utils.Extras
import Mathlib.Tactic.Linarith

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

/-- Flat constructor alias for proof ports that prefer Rocq-style positional
    case premises over record literals. -/
abbrev contract_induction_cases := @ContractInductionCases.mk

/-- Flat constructor alias for proof ports that prefer Rocq-style positional
    case premises over record literals. -/
abbrev nonrecursive_contract_induction_cases := @NonRecursiveContractInductionCases.mk

/-- Flat constructor alias for proof ports that prefer Rocq-style positional
    case premises over record literals. -/
abbrev dfs_contract_induction_cases := @DFSContractInductionCases.mk

private theorem contract_state_env_equiv
    {State : Type} [Serializable State]
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env')
    (addr : Base.Address) :
    @contract_state Base State _ env addr =
      @contract_state Base State _ env' addr := by
  unfold contract_state
  rw [henv.contract_states_eq addr]

private theorem chain_height_env_equiv
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env') :
    env.chain_height = env'.chain_height := by
  simpa [env_chain] using congrArg Chain.chain_height henv.chain_eq

private theorem current_slot_env_equiv
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env') :
    env.current_slot = env'.current_slot := by
  simpa [env_chain] using congrArg Chain.current_slot henv.chain_eq

private theorem finalized_height_env_equiv
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env') :
    env.finalized_height = env'.finalized_height := by
  simpa [env_chain] using congrArg Chain.finalized_height henv.chain_eq

omit Base in
private theorem forall_cons_head
    {A : Type} {P : A → Prop} {x : A} {xs : List A}
    (h : (x :: xs).Forall P) : P x := by
  rw [← ConCert.Utils.Extras.All_Forall] at h
  exact h.1

omit Base in
private theorem forall_cons_tail
    {A : Type} {P : A → Prop} {x : A} {xs : List A}
    (h : (x :: xs).Forall P) : xs.Forall P := by
  rw [← ConCert.Utils.Extras.All_Forall] at h ⊢
  exact h.2

private def call_action_body (to_addr : Base.Address) (amount : Amount) :
    Option SerializedValue → @ActionBody Base
  | none => .act_transfer to_addr amount
  | some msg_ser => .act_call to_addr amount msg_ser

private theorem call_action_body_tx_msg
    (to_addr : Base.Address) (amount : Amount) (msg : Option SerializedValue) :
    (match call_action_body (Base := Base) to_addr amount msg with
     | .act_call _ _ msg_ser => some msg_ser
     | _ => none) = msg := by
  cases msg <;> rfl

private theorem call_action_match_tx_msg
    (to_addr : Base.Address) (amount : Amount) (msg : Option SerializedValue) :
    (match (match msg with
            | none => ActionBody.act_transfer to_addr amount
            | some msg_ser => ActionBody.act_call to_addr amount msg_ser) with
     | .act_call _ _ msg_ser => some msg_ser
     | _ => none) = msg := by
  cases msg <;> rfl

private theorem mapped_actions_outgoing_self
    (origin addr : Base.Address) (bodies : List (@ActionBody Base)) :
    ((bodies.map (fun b =>
        ({ act_origin := origin, act_from := addr, act_body := b } : @Action Base))).filter
      (fun a => Base.address_eqb a.act_from addr)).map (fun a => a.act_body) =
      bodies := by
  induction bodies with
  | nil => simp
  | cons body bodies ih =>
      simp [Address.address_eq_refl addr, ih]

/-- The general contract induction principle.

    Given a contract `c`, three "facts" predicates supplying premises for
    each step kind, and a property `P` over the full operational state,
    plus the seven `ContractInductionCases` witnesses, conclude that for
    every reachable state where `c` is deployed, there exist deployment
    info / state / incoming calls satisfying `P`. -/
theorem contract_induction :
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
          (outgoing_txs trace caddr) := by
  intro Setup Msg State Error _ _ _ _ contract AddBlockFacts DeployFacts CallFacts P hCases
    bstate caddr trace hdeployed
  induction trace with
  | clnil =>
      simp [empty_state] at hdeployed
  | @snoc mid to_ tail step ih =>
      have hfacts := hCases.establish_facts step tail TagFacts.tag_facts
      cases step with
      | step_block header hq_empty hvalid hqueue_accounts _hqueue_origins henv =>
          have hpre_deployed :
              mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
            have hdeployed' :
                (add_new_block_to_env header mid.toEnvironment).env_contracts caddr =
                  some (contract_to_weak_contract contract) := by
              rw [← henv.contracts_eq caddr]
              exact hdeployed
            simpa [add_new_block_to_env] using hdeployed'
          obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ := ih hpre_deployed
          refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
          · simpa [deployment_info, step_deployment_info] using hdep
          · rw [contract_state_env_equiv henv caddr]
            simpa [add_new_block_to_env] using hstate
          · simp [incoming_calls, step_incoming_calls, hinc]
          · have haddr_contract : Base.address_is_contract caddr = true :=
              contract_addr_format caddr (contract_to_weak_contract contract)
                (trace_reachable (ChainedList.snoc tail
                  (ChainStep.step_block header hq_empty hvalid hqueue_accounts
                    _hqueue_origins henv))) hdeployed
            have hqueue_mid : outgoing_acts mid caddr = [] := by
              simp [outgoing_acts, hq_empty]
            have hqueue_to : outgoing_acts to_ caddr = [] :=
              outgoing_acts_after_block_nil to_ caddr hqueue_accounts haddr_contract
            have hne_creator : caddr ≠ header.block_creator := by
              intro heq
              rw [heq, hvalid.valid_creator] at haddr_contract
              cases haddr_contract
            have hbalance :
                to_.env_account_balances caddr = mid.env_account_balances caddr := by
              rw [henv.account_balances_eq caddr]
              simp [add_new_block_to_env, add_balance,
                Address.address_eq_ne caddr header.block_creator hne_creator]
            have hheight : to_.chain_height = header.block_height := by
              simpa [add_new_block_to_env] using chain_height_env_equiv henv
            have hslot : to_.current_slot = header.block_slot := by
              simpa [add_new_block_to_env] using current_slot_env_equiv henv
            have hfin : to_.finalized_height = header.block_finalized_height := by
              simpa [add_new_block_to_env] using finalized_height_env_equiv henv
            have hP_old :
                P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                  (mid.env_account_balances caddr) [] inc_calls (outgoing_txs tail caddr) := by
              simpa [hqueue_mid] using hP
            have hP_new :=
              hCases.add_block_case mid.chain_height mid.current_slot mid.finalized_height
                header.block_height header.block_slot header.block_finalized_height
                caddr dep cstate (mid.env_account_balances caddr) inc_calls
                (outgoing_txs tail caddr)
                (by simpa [stepFactsPred] using hfacts) hP_old TagAddBlock.tag_add_block
            simpa [hheight, hslot, hfin, hbalance, hqueue_to,
              outgoing_txs, trace_txs, step_txs] using hP_new
      | step_action act acts new_acts hq_prev eval hq_next =>
          have hreachable_to : reachable to_ :=
            trace_reachable (ChainedList.snoc tail
              (ChainStep.step_action act acts new_acts hq_prev eval hq_next))
          cases eval with
          | eval_transfer origin from_addr to_addr amount hamount hbalance hnot_contract hact henv hnew =>
              have hpre_deployed :
                  mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
                have hdeployed' :
                    (transfer_balance from_addr to_addr amount mid.toEnvironment).env_contracts
                        caddr =
                      some (contract_to_weak_contract contract) := by
                  rw [← henv.contracts_eq caddr]
                  exact hdeployed
                simpa [transfer_balance] using hdeployed'
              obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ := ih hpre_deployed
              have haddr_contract : Base.address_is_contract caddr = true :=
                contract_addr_format caddr (contract_to_weak_contract contract)
                  hreachable_to hdeployed
              have hne_to : caddr ≠ to_addr := by
                intro heq
                rw [heq, hnot_contract] at haddr_contract
                cases haddr_contract
              refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
              · simpa [deployment_info, step_deployment_info, eval_tx,
                  Address.address_eq_ne to_addr caddr (Ne.symm hne_to)] using hdep
              · rw [contract_state_env_equiv henv caddr]
                simpa [transfer_balance] using hstate
              · simp [incoming_calls, step_incoming_calls, eval_tx,
                  Address.address_eq_ne to_addr caddr (Ne.symm hne_to), hinc]
              · have hheight : to_.chain_height = mid.chain_height := by
                  simpa [transfer_balance] using chain_height_env_equiv henv
                have hslot : to_.current_slot = mid.current_slot := by
                  simpa [transfer_balance] using current_slot_env_equiv henv
                have hfin : to_.finalized_height = mid.finalized_height := by
                  simpa [transfer_balance] using finalized_height_env_equiv henv
                by_cases hfrom_eq : caddr = from_addr
                · subst from_addr
                  have hqueue_old :
                      outgoing_acts mid caddr =
                        ActionBody.act_transfer to_addr amount :: outgoing_acts to_ caddr := by
                    simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                      Address.address_eq_refl caddr]
                  have hbalance_to :
                      to_.env_account_balances caddr =
                        mid.env_account_balances caddr -
                          act_body_amount (ActionBody.act_transfer to_addr amount) := by
                    rw [henv.account_balances_eq caddr]
                    simp [transfer_balance, add_balance, act_body_amount,
                      Address.address_eq_refl caddr,
                      Address.address_eq_ne caddr to_addr hne_to]
                    ring
                  have hP_old :
                      P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                        (mid.env_account_balances caddr)
                        (ActionBody.act_transfer to_addr amount :: outgoing_acts to_ caddr)
                        inc_calls (outgoing_txs tail caddr) := by
                    simpa [hqueue_old] using hP
                  let tx : @Tx Base :=
                    { tx_origin := origin, tx_from := caddr, tx_to := to_addr,
                      tx_amount := amount, tx_body := .tx_empty }
                  have hP_new :=
                    hCases.outgoing_act_case mid.chain_height mid.current_slot
                      mid.finalized_height caddr dep cstate
                      (mid.env_account_balances caddr)
                      (ActionBody.act_transfer to_addr amount) (outgoing_acts to_ caddr)
                      inc_calls (outgoing_txs tail caddr) tx
                      hP_old rfl rfl (And.intro rfl (And.intro rfl (Or.inl rfl)))
                      TagOutgoingAct.tag_outgoing_act
                  simpa [hheight, hslot, hfin, hbalance_to, outgoing_txs, trace_txs,
                    step_txs, eval_tx, tx, Address.address_eq_refl caddr] using hP_new
                · have hfrom_false_caddr :
                      Base.address_eqb from_addr caddr = false :=
                    Address.address_eq_ne from_addr caddr (Ne.symm hfrom_eq)
                  have hfrom_false :
                      Base.address_eqb caddr from_addr = false :=
                    Address.address_eq_ne caddr from_addr hfrom_eq
                  have hto_false :
                      Base.address_eqb caddr to_addr = false :=
                    Address.address_eq_ne caddr to_addr hne_to
                  have hqueue_eq :
                      outgoing_acts mid caddr = outgoing_acts to_ caddr := by
                    simp [outgoing_acts, hq_prev, hq_next, hnew, hact, hfrom_false_caddr]
                  have hbalance_to :
                      to_.env_account_balances caddr = mid.env_account_balances caddr := by
                    rw [henv.account_balances_eq caddr]
                    simp [transfer_balance, add_balance, hfrom_false, hto_false]
                  simpa [hheight, hslot, hfin, hbalance_to, hqueue_eq, outgoing_txs,
                    trace_txs, step_txs, eval_tx, hfrom_false_caddr] using hP
          | eval_deploy origin from_addr to_addr amount wc setup state hamount hbalance hcontract_addr hnot_deployed hact hinit henv hnew =>
              have hheight : to_.chain_height = mid.chain_height := by
                simpa [set_contract_state, add_contract, transfer_balance] using
                  chain_height_env_equiv henv
              have hslot : to_.current_slot = mid.current_slot := by
                simpa [set_contract_state, add_contract, transfer_balance] using
                  current_slot_env_equiv henv
              have hfin : to_.finalized_height = mid.finalized_height := by
                simpa [set_contract_state, add_contract, transfer_balance] using
                  finalized_height_env_equiv henv
              by_cases hto_eq : caddr = to_addr
              · subst to_addr
                have hwc : wc = contract_to_weak_contract contract := by
                  have hdeployed' :
                      (set_contract_state caddr state
                          (add_contract caddr wc
                            (transfer_balance from_addr caddr amount mid.toEnvironment))).env_contracts
                          caddr =
                        some (contract_to_weak_contract contract) := by
                    rw [← henv.contracts_eq caddr]
                    exact hdeployed
                  exact Option.some.inj
                    (by
                      simpa [set_contract_state, add_contract,
                        Address.address_eq_refl caddr] using hdeployed')
                subst wc
                obtain ⟨setup_strong, result_strong, hsetup, hstate_ser, hinit_strong⟩ :=
                  wc_init_strong (contract := contract) hinit
                let dep : @DeploymentInfo Base Setup :=
                  { deployment_origin := origin, deployment_from := from_addr,
                    deployment_amount := amount, deployment_setup := setup_strong }
                let ctx : @ContractCallContext Base :=
                  { ctx_origin := origin, ctx_from := from_addr,
                    ctx_contract_address := caddr,
                    ctx_contract_balance := amount, ctx_amount := amount }
                have hno_out_queue :=
                  undeployed_contract_no_out_queue caddr mid (trace_reachable tail)
                    hcontract_addr hnot_deployed
                have hno_out_queue_cons :
                    ({ act_origin := origin, act_from := from_addr,
                       act_body := ActionBody.act_deploy amount
                         (contract_to_weak_contract contract) setup } :: acts).Forall
                      (fun a => Base.address_eqb a.act_from caddr = false) := by
                  simpa [hq_prev, hact] using hno_out_queue
                have hfrom_false :
                    Base.address_eqb from_addr caddr = false := by
                  let deployedAction : @Action Base :=
                    { act_origin := origin, act_from := from_addr,
                      act_body := ActionBody.act_deploy amount
                        (contract_to_weak_contract contract) setup }
                  have hno_out_queue_cons' :
                      (deployedAction :: acts).Forall
                        (fun a => Base.address_eqb a.act_from caddr = false) := by
                    simpa [deployedAction] using hno_out_queue_cons
                  have hhead :
                      Base.address_eqb deployedAction.act_from caddr = false :=
                    @forall_cons_head (@Action Base)
                      (fun a => Base.address_eqb a.act_from caddr = false)
                      deployedAction acts hno_out_queue_cons'
                  simpa [deployedAction] using hhead
                have hfrom_false_sym :
                    Base.address_eqb caddr from_addr = false := by
                  rw [Address.address_eq_sym]
                  exact hfrom_false
                have hacts_no_out :
                    acts.Forall (fun a => Base.address_eqb a.act_from caddr = false) :=
                  forall_cons_tail hno_out_queue_cons
                have hqueue_to_no_out :
                    to_.chain_state_queue.Forall
                      (fun a => Base.address_eqb a.act_from caddr = false) := by
                  rw [hq_next, hnew]
                  simpa using hacts_no_out
                have hqueue_to : outgoing_acts to_ caddr = [] :=
                  outgoing_acts_after_deploy_nil to_ caddr hqueue_to_no_out
                have hin_tail : incoming_calls Msg tail caddr = some [] :=
                  undeployed_contract_no_in_calls caddr tail hcontract_addr hnot_deployed
                have hout_tail : outgoing_txs tail caddr = [] :=
                  undeployed_contract_no_out_txs caddr tail hcontract_addr hnot_deployed
                have hbalance_zero :
                    mid.env_account_balances caddr = 0 :=
                  undeployed_contract_balance_0 mid caddr (trace_reachable tail)
                    hcontract_addr hnot_deployed
                have hbalance_to : to_.env_account_balances caddr = amount := by
                  rw [henv.account_balances_eq caddr]
                  simp [set_contract_state, add_contract, transfer_balance, add_balance,
                    Address.address_eq_refl caddr, hfrom_false_sym, hbalance_zero]
                refine ⟨dep, result_strong, [], ?_, ?_, ?_, ?_⟩
                · simp [dep, deployment_info, step_deployment_info, eval_tx,
                    Address.address_eq_refl caddr, hsetup]
                · rw [contract_state_env_equiv henv caddr]
                  simp [contract_state, set_contract_state, set_chain_contract_state,
                    Address.address_eq_refl caddr, ← hstate_ser,
                    Serializable.deserialize_serialize]
                · simp [incoming_calls, step_incoming_calls, eval_tx,
                    Address.address_eq_refl caddr, hin_tail]
                · have hdeploy_facts :
                      DeployFacts
                        (transfer_balance from_addr caddr amount mid.toEnvironment).toChain ctx := by
                    simpa [stepFactsPred, ctx] using hfacts
                  have hP_init :=
                    hCases.init_case
                      (transfer_balance from_addr caddr amount mid.toEnvironment).toChain
                      ctx setup_strong result_strong hdeploy_facts hinit_strong
                      TagDeployment.tag_deployment
                  have hout_trace :
                      outgoing_txs
                          (ChainedList.snoc tail
                            (ChainStep.step_action act acts new_acts hq_prev
                              (ActionEvaluation.eval_deploy origin from_addr caddr amount
                                (contract_to_weak_contract contract) setup state
                                hamount hbalance hcontract_addr hnot_deployed hact hinit henv hnew)
                              hq_next))
                          caddr = [] := by
                    simp [outgoing_txs, trace_txs, step_txs, eval_tx, hfrom_false]
                    simpa [outgoing_txs] using hout_tail
                  simpa [ctx, dep, hheight, hslot, hfin, hbalance_to, hqueue_to,
                    hout_trace, transfer_balance] using hP_init
              · have hto_false_caddr :
                    Base.address_eqb to_addr caddr = false :=
                  Address.address_eq_ne to_addr caddr (Ne.symm hto_eq)
                have hto_false :
                    Base.address_eqb caddr to_addr = false :=
                  Address.address_eq_ne caddr to_addr hto_eq
                have hpre_deployed :
                    mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
                  have hdeployed' :
                      (set_contract_state to_addr state
                          (add_contract to_addr wc
                            (transfer_balance from_addr to_addr amount mid.toEnvironment))).env_contracts
                          caddr =
                        some (contract_to_weak_contract contract) := by
                    rw [← henv.contracts_eq caddr]
                    exact hdeployed
                  simpa [set_contract_state, add_contract, hto_false] using hdeployed'
                obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ :=
                  ih hpre_deployed
                refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
                · simpa [deployment_info, step_deployment_info, eval_tx,
                    hto_false_caddr] using hdep
                · rw [contract_state_env_equiv henv caddr]
                  simpa [contract_state, set_contract_state, set_chain_contract_state,
                    hto_false] using hstate
                · simp [incoming_calls, step_incoming_calls, eval_tx,
                    hto_false_caddr, hinc]
                · by_cases hfrom_eq : caddr = from_addr
                  · subst from_addr
                    have hqueue_old :
                        outgoing_acts mid caddr =
                          ActionBody.act_deploy amount wc setup :: outgoing_acts to_ caddr := by
                      simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                        Address.address_eq_refl caddr]
                    have hbalance_to :
                        to_.env_account_balances caddr =
                          mid.env_account_balances caddr -
                            act_body_amount (ActionBody.act_deploy amount wc setup) := by
                      rw [henv.account_balances_eq caddr]
                      simp [set_contract_state, add_contract, transfer_balance,
                        add_balance, act_body_amount, Address.address_eq_refl caddr,
                        hto_false]
                      ring
                    have hP_old :
                        P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                          (mid.env_account_balances caddr)
                          (ActionBody.act_deploy amount wc setup :: outgoing_acts to_ caddr)
                          inc_calls (outgoing_txs tail caddr) := by
                      simpa [hqueue_old] using hP
                    let tx : @Tx Base :=
                      { tx_origin := origin, tx_from := caddr, tx_to := to_addr,
                        tx_amount := amount, tx_body := .tx_deploy wc setup }
                    have hP_new :=
                      hCases.outgoing_act_case mid.chain_height mid.current_slot
                        mid.finalized_height caddr dep cstate
                        (mid.env_account_balances caddr)
                        (ActionBody.act_deploy amount wc setup) (outgoing_acts to_ caddr)
                        inc_calls (outgoing_txs tail caddr) tx
                        hP_old rfl rfl (And.intro rfl rfl)
                        TagOutgoingAct.tag_outgoing_act
                    simpa [hheight, hslot, hfin, hbalance_to, outgoing_txs, trace_txs,
                      step_txs, eval_tx, tx, Address.address_eq_refl caddr] using hP_new
                  · have hfrom_false_caddr :
                        Base.address_eqb from_addr caddr = false :=
                      Address.address_eq_ne from_addr caddr (Ne.symm hfrom_eq)
                    have hfrom_false :
                        Base.address_eqb caddr from_addr = false :=
                      Address.address_eq_ne caddr from_addr hfrom_eq
                    have hqueue_eq :
                        outgoing_acts mid caddr = outgoing_acts to_ caddr := by
                      simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                        hfrom_false_caddr]
                    have hbalance_to :
                        to_.env_account_balances caddr = mid.env_account_balances caddr := by
                      rw [henv.account_balances_eq caddr]
                      simp [set_contract_state, add_contract, transfer_balance,
                        add_balance, hfrom_false, hto_false]
                    simpa [hheight, hslot, hfin, hbalance_to, hqueue_eq, outgoing_txs,
                      trace_txs, step_txs, eval_tx, hfrom_false_caddr] using hP
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state resp_acts hamount hbalance hcontract hstate hact hreceive hnew henv =>
              have hheight : to_.chain_height = mid.chain_height := by
                simpa [set_contract_state, transfer_balance] using
                  chain_height_env_equiv henv
              have hslot : to_.current_slot = mid.current_slot := by
                simpa [set_contract_state, transfer_balance] using
                  current_slot_env_equiv henv
              have hfin : to_.finalized_height = mid.finalized_height := by
                simpa [set_contract_state, transfer_balance] using
                  finalized_height_env_equiv henv
              have hpre_deployed :
                  mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
                have hdeployed' :
                    (set_contract_state to_addr new_state
                        (transfer_balance from_addr to_addr amount mid.toEnvironment)).env_contracts
                        caddr =
                      some (contract_to_weak_contract contract) := by
                  rw [← henv.contracts_eq caddr]
                  exact hdeployed
                simpa [set_contract_state, transfer_balance] using hdeployed'
              obtain ⟨dep, cstate, inc_calls, hdep, hstate_old, hinc, hP⟩ :=
                ih hpre_deployed
              by_cases hto_eq : caddr = to_addr
              · subst to_addr
                have hwc : wc = contract_to_weak_contract contract := by
                  exact Option.some.inj (hcontract.symm.trans hpre_deployed)
                subst wc
                obtain ⟨prev_state_strong, msg_strong, new_state_strong,
                  hprev_deser, hmsg_rel, hnew_state_ser, hreceive_strong⟩ :=
                  wc_receive_strong (contract := contract) hreceive
                have hprev_contract_state :
                    @contract_state Base State _ mid.toEnvironment caddr =
                      some prev_state_strong := by
                  unfold contract_state
                  rw [hstate]
                  exact hprev_deser
                have hcstate_eq : cstate = prev_state_strong :=
                  Option.some.inj (hstate_old.symm.trans hprev_contract_state)
                subst prev_state_strong
                let chain : Chain :=
                  (transfer_balance from_addr caddr amount mid.toEnvironment).toChain
                let ctx : @ContractCallContext Base :=
                  { ctx_origin := origin, ctx_from := from_addr,
                    ctx_contract_address := caddr,
                    ctx_contract_balance :=
                      (transfer_balance from_addr caddr amount
                        mid.toEnvironment).env_account_balances caddr,
                    ctx_amount := amount }
                let callInfo : @ContractCallInfo Base Msg :=
                  { call_origin := origin, call_from := from_addr,
                    call_amount := amount, call_msg := msg_strong }
                have hctx_balance :
                    to_.env_account_balances caddr =
                      (transfer_balance from_addr caddr amount
                        mid.toEnvironment).env_account_balances caddr := by
                  rw [henv.account_balances_eq caddr]
                  simp [set_contract_state]
                have hreceive_ctx :
                    contract.receive chain ctx cstate msg_strong =
                      .Ok (new_state_strong, resp_acts) := by
                  simpa [chain, ctx, hctx_balance] using hreceive_strong
                refine ⟨dep, new_state_strong, callInfo :: inc_calls, ?_, ?_, ?_, ?_⟩
                · simpa [deployment_info, step_deployment_info, eval_tx,
                    Address.address_eq_refl caddr] using hdep
                · rw [contract_state_env_equiv henv caddr]
                  simp [contract_state, set_contract_state, set_chain_contract_state,
                    Address.address_eq_refl caddr, ← hnew_state_ser,
                    Serializable.deserialize_serialize]
                · cases msg_strong with
                  | none =>
                      have hmsg_none : msg = none := by
                        simpa using hmsg_rel
                      simp [incoming_calls, step_incoming_calls, eval_tx,
                        Address.address_eq_refl caddr, hmsg_none, hinc, callInfo]
                  | some msg_typed =>
                      have hbind : (msg >>= deserialize) = some msg_typed := by
                        simpa using hmsg_rel
                      cases msg with
                      | none =>
                          simp at hbind
                      | some msg_ser =>
                          cases hdes : (deserialize msg_ser : Option Msg) with
                          | none =>
                              simp [hdes] at hbind
                          | some msg_typed' =>
                              simp [hdes] at hbind
                              cases hbind
                              simp [incoming_calls, step_incoming_calls, eval_tx,
                                Address.address_eq_refl caddr, hinc, hdes, callInfo]
                · by_cases hfrom_eq : from_addr = caddr
                  · subst from_addr
                    let head : @ActionBody Base := call_action_body caddr amount msg
                    let prev_queue : List (@ActionBody Base) :=
                      (acts.filter (fun a => Base.address_eqb a.act_from caddr)).map
                        (fun a => a.act_body)
                    have hhead_match :
                        (match head with
                         | .act_transfer to_ amount' =>
                             to_ = ctx.ctx_contract_address ∧
                             amount' = ctx.ctx_amount ∧ msg_strong = none
                         | .act_call to_ amount' msg_ser =>
                             to_ = ctx.ctx_contract_address ∧
                             amount' = ctx.ctx_amount ∧
                             msg_strong ≠ none ∧ deserialize msg_ser = msg_strong
                         | _ => False) := by
                      cases hmsg : msg with
                      | none =>
                          cases msg_strong with
                          | none =>
                              simp only [head, call_action_body, hmsg]
                              simp [ctx]
                          | some msg_typed =>
                              simp [hmsg] at hmsg_rel
                      | some msg_ser =>
                          cases msg_strong with
                          | none =>
                              simp [hmsg] at hmsg_rel
                          | some msg_typed =>
                              have hdes : deserialize msg_ser = some msg_typed := by
                                simpa [hmsg] using hmsg_rel
                              simp only [head, call_action_body, hmsg]
                              change caddr = ctx.ctx_contract_address ∧
                                amount = ctx.ctx_amount ∧
                                (some msg_typed ≠ (none : Option Msg)) ∧
                                deserialize msg_ser = some msg_typed
                              simp [ctx, hdes]
                    have hqueue_mid :
                        outgoing_acts mid caddr = head :: prev_queue := by
                      simp [outgoing_acts, hq_prev, hact, head, prev_queue,
                        call_action_body, Address.address_eq_refl caddr]
                      rfl
                    have hqueue_to :
                        outgoing_acts to_ caddr = resp_acts ++ prev_queue := by
                      simp [outgoing_acts, hq_next, hnew, prev_queue,
                        mapped_actions_outgoing_self]
                    have hcall_balance_old :
                        mid.env_account_balances caddr =
                          (transfer_balance caddr caddr amount
                            mid.toEnvironment).env_account_balances caddr := by
                      simp [transfer_balance, add_balance, Address.address_eq_refl caddr]
                    have hcall_facts :
                        CallFacts chain ctx cstate (head :: prev_queue) (some inc_calls) := by
                      have hfacts_call := hfacts cstate hpre_deployed hstate_old
                      simpa [stepFactsPred, chain, ctx, hinc, hqueue_mid] using hfacts_call
                    have hP_old :
                        P chain.chain_height chain.current_slot chain.finalized_height
                          caddr dep cstate ctx.ctx_contract_balance
                          (head :: prev_queue) inc_calls (outgoing_txs tail caddr) := by
                      simpa [chain, ctx, hcall_balance_old, hqueue_mid] using hP
                    have hP_new :=
                      hCases.recursive_call_case chain ctx dep cstate msg_strong
                        head prev_queue inc_calls (outgoing_txs tail caddr)
                        new_state_strong resp_acts rfl hcall_facts hP_old
                        hhead_match hreceive_ctx TagRecursiveCall.tag_recursive_call
                    simpa [chain, ctx, hheight, hslot, hfin, hctx_balance, hqueue_to,
                      outgoing_txs, trace_txs, step_txs, eval_tx, transfer_balance,
                      Address.address_eq_refl caddr, callInfo, head,
                      call_action_body, call_action_body_tx_msg,
                      call_action_match_tx_msg] using hP_new
                  · let prev_queue : List (@ActionBody Base) := outgoing_acts mid caddr
                    have hfrom_false_caddr :
                        Base.address_eqb from_addr caddr = false :=
                      Address.address_eq_ne from_addr caddr hfrom_eq
                    have hfrom_false :
                        Base.address_eqb caddr from_addr = false :=
                      Address.address_eq_ne caddr from_addr (Ne.symm hfrom_eq)
                    have hqueue_to :
                        outgoing_acts to_ caddr = resp_acts ++ prev_queue := by
                      simp [outgoing_acts, hq_prev, hq_next, hnew, hact, prev_queue,
                        hfrom_false_caddr, mapped_actions_outgoing_self]
                    have hcall_balance_old :
                        mid.env_account_balances caddr =
                          (transfer_balance from_addr caddr amount
                            mid.toEnvironment).env_account_balances caddr - amount := by
                      simp [transfer_balance, add_balance, hfrom_false,
                        Address.address_eq_refl caddr]
                    have hcall_facts :
                        CallFacts chain ctx cstate prev_queue (some inc_calls) := by
                      have hfacts_call := hfacts cstate hpre_deployed hstate_old
                      simpa [stepFactsPred, chain, ctx, hinc, prev_queue] using hfacts_call
                    have hP_old :
                        P chain.chain_height chain.current_slot chain.finalized_height
                          caddr dep cstate (ctx.ctx_contract_balance - ctx.ctx_amount)
                          prev_queue inc_calls (outgoing_txs tail caddr) := by
                      simpa [chain, ctx, hcall_balance_old, prev_queue] using hP
                    have hP_new :=
                      hCases.nonrecursive_call_case chain ctx dep cstate msg_strong
                        prev_queue inc_calls (outgoing_txs tail caddr)
                        new_state_strong resp_acts hfrom_eq hcall_facts hP_old
                        hreceive_ctx TagNonrecursiveCall.tag_nonrecursive_call
                    simpa [chain, ctx, hheight, hslot, hfin, hctx_balance, hqueue_to,
                      outgoing_txs, trace_txs, step_txs, eval_tx, hfrom_false_caddr,
                      callInfo] using hP_new
              · have hto_false_caddr :
                    Base.address_eqb to_addr caddr = false :=
                  Address.address_eq_ne to_addr caddr (Ne.symm hto_eq)
                have hto_false :
                    Base.address_eqb caddr to_addr = false :=
                  Address.address_eq_ne caddr to_addr hto_eq
                refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
                · simpa [deployment_info, step_deployment_info, eval_tx,
                    hto_false_caddr] using hdep
                · rw [contract_state_env_equiv henv caddr]
                  simpa [contract_state, set_contract_state, set_chain_contract_state,
                    hto_false] using hstate_old
                · simp [incoming_calls, step_incoming_calls, eval_tx,
                    hto_false_caddr, hinc]
                · by_cases hfrom_eq : caddr = from_addr
                  · subst from_addr
                    have hbalance_to :
                        to_.env_account_balances caddr =
                          mid.env_account_balances caddr - amount := by
                      rw [henv.account_balances_eq caddr]
                      simp [set_contract_state, transfer_balance, add_balance,
                        Address.address_eq_refl caddr, hto_false]
                      ring
                    cases msg with
                    | none =>
                        have hqueue_old :
                            outgoing_acts mid caddr =
                              ActionBody.act_transfer to_addr amount :: outgoing_acts to_ caddr := by
                          simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                            Address.address_eq_refl caddr, hto_false_caddr]
                        have hP_old :
                            P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                              (mid.env_account_balances caddr)
                              (ActionBody.act_transfer to_addr amount :: outgoing_acts to_ caddr)
                              inc_calls (outgoing_txs tail caddr) := by
                          simpa [hqueue_old] using hP
                        let tx : @Tx Base :=
                          { tx_origin := origin, tx_from := caddr, tx_to := to_addr,
                            tx_amount := amount, tx_body := .tx_call none }
                        have hP_new :=
                          hCases.outgoing_act_case mid.chain_height mid.current_slot
                            mid.finalized_height caddr dep cstate
                            (mid.env_account_balances caddr)
                            (ActionBody.act_transfer to_addr amount) (outgoing_acts to_ caddr)
                            inc_calls (outgoing_txs tail caddr) tx
                            hP_old rfl rfl
                            (And.intro rfl (And.intro rfl (Or.inr rfl)))
                            TagOutgoingAct.tag_outgoing_act
                        simpa [hheight, hslot, hfin, hbalance_to, outgoing_txs,
                          trace_txs, step_txs, eval_tx, tx,
                          Address.address_eq_refl caddr] using hP_new
                    | some msg_ser =>
                        have hqueue_old :
                            outgoing_acts mid caddr =
                              ActionBody.act_call to_addr amount msg_ser ::
                                outgoing_acts to_ caddr := by
                          simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                            Address.address_eq_refl caddr, hto_false_caddr]
                        have hP_old :
                            P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                              (mid.env_account_balances caddr)
                              (ActionBody.act_call to_addr amount msg_ser :: outgoing_acts to_ caddr)
                              inc_calls (outgoing_txs tail caddr) := by
                          simpa [hqueue_old] using hP
                        let tx : @Tx Base :=
                          { tx_origin := origin, tx_from := caddr, tx_to := to_addr,
                            tx_amount := amount, tx_body := .tx_call (some msg_ser) }
                        have hP_new :=
                          hCases.outgoing_act_case mid.chain_height mid.current_slot
                            mid.finalized_height caddr dep cstate
                            (mid.env_account_balances caddr)
                            (ActionBody.act_call to_addr amount msg_ser) (outgoing_acts to_ caddr)
                            inc_calls (outgoing_txs tail caddr) tx
                            hP_old rfl rfl (And.intro rfl (And.intro rfl rfl))
                            TagOutgoingAct.tag_outgoing_act
                        simpa [hheight, hslot, hfin, hbalance_to, outgoing_txs,
                          trace_txs, step_txs, eval_tx, tx,
                          Address.address_eq_refl caddr] using hP_new
                  · have hfrom_false_caddr :
                        Base.address_eqb from_addr caddr = false :=
                      Address.address_eq_ne from_addr caddr (Ne.symm hfrom_eq)
                    have hfrom_false :
                        Base.address_eqb caddr from_addr = false :=
                      Address.address_eq_ne caddr from_addr hfrom_eq
                    have hqueue_eq :
                        outgoing_acts mid caddr = outgoing_acts to_ caddr := by
                      simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                        hfrom_false_caddr, hto_false_caddr]
                    have hbalance_to :
                        to_.env_account_balances caddr = mid.env_account_balances caddr := by
                      rw [henv.account_balances_eq caddr]
                      simp [set_contract_state, transfer_balance, add_balance,
                        hfrom_false, hto_false]
                    simpa [hheight, hslot, hfin, hbalance_to, hqueue_eq, outgoing_txs,
                      trace_txs, step_txs, eval_tx, hfrom_false_caddr] using hP
      | step_action_invalid act acts henv hq_prev hq_next hfrom_account hinvalid =>
          have hpre_deployed :
              mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
            rw [← henv.contracts_eq caddr]
            exact hdeployed
          obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ := ih hpre_deployed
          refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
          · simpa [deployment_info, step_deployment_info] using hdep
          · rw [contract_state_env_equiv henv caddr]
            exact hstate
          · simp [incoming_calls, step_incoming_calls, hinc]
          · have haddr_contract : Base.address_is_contract caddr = true :=
              contract_addr_format caddr (contract_to_weak_contract contract)
                (trace_reachable (ChainedList.snoc tail
                  (ChainStep.step_action_invalid act acts henv hq_prev hq_next
                    hfrom_account hinvalid))) hdeployed
            have hact_not_from_contract :
                Base.address_eqb act.act_from caddr = false := by
              unfold act_is_from_account at hfrom_account
              apply Address.address_eq_ne
              intro heq
              rw [heq, haddr_contract] at hfrom_account
              cases hfrom_account
            have hqueue :
                outgoing_acts mid caddr = outgoing_acts to_ caddr := by
              simp [outgoing_acts, hq_prev, hq_next, hact_not_from_contract]
            have hheight : to_.chain_height = mid.chain_height :=
              chain_height_env_equiv henv
            have hslot : to_.current_slot = mid.current_slot :=
              current_slot_env_equiv henv
            have hfin : to_.finalized_height = mid.finalized_height :=
              finalized_height_env_equiv henv
            have hbalance :
                to_.env_account_balances caddr = mid.env_account_balances caddr :=
              henv.account_balances_eq caddr
            simpa [hheight, hslot, hfin, hbalance, hqueue, outgoing_txs, trace_txs,
              step_txs] using hP
      | step_permute henv hperm =>
          have hpre_deployed :
              mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
            rw [← henv.contracts_eq caddr]
            exact hdeployed
          obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ := ih hpre_deployed
          refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
          · simpa [deployment_info, step_deployment_info] using hdep
          · rw [contract_state_env_equiv henv caddr]
            exact hstate
          · simp [incoming_calls, step_incoming_calls, hinc]
          · have hperm_out :
                List.Perm (outgoing_acts mid caddr) (outgoing_acts to_ caddr) := by
              unfold outgoing_acts
              exact (hperm.filter (fun act => Base.address_eqb act.act_from caddr)).map
                (fun act => act.act_body)
            have hheight : to_.chain_height = mid.chain_height :=
              chain_height_env_equiv henv
            have hslot : to_.current_slot = mid.current_slot :=
              current_slot_env_equiv henv
            have hfin : to_.finalized_height = mid.finalized_height :=
              finalized_height_env_equiv henv
            have hbalance :
                to_.env_account_balances caddr = mid.env_account_balances caddr :=
              henv.account_balances_eq caddr
            have hP_new :=
              hCases.permute_case mid.chain_height mid.current_slot mid.finalized_height
                caddr dep cstate (mid.env_account_balances caddr)
                (outgoing_acts mid caddr) inc_calls (outgoing_txs tail caddr)
                (outgoing_acts to_ caddr) hP hperm_out
                TagPermuteQueue.tag_permute_queue
            simpa [hheight, hslot, hfin, hbalance, outgoing_txs, trace_txs, step_txs]
              using hP_new

/-- If a property `P` holds for every action produced by the receive
    function, then it holds for every action in the outgoing queue of any
    reachable state where the contract is deployed. -/
theorem lift_outgoing_acts_prop
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {Q : @ActionBody Base → Prop}
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base) (caddr : Base.Address)
    (_hr : reachable bstate)
    (Hc : ∀ (chain : Chain) (ctx : @ContractCallContext Base) (cstate : State)
            (msg : Option Msg) (new_cstate : State) (acts : List (@ActionBody Base)),
            contract.receive chain ctx cstate msg = .Ok (new_cstate, acts) →
            acts.Forall Q)
    (hd : bstate.env_contracts caddr = some (contract_to_weak_contract contract)) :
    (outgoing_acts bstate caddr).Forall Q := by
  obtain ⟨trace⟩ := _hr
  -- P = "the outgoing-actions queue satisfies Forall Q"
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
          State → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ _ _ _ out_queue _ _ => out_queue.Forall Q
  have cases : ContractInductionCases contract
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True) P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      -- The facts predicate is trivially True for all branches instantiated here.
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
        cases eval with
        | eval_transfer => trivial
        | eval_deploy => trivial
        | eval_call =>
          intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · -- add_block_case: queue was [], stays []
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; simp [P]
    · -- init_case: queue is []
      intro _ _ _ _ _ _ _; simp [P]
    · -- outgoing_act_case: pop head from queue preserves Forall
      intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
      simp only [P, List.forall_cons] at ih
      exact ih.2
    · -- nonrecursive_call_case: new queue = new_acts ++ prev_queue
      intro _ _ _ _ _ _ _ _ _ _ _ _ ih hr _
      simp only [P] at ih ⊢
      exact (ConCert.Utils.Extras.Forall_app Q _ _).mp ⟨Hc _ _ _ _ _ _ hr, ih⟩
    · -- recursive_call_case: new queue = new_acts ++ prev_queue (head popped)
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _ hr _
      simp only [P, List.forall_cons] at ih
      simp only [P]
      exact (ConCert.Utils.Extras.Forall_app Q _ _).mp ⟨Hc _ _ _ _ _ _ hr, ih.2⟩
    · -- permute_case: Forall preserved by permutation
      intro _ _ _ _ _ _ _ _ _ _ _ ih hperm _
      simp only [P] at ih ⊢
      exact ConCert.Utils.Extras.forall_respects_permutation _ _ Q hperm ih
  obtain ⟨_, _, _, _, _, _, hP⟩ :=
    contract_induction contract _ _ _ P cases bstate caddr trace hd
  exact hP

/-- If the receive function always returns an empty action list, the
    outgoing queue is always empty. -/
theorem lift_outgoing_acts_nil
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (Hc : ∀ (chain : Chain) (ctx : @ContractCallContext Base) (cstate : State)
            (msg : Option Msg) (new_cstate : State) (acts : List (@ActionBody Base)),
            contract.receive chain ctx cstate msg = .Ok (new_cstate, acts) →
            acts = [])
    (hd : bstate.env_contracts caddr = some (contract_to_weak_contract contract)) :
    outgoing_acts bstate caddr = [] := by
  have hall :
      (outgoing_acts bstate caddr).Forall (fun _ : @ActionBody Base => False) :=
    lift_outgoing_acts_prop contract bstate caddr hr
      (by
        intro _ _ _ _ _ acts hrec
        rw [Hc _ _ _ _ _ _ hrec]
        trivial)
      hd
  -- Forall False on a list ⇒ the list is empty
  cases h : outgoing_acts bstate caddr with
  | nil => rfl
  | cons hd tl =>
    rw [h] at hall
    simp [List.forall_cons] at hall

/-- If a property `P` is preserved by both `init` (initial result satisfies
    `P`) and `receive` (`P` on input cstate ⇒ `P` on output cstate), then
    `P` holds for the contract's state at every reachable point. -/
theorem lift_contract_state_prop
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {Q : State → Prop}
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base) (caddr : Base.Address)
    (Hinit : ∀ (chain : Chain) (ctx : @ContractCallContext Base) (setup : Setup)
               (result : State),
               contract.init chain ctx setup = .Ok result → Q result)
    (Hreceive : ∀ (chain : Chain) (ctx : @ContractCallContext Base) (cstate : State)
                  (msg : Option Msg) (new_cstate : State) (acts : List (@ActionBody Base)),
                  Q cstate →
                  contract.receive chain ctx cstate msg = .Ok (new_cstate, acts) →
                  Q new_cstate)
    (hr : reachable bstate)
    (hd : bstate.env_contracts caddr = some (contract_to_weak_contract contract)) :
    ∃ cstate, @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
              Q cstate := by
  obtain ⟨trace⟩ := hr
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
          State → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ _ cstate _ _ _ _ => Q cstate
  have cases : ContractInductionCases contract
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True) P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
        cases eval with
        | eval_transfer => trivial
        | eval_deploy => trivial
        | eval_call => intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _; exact ih
    · intro _ _ _ _ _ hinit _; exact Hinit _ _ _ _ hinit
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _; exact ih
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih hrec _
      exact Hreceive _ _ _ _ _ _ ih hrec
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _ hrec _
      exact Hreceive _ _ _ _ _ _ ih hrec
    · intro _ _ _ _ _ _ _ _ _ _ _ ih _ _; exact ih
  obtain ⟨_, cstate, _, _, hcs, _, hP⟩ :=
    contract_induction contract _ _ _ P cases bstate caddr trace hd
  exact ⟨cstate, hcs, hP⟩

/-- Same as `lift_contract_state_prop` but carrying the deployment info
    alongside the state. -/
theorem lift_dep_info_contract_state_prop
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {Q : @DeploymentInfo Base Setup → State → Prop}
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate)
    (Hinit : ∀ (chain : Chain) (ctx : @ContractCallContext Base) (setup : Setup)
               (result : State),
               contract.init chain ctx setup = .Ok result →
               Q { deployment_origin := ctx.ctx_origin,
                   deployment_from   := ctx.ctx_from,
                   deployment_amount := ctx.ctx_amount,
                   deployment_setup  := setup } result)
    (Hreceive : ∀ (chain : Chain) (ctx : @ContractCallContext Base) (cstate : State)
                  (msg : Option Msg) (new_cstate : State) (acts : List (@ActionBody Base))
                  (dep : @DeploymentInfo Base Setup),
                  Q dep cstate →
                  contract.receive chain ctx cstate msg = .Ok (new_cstate, acts) →
                  Q dep new_cstate)
    (hd : bstate.env_contracts caddr = some (contract_to_weak_contract contract)) :
    ∃ dep cstate,
      deployment_info Setup trace caddr = some dep ∧
      @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
      Q dep cstate := by
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
          State → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ dep cstate _ _ _ _ => Q dep cstate
  have cases : ContractInductionCases contract
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True) P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
        cases eval with
        | eval_transfer => trivial
        | eval_deploy => trivial
        | eval_call => intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _; exact ih
    · intro _ _ _ _ _ hinit _; exact Hinit _ _ _ _ hinit
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _; exact ih
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih hrec _
      exact Hreceive _ _ _ _ _ _ _ ih hrec
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _ hrec _
      exact Hreceive _ _ _ _ _ _ _ ih hrec
    · intro _ _ _ _ _ _ _ _ _ _ _ ih _ _; exact ih
  obtain ⟨dep, cstate, _, hdep, hcs, _, hP⟩ :=
    contract_induction contract _ _ _ P cases bstate caddr trace hd
  exact ⟨dep, cstate, hdep, hcs, hP⟩

end ConCert.Execution.BlockchainInduction
