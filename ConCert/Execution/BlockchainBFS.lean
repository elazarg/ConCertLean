/- Port of execution/theories/BlockchainBFS.v.

   Note: the Coq file is named `BlockchainBFS.v` but its `Section DepthFirst`
   defines DFS-related predicates (`NoPermutations`, `NoPermutations'`,
   `NoPermutations''`, `DFSChainTrace`). BFS-related predicates live in the
   sibling `BlockchainDFS.v` (similar misnomer). We mirror the Coq layout. -/

import ConCert.Execution.BlockchainBase
import ConCert.Execution.BlockchainTheories
import ConCert.Execution.BlockchainInduction
import ConCert.Execution.ChainedList
import ConCert.Execution.ResultMonad
import ConCert.Execution.SerializableBase

namespace ConCert.Execution.BlockchainBFS

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.SerializableBase
open ConCert.Execution.ChainedList

variable [Base : ChainBase]

/-- A trace contains no permutation step. Defined as a `Fixpoint`-style
    structural recursion: every `step_permute` makes the property `False`. -/
def NoPermutations : ∀ {frm to_ : @ChainState Base}, ChainTrace frm to_ → Prop
  | _, _, .clnil      => True
  | _, _, .snoc xs s  =>
    match s with
    | .step_permute _ _ => False
    | _ => NoPermutations xs

/-- Identical to `NoPermutations`; the Coq source ships both forms. -/
abbrev NoPermutations' := @NoPermutations

inductive StepNotPermute :
    ∀ {frm to_ : @ChainState Base}, ChainStep frm to_ → Prop
  | snp_block : ∀ {frm to_ : @ChainState Base}
                  (h : @BlockHeader Base)
                  (h1 : frm.chain_state_queue = [])
                  (h2 : IsValidNextBlock h (env_chain frm.toEnvironment))
                  (h3 : to_.chain_state_queue.Forall act_is_from_account)
                  (h4 : to_.chain_state_queue.Forall act_origin_is_eq_from)
                  (h5 : EnvironmentEquiv to_.toEnvironment
                         (add_new_block_to_env h frm.toEnvironment)),
                  StepNotPermute (ChainStep.step_block h h1 h2 h3 h4 h5)
  | snp_action : ∀ {frm to_ : @ChainState Base}
                   (act : @Action Base) (acts new_acts : List (@Action Base))
                   (h1 : frm.chain_state_queue = act :: acts)
                   (h2 : ActionEvaluation frm.toEnvironment act to_.toEnvironment new_acts)
                   (h3 : to_.chain_state_queue = new_acts ++ acts),
                   StepNotPermute (ChainStep.step_action act acts new_acts h1 h2 h3)
  -- Deviation: upstream's `snp_action_invalid` constructor targets
  -- `step_action` (apparent copy-paste); we correct it to
  -- `step_action_invalid`.
  | snp_action_invalid : ∀ {frm to_ : @ChainState Base}
                           (act : @Action Base) (acts : List (@Action Base))
                           (h1 : EnvironmentEquiv to_.toEnvironment frm.toEnvironment)
                           (h2 : frm.chain_state_queue = act :: acts)
                           (h3 : to_.chain_state_queue = acts)
                           (h4 : act_is_from_account act)
                           (h5 : ∀ bstate new_acts,
                                  ActionEvaluation frm.toEnvironment act bstate new_acts → False),
                           StepNotPermute (ChainStep.step_action_invalid act acts h1 h2 h3 h4 h5)

inductive NoPermutations'' :
    ∀ {frm to_ : @ChainState Base}, ChainTrace frm to_ → Prop
  | trace_nil  : ∀ {x : @ChainState Base},
                   NoPermutations'' (ChainedList.clnil (p := x))
  | trace_step : ∀ {frm mid to_ : @ChainState Base}
                   (trace : ChainTrace frm mid) (step : ChainStep mid to_),
                   NoPermutations'' trace →
                   StepNotPermute step →
                   NoPermutations'' (ChainedList.snoc trace step)

def DFSChainTrace (frm to_ : @ChainState Base) : Type :=
  { trace : ChainTrace frm to_ // NoPermutations'' trace }

def DFSChainTrace_to_ChainTrace {frm to_ : @ChainState Base}
    (trace : DFSChainTrace frm to_) : ChainTrace frm to_ :=
  trace.val

/-- Coq direction: if a property `P` holds over *all* traces, then it
    also holds when restricted to DFS (permutation-free) traces. This is
    a weakening of an all-traces theorem to DFS-traces. -/
axiom DFS_weaken :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (P :
       Nat → Nat → Nat →
       Base.Address →
       @DeploymentInfo Base Setup →
       State →
       Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop),
    (∀ (bstate : @ChainState Base) (caddr : Base.Address)
       (trace : ChainTrace empty_state bstate),
       bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
       ∃ dep cstate inc_calls,
         deployment_info Setup trace caddr = some dep ∧
         @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
         incoming_calls Msg trace caddr = some inc_calls ∧
         P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
           dep cstate (bstate.env_account_balances caddr)
           (outgoing_acts bstate caddr) inc_calls (outgoing_txs trace caddr)) →
    ∀ (bstate : @ChainState Base) (caddr : Base.Address)
      (trace : ChainTrace empty_state bstate),
      NoPermutations'' trace →
      bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
      ∃ dep cstate inc_calls,
        deployment_info Setup trace caddr = some dep ∧
        @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
        incoming_calls Msg trace caddr = some inc_calls ∧
        P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
          dep cstate (bstate.env_account_balances caddr)
          (outgoing_acts bstate caddr) inc_calls (outgoing_txs trace caddr)

/-- DFS-flavored contract induction. Restricted to traces without
    permutation steps; consequently the queue-permutation case is
    *not* required. Takes `DFSContractInductionCases`, which omits
    `permute_case`. -/
axiom dfs_contract_induction :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (AddBlockFacts : Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    (P :
       Nat → Nat → Nat →
       Base.Address →
       @DeploymentInfo Base Setup →
       State →
       Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop),
    DFSContractInductionCases contract AddBlockFacts DeployFacts CallFacts P →
    ∀ (bstate : @ChainState Base) (caddr : Base.Address)
      (trace : ChainTrace empty_state bstate),
      NoPermutations'' trace →
      bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
      ∃ dep cstate inc_calls,
        deployment_info Setup trace caddr = some dep ∧
        @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
        incoming_calls Msg trace caddr = some inc_calls ∧
        P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
          dep cstate (bstate.env_account_balances caddr)
          (outgoing_acts bstate caddr) inc_calls (outgoing_txs trace caddr)

end ConCert.Execution.BlockchainBFS
