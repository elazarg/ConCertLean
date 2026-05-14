/- Port of execution/test/TraceGens.v.

   The original is a large collection of QuickChick generators and checkers
   over `ChainBuilder` / `ChainTrace`. This port exposes a minimal
   compatibility layer with the shrinkers and a few helpers; generator
   combinators can be added when specific tests require them. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Serializable
import ConCert.Execution.ChainedList
import ConCert.Execution.Test.TestUtils

namespace ConCert.Execution.Test.TraceGens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.ChainedList

variable [Base : ChainBase] [TA : @TestAddresses Base]

def BlockReward : Amount := 50
def BlockCreator : Base.Address := @creator Base TA
def MaxGenAttempts : Nat := 2

def chainstep_states {prev_bstate next_bstate : @ChainState Base}
    (_step : ChainStep prev_bstate next_bstate) :
    @ChainState Base × @ChainState Base :=
  (prev_bstate, next_bstate)

def trace_blocks : ∀ {frm to_ : @ChainState Base},
    ChainTrace frm to_ → List (@BlockHeader Base × List (@Action Base))
  | _, _, .clnil => []
  | _, _, .snoc trace' step =>
      let rest := trace_blocks trace'
      match step with
      | .step_block header _ _ _ _ _ =>
          rest ++ [(header, (chainstep_states step).2.chain_state_queue)]
      | _ => rest

def trace_states : ∀ {frm to_ : @ChainState Base},
    ChainTrace frm to_ → List (@ChainState Base)
  | _, _, .clnil => []
  | _, _, .snoc trace' step =>
      trace_states trace' ++ [(chainstep_states step).2]

def trace_states_step_block : ∀ {frm to_ : @ChainState Base},
    ChainTrace frm to_ → List (@ChainState Base)
  | _, _, .clnil => []
  | _, _, .snoc trace' step =>
      let rest := trace_states_step_block trace'
      match step with
      | .step_block _ _ _ _ _ _ => rest ++ [(chainstep_states step).2]
      | _ => rest

def trace_states_step_action : ∀ {frm to_ : @ChainState Base},
    ChainTrace frm to_ →
      List (@Action Base × List (@Action Base) × @ChainState Base × @ChainState Base)
  | _, _, .clnil => []
  | _, _, .snoc trace' step =>
      let rest := trace_states_step_action trace'
      match step with
      | .step_action act _ new_acts _ _ _ =>
          let states := chainstep_states step
          rest ++ [(act, new_acts, states.1, states.2)]
      | _ => rest

def shrinkListAux_ {A : Type} : List A → List (List A)
  | [] => []
  | x :: xs => xs :: (shrinkListAux_ xs).map (fun xs' => x :: xs')

def shrinkChainBuilderAux {A : Type} (BH : Type) :
    List (BH × List A) → List (List (BH × List A))
  | [] => []
  | block :: blocks' =>
    let acts_shrunk := shrinkListAux_ block.2
    let block_shrunk := acts_shrunk.map (fun acts => (block.1, acts))
    (block_shrunk.map (fun b' => b' :: blocks')) ++
      (shrinkChainBuilderAux BH blocks').map (fun xs => block :: xs)

def ChainTrace_ChainTraceProp {frm to_ : @ChainState Base}
    (trace : ChainTrace frm to_) (pf : @ChainState Base → Bool) : Checker :=
  let states := trace_states_step_block trace
  discard_empty states (fun ss => conjoin_map (fun cs => checker (pf cs)) ss)

def existsb_chaintrace {frm to_ : @ChainState Base}
    (pf : @ChainState Base → Bool) (trace : ChainTrace frm to_) : Bool :=
  (trace_states trace).any pf

end ConCert.Execution.Test.TraceGens
