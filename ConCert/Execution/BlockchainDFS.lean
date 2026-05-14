/- Port of execution/theories/BlockchainDFS.v.

   Note: the Coq file is named `BlockchainDFS.v` but its `Section BreadthFirst`
   defines BFS-related predicates (`BFSPermutations`, `BFSChainTrace`).
   DFS-related predicates live in `BlockchainBFS.v` (similar misnomer).
   This module mirrors the Coq layout. -/

import ConCert.Execution.BlockchainBase
import ConCert.Execution.ChainedList

namespace ConCert.Execution.BlockchainDFS

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ChainedList

variable [Base : ChainBase]

-- A trace is "BFS-shaped": permutation steps may appear only directly
-- after a `step_action`, and they must produce a queue equal to the
-- action's new+remaining acts concatenation.

/-- Per-step BFS constraint at the position after trace `xs`. -/
def step_bfs_ok {frm mid to_ : @ChainState Base}
    (xs : ChainTrace frm mid) (s : ChainStep mid to_) : Prop :=
  match xs, s with
  | .clnil, .step_permute _ _ => False
  | .clnil, _ => True
  | .snoc _ (.step_action _ acts new_acts _ _ _), .step_permute _ _ =>
      to_.chain_state_queue = (acts ++ new_acts)
  | _, _ => True

def BFSPermutations : ∀ {frm to_ : @ChainState Base}, ChainTrace frm to_ → Prop
  | _, _, .clnil      => True
  | _, _, .snoc xs s  => step_bfs_ok xs s ∧ BFSPermutations xs

def BFSChainTrace (frm to_ : @ChainState Base) : Type :=
  { x : ChainTrace frm to_ // BFSPermutations x }

def BFSChainTrace_to_ChainTrace {frm to_ : @ChainState Base}
    (trace : BFSChainTrace frm to_) : ChainTrace frm to_ :=
  trace.val

end ConCert.Execution.BlockchainDFS
