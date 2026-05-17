/- Port of execution/test/TraceGens.v.

   The original is a large collection of QuickChick generators and checkers
   over `ChainBuilder` / `ChainTrace`. This port exposes the shrinkers and
   helper generators needed by the ported tests; more generator combinators can
   be added when specific tests require them. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Serializable
import ConCert.Execution.ChainedList
import ConCert.Execution.Test.TestUtils

namespace ConCert.Execution.Test.TraceGens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.LocalBlockchain
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

omit Base TA

/-! ### Executable local-chain generators

These are intentionally concrete rather than typeclass-generic. ConCert's
abstract `ChainBase` does not tell us how to enumerate fresh addresses or how to
construct non-contract addresses. The local-chain test backend does, so it is
the right level for executable trace/property generation. -/

abbrev TestBase := LocalChainBase AddrSize
abbrev TestAddress := ConCert.Execution.BoundedN AddrSize
abbrev TestAction := Action (Base := TestBase)
abbrev TestBlockHeader := BlockHeader (Base := TestBase)
abbrev TestLocalChain := LocalChain AddrSize
abbrev TestLocalChainBuilder := LocalChainBuilder AddrSize
abbrev TestAddBlockError := ConCert.Execution.BlockchainBuilder.AddBlockError (Base := TestBase)

def genFailure {A : Type} (msg : String) : G A :=
  throw <| Plausible.GenError.genError msg

def boundedOfNatOrFail {bound : Nat} (n : Nat) : G (ConCert.Execution.BoundedN bound) :=
  match ConCert.Execution.BoundedN.of_N (bound := bound) n with
  | some addr => return addr
  | none => genFailure s!"address {n} is outside bound {bound}"

def gLocalAddress (bound : Nat) : G (ConCert.Execution.BoundedN bound) := do
  match ← gBoundedNOpt bound with
  | some addr => return addr
  | none => genFailure s!"cannot generate an address for empty bound {bound}"

def gLocalAccountAddress : G TestAddress := do
  let n ← chooseNatBetween 0 (TestUtils.ContractAddrBase - 1) (by decide)
  boundedOfNatOrFail (bound := AddrSize) n

def gLocalContractAddress : G TestAddress := do
  let n ← chooseNatBetween TestUtils.ContractAddrBase (AddrSize - 1) (by decide)
  boundedOfNatOrFail (bound := AddrSize) n

def fixedLocalAddress (n : Nat) (h : n < AddrSize) : TestAddress :=
  ⟨n, h⟩

def fixedUser10 : TestAddress := fixedLocalAddress 10 (by decide)
def fixedUser11 : TestAddress := fixedLocalAddress 11 (by decide)
def fixedContractBase : TestAddress := fixedLocalAddress TestUtils.ContractAddrBase (by decide)

def gPositiveRewardNat : G Nat :=
  chooseNatBetween 1 100 (by decide)

def gNonnegativeAmountNat (hi : Nat) : G Nat :=
  chooseNatBetween 0 hi (Nat.zero_le hi)

def nextBlockHeader (lc : TestLocalChain) (creator : TestAddress) (reward : Amount) :
    TestBlockHeader :=
  BlockHeader.mk (Base := TestBase) (lc.lc_height + 1) (lc.lc_slot + 1)
    lc.lc_fin_height reward creator

def invalidHeightHeader (lc : TestLocalChain) (creator : TestAddress) : TestBlockHeader :=
  BlockHeader.mk (Base := TestBase) lc.lc_height (lc.lc_slot + 1)
    lc.lc_fin_height 0 creator

def transferAction (frm to_ : TestAddress) (amount : Amount) : TestAction :=
  Action.mk (Base := TestBase) frm frm
    (ActionBody.act_transfer (Base := TestBase) to_ amount)

def originMismatchTransferAction : TestAction :=
  Action.mk (Base := TestBase) fixedUser10 fixedUser11
    (ActionBody.act_transfer (Base := TestBase) fixedUser10 0)

def invalidRootTransferAction : TestAction :=
  Action.mk (Base := TestBase) fixedContractBase fixedContractBase
    (ActionBody.act_transfer (Base := TestBase) fixedUser10 0)

def gTransferAction (maxAmount : Nat := 100) : G TestAction := do
  let frm ← gLocalAccountAddress
  let to_ ← gLocalAccountAddress
  let amount ← gNonnegativeAmountNat maxAmount
  return transferAction frm to_ (amount : Int)

def gFundedTransferBlock (lc : TestLocalChain) : G (TestBlockHeader × List TestAction) := do
  let creator ← gLocalAccountAddress
  let recipient ← gLocalAccountAddress
  let reward ← gPositiveRewardNat
  let amount ← gNonnegativeAmountNat reward
  let header := nextBlockHeader lc creator (reward : Int)
  let action := transferAction creator recipient (amount : Int)
  return (header, [action])

def addGeneratedTransferBlock (depthFirst : Bool) (lcb : TestLocalChainBuilder) :
    G (ConCert.Execution.ResultMonad.Result TestLocalChainBuilder TestAddBlockError) := do
  let block ← gFundedTransferBlock lcb.lcb_lc
  return add_block AddrSize depthFirst lcb block.1 block.2

def gLocalChainBuilder : Nat → G TestLocalChainBuilder
  | 0 => return lcb_initial AddrSize
  | n + 1 => do
      let lcb ← gLocalChainBuilder n
      match ← addGeneratedTransferBlock DepthFirst lcb with
      | .Ok lcb' => return lcb'
      | .Err _ => return lcb

end ConCert.Execution.Test.TraceGens
