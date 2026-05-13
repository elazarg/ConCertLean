/- Port of execution/test/TraceGens.v.

   The original is a large collection of QuickChick generators and checkers
   over `ChainBuilder` / `ChainTrace`. We expose a minimal shim with the
   shrinkers and a few helpers; the bulk of the generator combinators are
   to be ported on demand. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Serializable
import ConCert.Execution.ChainedList
import ConCert.Execution.Test.TestUtils

namespace ConCert.Execution.Test.TraceGens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils

variable [Base : ChainBase] [TA : @TestAddresses Base]

def BlockReward : Amount := 50
def BlockCreator : Base.Address := @creator Base TA
def MaxGenAttempts : Nat := 2

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

def existsb_chaintrace (pf : @ChainState Base → Bool)
    (states : List (@ChainState Base)) : Bool :=
  states.any pf

end ConCert.Execution.Test.TraceGens
