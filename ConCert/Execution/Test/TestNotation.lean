/- Port of execution/test/TestNotation.v.

   Parameters carrier, generated-chain wrappers, and boolean checker
   combinators used by the ported smoke/property tests. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Test.TestUtils
import ConCert.Execution.Test.TraceGens

namespace ConCert.Execution.Test.TestNotation

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens

def max_trace_length : Nat := 7
def max_acts_per_block : Nat := 2
def act_depth : Nat := 3

variable [Base : ChainBase]

structure TestNotationParameters where
  gAction : @Environment Base → GOpt (@Action Base)

def bool_to_option {A : Type} (P : A → Bool) : A → Option Unit :=
  fun cs => if P cs then some () else none

def checkForAllStatesInTrace {A : Type}
    (Q : List (@ChainState Base) → @ChainState Base → Bool) :
    A → List (@ChainState Base) → List (@ChainState Base) → Checker :=
  fun _ pre_trace post_trace =>
    checker (post_trace.foldl (fun a cs => a && Q pre_trace cs) true)

def forAllGeneratedLocalChainBuilders
    (blocks : Nat) (pf : TestLocalChainBuilder → Bool) : Checker :=
  forAllGen (gLocalChainBuilder blocks) pf

def forAllGeneratedLocalChains
    (blocks : Nat) (pf : TestLocalChain → Bool) : Checker :=
  forAllGeneratedLocalChainBuilders blocks (fun cb => pf cb.lcb_lc)

end ConCert.Execution.Test.TestNotation
