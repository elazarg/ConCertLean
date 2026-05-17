/- Port of execution/test/TestUtils.v.

   Plausible-backed replacement for the QuickChick-specific helpers used by
   the ported test files. -/

import Plausible.Gen
import Plausible.Sampleable
import Plausible.Testable
import ConCert.Execution.Blockchain
import ConCert.Execution.BoundedN
import ConCert.Execution.Containers
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.ChainedList
import ConCert.Execution.Test.LocalBlockchain

namespace ConCert.Execution.Test.TestUtils

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainBuilder
open ConCert.Execution.SerializableBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open Plausible

/-! QuickChick-style names mapped onto Plausible. -/

abbrev G := Plausible.Gen
abbrev GOpt (A : Type) := Plausible.Gen (Option A)

@[inline] def returnGen {A : Type} (a : A) : Plausible.Gen A := pure a
@[inline] def bindGen {A B : Type} (g : Plausible.Gen A) (f : A → Plausible.Gen B) :
    Plausible.Gen B := g >>= f

/-- A `Checker` here is a thunked boolean. This avoids depending on
    Plausible's `Testable` infrastructure where call sites only need
    composition. -/
abbrev Checker := Plausible.Gen Bool

@[inline] def checker (b : Bool) : Checker := pure b
@[inline] def conjoin (cs : List Checker) : Checker :=
  cs.foldl (fun acc c => acc >>= fun a => c >>= fun b => pure (a && b)) (pure true)
@[inline] def disjoin (cs : List Checker) : Checker :=
  cs.foldl (fun acc c => acc >>= fun a => c >>= fun b => pure (a || b)) (pure false)
@[inline] def conjoin_map {A : Type} (f : A → Checker) (l : List A) : Checker :=
  conjoin (l.map f)
@[inline] def repeatn (n : Nat) (c : Checker) : Checker :=
  conjoin ((List.range n).map (fun _ => c))

structure CheckerConfig where
  numTests : Nat := 100
  maxSize : Nat := 25
  seed : Nat := 0
  deriving Repr

def defaultCheckerConfig : CheckerConfig := {}

def strictCheckerConfig : CheckerConfig :=
  { numTests := 200, maxSize := 50, seed := 20260514 }

structure CheckerFailure where
  sample : Nat
  size : Nat
  seed : Nat
  deriving Repr

structure ShrinkFailure where
  sample : Nat
  size : Nat
  seed : Nat
  shrinks : Nat
  counterexample : String
  deriving Repr

def checkerSampleSize (cfg : CheckerConfig) (sample : Nat) : Nat :=
  if cfg.numTests ≤ 1 then cfg.maxSize
  else sample * cfg.maxSize / (cfg.numTests - 1)

def runGenWithSeed {A : Type} (seed size : Nat) (g : G A) : IO A := do
  match (Plausible.runRandWith seed g).run ⟨size⟩ with
  | .ok a => pure a
  | .error (.genError msg) =>
      throw (IO.userError s!"generation failed at seed {seed}, size {size}: {msg}")

def runChecker (cfg : CheckerConfig) (c : Checker) : IO (Option CheckerFailure) := do
  if cfg.numTests = 0 then
    throw (IO.userError "checker configuration must run at least one sample")
  for sample in [0:cfg.numTests] do
    let size := checkerSampleSize cfg sample
    let seed := cfg.seed + sample
    let ok ← runGenWithSeed seed size c
    if !ok then
      return some { sample, size, seed }
  return none

def assertChecker (name : String) (cfg : CheckerConfig) (c : Checker) : IO Unit := do
  match ← runChecker cfg c with
  | none => pure ()
  | some failure =>
      throw (IO.userError
        s!"{name}: property falsified at sample {failure.sample}, size {failure.size}, seed {failure.seed}")

def assertCheckerFails (name : String) (cfg : CheckerConfig) (c : Checker) : IO Unit := do
  match ← runChecker cfg c with
  | some _ => pure ()
  | none =>
      throw (IO.userError
        s!"{name}: expected a generated counterexample, but all {cfg.numTests} samples passed")

def shrinkCounterexample {A : Type}
    (shrink : A → List A) (p : A → Bool) : Nat → A → A × Nat
  | 0, a => (a, 0)
  | fuel + 1, a =>
      match (shrink a).find? (fun a' => !(p a')) with
      | none => (a, 0)
      | some a' =>
          let (best, shrinks) := shrinkCounterexample shrink p fuel a'
          (best, shrinks + 1)

def runShrinkChecker {A : Type}
    (cfg : CheckerConfig) (g : G A) (shrink : A → List A)
    (showA : A → String) (p : A → Bool) : IO (Option ShrinkFailure) := do
  if cfg.numTests = 0 then
    throw (IO.userError "checker configuration must run at least one sample")
  for sample in [0:cfg.numTests] do
    let size := checkerSampleSize cfg sample
    let seed := cfg.seed + sample
    let a ← runGenWithSeed seed size g
    if !(p a) then
      let (small, shrinks) := shrinkCounterexample shrink p cfg.maxSize a
      return some
        { sample, size, seed, shrinks, counterexample := showA small }
  return none

def assertForAllShrink {A : Type}
    (name : String) (cfg : CheckerConfig) (g : G A) (shrink : A → List A)
    (showA : A → String) (p : A → Bool) : IO Unit := do
  match ← runShrinkChecker cfg g shrink showA p with
  | none => pure ()
  | some failure =>
      throw (IO.userError
        s!"{name}: property falsified at sample {failure.sample}, size {failure.size}, seed {failure.seed}; shrunk {failure.shrinks} times to {failure.counterexample}")

def assertForAllShrinkFails {A : Type}
    (name : String) (cfg : CheckerConfig) (g : G A) (shrink : A → List A)
    (showA : A → String) (p : A → Bool) : IO Unit := do
  match ← runShrinkChecker cfg g shrink showA p with
  | some _ => pure ()
  | none =>
      throw (IO.userError
        s!"{name}: expected a generated counterexample, but all {cfg.numTests} samples passed")

def shrinkNat : Nat → List Nat
  | 0 => []
  | n => [n / 2, 0].eraseDups

def shrinkInt (i : Int) : List Int :=
  if i = 0 then [] else [i / 2, 0]

def forAllGen {A : Type} (g : G A) (p : A → Bool) : Checker := do
  let a ← g
  checker (p a)

def chooseNatBetween (lo hi : Nat) (h : lo ≤ hi) : G Nat := do
  let n ← Plausible.Gen.choose Nat lo hi h
  return n.val

def chooseIntBetween (lo hi : Int) (h : lo ≤ hi) : G Int := do
  let n ← Plausible.Gen.choose Int lo hi h
  return n.val

def chooseAmountBetween (lo hi : Amount) (h : lo ≤ hi) : G Amount :=
  chooseIntBetween lo hi h

def chooseBool : G Bool :=
  Plausible.Gen.chooseAny Bool

/-! Configuration constants. -/

def AddrSize : Nat := 256
def ContractAddrBase : Nat := 128
def DepthFirst : Bool := true

/-! Test helpers over an arbitrary `Base : ChainBase`. Concrete
    blockchain operations (`build_call`, `build_transfer`, `build_deploy`) are
    real definitions over the proper `Action` / `ActionBody` types. -/

/-- Constructing `Base.Address` values requires knowing the concrete address
    representation of the underlying chain. In test code parameterized over an
    abstract `ChainBase`, these conversions must be supplied explicitly. The
    small typeclass is instantiated by concrete blockchains such as
    `LocalChainBase`. -/
class TestAddresses (Base : ChainBase) where
  addr_of_Z : Int → Base.Address
  addr_of_N : Nat → Base.Address

private def localDefaultAddress : ConCert.Execution.BoundedN AddrSize :=
  ⟨0, by unfold AddrSize; decide⟩

instance localChainBaseTestAddresses :
    TestAddresses (ConCert.Execution.Test.LocalBlockchain.LocalChainBase AddrSize) where
  addr_of_Z z :=
    match ConCert.Execution.BoundedN.of_Z (bound := AddrSize) z with
    | some addr => addr
    | none => localDefaultAddress
  addr_of_N n :=
    match ConCert.Execution.BoundedN.of_N (bound := AddrSize) n with
    | some addr => addr
    | none => localDefaultAddress

noncomputable instance localChainBuilder :
    @ChainBuilderType (ConCert.Execution.Test.LocalBlockchain.LocalChainBase AddrSize) :=
  ConCert.Execution.Test.LocalBlockchain.LocalChainBuilderImpl AddrSize DepthFirst

def empty_chain : ConCert.Execution.Test.LocalBlockchain.LocalChainBuilder AddrSize :=
  ConCert.Execution.Test.LocalBlockchain.lcb_initial AddrSize

def get_contracts
    (chain : ConCert.Execution.Test.LocalBlockchain.LocalChainBuilder AddrSize) :=
  chain.lcb_lc.lc_contracts

variable [Base : ChainBase] [TA : TestAddresses Base]

def addr_of_Z (z : Int) : Base.Address := TA.addr_of_Z z
def addr_of_N (n : Nat) : Base.Address := TA.addr_of_N n

def zero_address : Base.Address := addr_of_Z 0
def creator       : Base.Address := addr_of_Z 10
def person_1      : Base.Address := addr_of_Z 11
def person_2      : Base.Address := addr_of_Z 12
def person_3      : Base.Address := addr_of_Z 13
def person_4      : Base.Address := addr_of_Z 14
def person_5      : Base.Address := addr_of_Z 15
def contract_base_addr : Base.Address := addr_of_N ContractAddrBase

def test_chain_addrs_3 : List Base.Address := [person_1, person_2, person_3]
def test_chain_addrs_5 : List Base.Address := test_chain_addrs_3 ++ [person_4, person_5]

def build_call {A : Type} [Serializable A]
    (frm to_ : Base.Address) (amount : Amount) (msg : A) : @Action Base :=
  { act_origin := frm, act_from := frm,
    act_body := .act_call to_ amount (serialize msg) }

def build_transfer (frm to_ : Base.Address) (amount : Amount) : @Action Base :=
  { act_origin := frm, act_from := frm, act_body := .act_transfer to_ amount }

def build_transfers (frm : Base.Address) (txs : List (Base.Address × Amount)) :
    List (@Action Base) :=
  txs.map (fun p => build_transfer frm p.1 p.2)

def build_deploy {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (frm : Base.Address) (amount : Amount)
    (c : @Contract Base Setup Msg State Error _ _ _ _) (setup : Setup) : @Action Base :=
  { act_origin := frm, act_from := frm, act_body := create_deployment amount c setup }

def string_of_FMap {A B : Type} [Ord A] [LawfulOrd A]
    (showA : A → String) (showB : B → String) (m : FMap A B) : String :=
  "[" ++ String.intercalate "; "
    ((FMap.elements m).map (fun p => showA p.1 ++ "-->" ++ showB p.2))
  ++ "]"

def filter_FMap {A B : Type} [Ord A] [LawfulOrd A]
    (f : (A × B) → Bool) (m : FMap A B) : FMap A B :=
  FMap.of_list ((FMap.elements m).filter f)

def map_values_FMap {A B C : Type} [Ord A] [LawfulOrd A] (f : B → C) (m : FMap A B) :
    FMap A C :=
  FMap.of_list ((FMap.elements m).map (fun p => (p.1, f p.2)))

def FMap_find_ {A B : Type} [Ord A] [LawfulOrd A]
    (k : A) (m : FMap A B) (default : B) : B :=
  match FMap.find k m with
  | some v => v
  | none => default

def get_contract_state {S : Type} [Serializable S]
    (env : @Environment Base) (addr : Base.Address) : Option S :=
  match env.env_contract_states addr with
  | some ser => deserialize ser
  | none => none

def split_at_first_satisfying_fix {A : Type} (p : A → Bool) :
    List A → List A → Option (List A × List A)
  | [], _ => none
  | x :: xs, acc =>
      if p x then
        some (acc ++ [x], xs)
      else
        split_at_first_satisfying_fix p xs (acc ++ [x])

def split_at_first_satisfying {A : Type} (p : A → Bool) (l : List A) :
    Option (List A × List A) :=
  split_at_first_satisfying_fix p l []

def pickDrop {T E : Type} (default : E)
    (xs : List (Nat × G (Result T E))) (n : Nat) :
    Nat × G (Result T E) × List (Nat × G (Result T E)) :=
  match xs with
  | [] => (0, returnGen (.Err default), [])
  | (k, x) :: xs =>
      if n < k then
        (k, x, xs)
      else
        let (k', x', xs') := pickDrop default xs (n - k)
        (k', x', (k, x) :: xs')

def backtrack_result_fix {T E : Type} (default : E) :
    Nat → List (Nat × G (Result T E)) → G (Result T E)
  | 0, _ => returnGen (.Err default)
  | _ + 1, [] => returnGen (.Err default)
  | fuel + 1, (_, g) :: gs => do
      let ma ← g
      match ma with
      | .Ok _ => returnGen ma
      | .Err _ => backtrack_result_fix default fuel gs

def backtrack_result {T E : Type} (default : E)
    (gs : List (Nat × G (Result T E))) : G (Result T E) :=
  backtrack_result_fix default gs.length gs

/-! GOpt helpers. -/

def elems_opt {A : Type} (l : List A) : GOpt A :=
  match l with
  | x :: xs => (do
      let a ← Plausible.Gen.elements (x :: xs) (by simp)
      return some a : Plausible.Gen (Option A))
  | [] => returnGen none

def returnGenSome {A : Type} (a : A) : GOpt A := (pure (some a) : Plausible.Gen _)

def liftOpt {A B : Type} (f : A → B) (g : GOpt A) : GOpt B :=
  (g >>= fun oa =>
    (match oa with
     | some a => pure (some (f a))
     | none   => pure none : Plausible.Gen _) : Plausible.Gen _)

def liftOptGen {A : Type} (g : Plausible.Gen A) : GOpt A :=
  (g >>= fun a => (pure (some a) : Plausible.Gen _) : Plausible.Gen _)

def bindOpt {A B : Type} (g : GOpt A) (f : A → GOpt B) : GOpt B :=
  (g >>= fun oa =>
    (match oa with
     | some a => f a
     | none   => pure none : Plausible.Gen _) : Plausible.Gen _)

def sampleFMapOpt {A B : Type} [Ord A] [LawfulOrd A] (m : FMap A B) :
    GOpt (A × B) :=
  elems_opt (FMap.elements m)

def sampleFMapOpt_filter {A B : Type} [Ord A] [LawfulOrd A]
    (m : FMap A B) (f : (A × B) → Bool) : GOpt (A × B) :=
  elems_opt ((FMap.elements m).filter f)

def sample2UniqueFMapOpt {A B : Type} [Ord A] [LawfulOrd A] (m : FMap A B) :
    GOpt ((A × B) × (A × B)) :=
  bindOpt (sampleFMapOpt m) (fun p1 =>
    bindOpt (sampleFMapOpt (FMap.remove p1.1 m)) (fun p2 =>
      returnGenSome (p1, p2)))

def gBoundedNOpt (bound : Nat) : GOpt (ConCert.Execution.BoundedN bound) :=
  if h : 0 < bound then (do
    let n ← Plausible.Gen.choose Nat 0 (bound - 1) (by omega)
    return some ⟨n.val, by have hn := n.property.2; omega⟩ :
      Plausible.Gen (Option (ConCert.Execution.BoundedN bound)))
  else
    returnGen none

def gBoundedN : G (ConCert.Execution.BoundedN AddrSize) := do
  match ← gBoundedNOpt AddrSize with
  | some addr => return addr
  | none => return localDefaultAddress

def gAddress_ (default : Base.Address) (addrs : List Base.Address) : G Base.Address :=
  match addrs with
  | [] => returnGen default
  | addr :: rest => Plausible.Gen.elements (addr :: rest) (by simp)

def gAddress (addrs : List Base.Address) : G Base.Address :=
  gAddress_ zero_address addrs

def gTestAddrs3 : G Base.Address := gAddress test_chain_addrs_3

def gTestAddrs5 : G Base.Address := gAddress test_chain_addrs_5

def gUserAddress : GOpt Base.Address :=
  returnGenSome (addr_of_N 0)

def gContractAddress : GOpt Base.Address :=
  returnGenSome contract_base_addr

def gAddrWithout (ws addrs : List Base.Address) : G Base.Address :=
  let addrs' := addrs.filter (fun a => !(ws.any (fun w => Base.address_eqb a w)))
  gAddress addrs'

def gUniqueAddrPair (addrs : List Base.Address) : GOpt (Base.Address × Base.Address) :=
  bindOpt (elems_opt addrs) (fun addr1 =>
    let addrs' := addrs.filter (fun a => !(Base.address_eqb addr1 a))
    bindOpt (elems_opt addrs') (fun addr2 =>
      returnGenSome (addr1, addr2)))

def optToVector {A : Type} : Nat → GOpt A → G (List A)
  | 0, _ => returnGen []
  | n + 1, g => do
      let oa ← g
      let rest ← optToVector n g
      match oa with
      | some a => returnGen (a :: rest)
      | none => returnGen rest

def isSomeCheck {A : Type} (a : Option A) (f : A → Bool) : Checker :=
  match a with
  | some v => checker (f v)
  | none => checker true

def existsP {A : Type} (g : G A) (p : A → Bool) : Checker := do
  let a ← g
  checker (p a)

def existsPShrink {A : Type} (g : G A) (p : A → Bool) : Checker :=
  existsP g p

def discard_empty {A : Type} (l : List A) (f : List A → Checker) : Checker :=
  match l with
  | [] => checker true
  | _ => f l

def forEachMapEntry {A B : Type} [Ord A] [LawfulOrd A]
    (m : FMap A B) (pf : A → B → Bool) : Checker :=
  conjoin_map (fun p => checker (pf p.1 p.2)) (FMap.elements m)

def repeatWith {A : Type} (l : List A) (c : A → Checker) : Checker :=
  conjoin (l.map c)

def discardToSuccess (p : Checker) : Checker := p

def conjoin_no_discard (l : List Checker) : Checker :=
  conjoin_map discardToSuccess l

end ConCert.Execution.Test.TestUtils
