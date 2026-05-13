/- Port of execution/test/TestUtils.v.

   Minimal Plausible-based shim. The original is hundreds of QuickChick-specific
   helpers; we expose just enough to make the other test files type-check.
   Concrete generators/checkers can be filled in as needed. -/

import Plausible.Gen
import Plausible.Sampleable
import Plausible.Testable
import ConCert.Execution.Blockchain
import ConCert.Execution.Containers
import ConCert.Execution.Serializable
import ConCert.Execution.ChainedList

namespace ConCert.Execution.Test.TestUtils

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Containers
open Plausible

/-! QuickChick-style names mapped onto Plausible. -/

abbrev G := Plausible.Gen
abbrev GOpt (A : Type) := Plausible.Gen (Option A)

@[inline] def returnGen {A : Type} (a : A) : Plausible.Gen A := pure a
@[inline] def bindGen {A B : Type} (g : Plausible.Gen A) (f : A → Plausible.Gen B) :
    Plausible.Gen B := g >>= f

/-- A `Checker` here is just a thunked boolean — we don't drag in Plausible's
    `Testable` infrastructure since most call sites only need composition. -/
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

/-! Configuration constants. -/

def AddrSize : Nat := 256
def ContractAddrBase : Nat := 128
def DepthFirst : Bool := true

/-! Stub helpers — kept as polymorphic defs over an arbitrary `Base : ChainBase`
    so they compose with the rest of the blockchain layer. Concrete blockchain
    operations (`build_call`, `build_transfer`, `build_deploy`) come back as
    real defs over the proper `Action` / `ActionBody` types. -/

variable [Base : ChainBase]

/-- Constructing `Base.Address` values requires knowing the concrete address
    representation of the underlying chain. In test code parameterized over
    an abstract `ChainBase` we have to thread these through; we package them
    in a small typeclass that a concrete blockchain (e.g. `LocalChainBase`)
    instantiates. -/
class TestAddresses where
  addr_of_Z : Int → Base.Address
  addr_of_N : Nat → Base.Address

variable [TA : @TestAddresses Base]

def addr_of_Z (z : Int) : Base.Address := TA.addr_of_Z z
def addr_of_N (n : Nat) : Base.Address := TA.addr_of_N n

def zero_address : Base.Address := addr_of_Z 0
def creator       : Base.Address := addr_of_Z 10
def person_1      : Base.Address := addr_of_Z 11
def person_2      : Base.Address := addr_of_Z 12
def person_3      : Base.Address := addr_of_Z 13
def person_4      : Base.Address := addr_of_Z 14
def person_5      : Base.Address := addr_of_Z 15

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

/-! GOpt helpers. -/

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

end ConCert.Execution.Test.TestUtils
