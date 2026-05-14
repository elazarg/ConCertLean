/- Port of execution/theories/ContractCommon.v -/

import ConCert.Utils.Extras
import ConCert.Execution.Blockchain
import ConCert.Execution.Containers
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad

namespace ConCert.Execution.ContractCommon

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.Monad

namespace AddressMap

variable [Base : ChainBase]

abbrev AddrMap (V : Type) := FMap Base.Address V

def find {V : Type} (addr : Base.Address) (m : AddrMap V) : Option V :=
  FMap.find addr m

def add {V : Type} (addr : Base.Address) (val : V) (m : AddrMap V) : AddrMap V :=
  FMap.add addr val m

def values {V : Type} (m : AddrMap V) : List V := FMap.values m
def keys {V : Type} (m : AddrMap V) : List Base.Address := FMap.keys m

def of_list {V : Type} (l : List (Base.Address × V)) : AddrMap V :=
  FMap.of_list l

def empty {V : Type} : AddrMap V := FMap.empty

def update {V : Type} (addr : Base.Address) (val : Option V) (m : AddrMap V) : AddrMap V :=
  FMap.update addr val m

end AddressMap

theorem AddressMap_find_convertible
    [Base : ChainBase] {V : Type} :
    @AddressMap.find Base V = (fun addr m => FMap.find addr m) := rfl

theorem AddressMap_add_convertible
    [Base : ChainBase] {V : Type} :
    @AddressMap.add Base V = (fun addr v m => FMap.add addr v m) := rfl

/-! ### Utility helpers -/

def maybe (n : Nat) : Option Nat :=
  if n == 0 then none else some n

theorem maybe_cases (n : Nat) :
    (maybe n = none ∧ n = 0) ∨ (maybe n = some n ∧ n > 0) := by
  unfold maybe
  by_cases h : n = 0
  · subst h; left; exact ⟨rfl, rfl⟩
  · right
    have hne : (n == 0) = false := by simp [h]
    rw [hne]
    exact ⟨rfl, Nat.pos_of_ne_zero h⟩

theorem maybe_sub_add (n value : Nat) (h : value ≤ n) :
    (maybe ((ConCert.Utils.Extras.withDefault 0 (maybe (n - value))) + value) = none ∧ n = 0) ∨
    (maybe ((ConCert.Utils.Extras.withDefault 0 (maybe (n - value))) + value) = some n) := by
  rcases maybe_cases (n - value) with ⟨hm, hsub⟩ | ⟨hm, hsub⟩
  · -- n - value = 0, so n = value (since value ≤ n means value = n)
    have hn : n = value := by omega
    rw [hm]
    show _ = none ∧ _ = 0 ∨ _ = some n
    unfold ConCert.Utils.Extras.withDefault maybe
    by_cases hv : value = 0
    · subst hv; subst hn; left; exact ⟨rfl, rfl⟩
    · right
      have hne : ((0 + value) == 0) = false := by simp [hv]
      rw [hne]
      simp [hn]
  · rw [hm]
    right
    unfold ConCert.Utils.Extras.withDefault maybe
    have hnv : (n - value + value) = n := Nat.sub_add_cancel h
    have hne : ((n - value + value) == 0) = false := by simp [hnv]; omega
    rw [hne, hnv]; rfl

def throwIf {E : Type} (cond : Bool) (err : E) : Result Unit E :=
  if cond then .Err err else .Ok ()

variable [Base : ChainBase]

def without_actions {T E : Type} (x : Result T E) :
    Result (T × List (@ActionBody Base)) E :=
  match x with
  | .Ok v => .Ok (v, [])
  | .Err e => .Err e

def not_payable {T E : Type}
    (ctx : @ContractCallContext Base) (x : Result T E) (err : E) : Result T E :=
  match throwIf (ctx.ctx_amount > 0) err with
  | .Ok _ => x
  | .Err e => .Err e

syntax "destruct_throw_if" : tactic
syntax "destruct_match_some" : tactic
syntax "contract_simpl" : tactic
syntax "result_to_option" : tactic

macro_rules
  | `(tactic| destruct_throw_if) =>
      `(tactic| unfold throwIf at * <;> split at * <;> simp_all)
  | `(tactic| destruct_match_some) =>
      `(tactic| first | casesm* Option _ <;> simp_all | split <;> simp_all)
  | `(tactic| contract_simpl) =>
      `(tactic| simp_all [throwIf, without_actions, not_payable, maybe,
        ConCert.Execution.ResultMonad.Result.bind,
        ConCert.Execution.ResultMonad.option_of_result,
        ConCert.Execution.ResultMonad.result_of_option,
        ConCert.Execution.ResultMonad.isOk,
        ConCert.Execution.ResultMonad.isErr])
  | `(tactic| result_to_option) =>
      `(tactic| simp_all [ConCert.Execution.ResultMonad.option_of_result,
        ConCert.Execution.ResultMonad.result_of_option])

end ConCert.Execution.ContractCommon
