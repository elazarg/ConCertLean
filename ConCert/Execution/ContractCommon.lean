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

axiom AddressMap_find_convertible :
  ∀ [Base : ChainBase] {V : Type},
    @AddressMap.find Base V = (fun addr m => FMap.find addr m)

axiom AddressMap_add_convertible :
  ∀ [Base : ChainBase] {V : Type},
    @AddressMap.add Base V = (fun addr v m => FMap.add addr v m)

/-! ### Utility helpers -/

def maybe (n : Nat) : Option Nat :=
  if n == 0 then none else some n

axiom maybe_cases :
  ∀ (n : Nat),
    (maybe n = none ∧ n = 0) ∨ (maybe n = some n ∧ n > 0)

axiom maybe_sub_add :
  ∀ (n value : Nat),
    value ≤ n →
    (maybe ((ConCert.Utils.Extras.withDefault 0 (maybe (n - value))) + value) = none ∧ n = 0) ∨
    (maybe ((ConCert.Utils.Extras.withDefault 0 (maybe (n - value))) + value) = some n)

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

-- TODO: port tactic destruct_throw_if
-- TODO: port tactic destruct_match_some
-- TODO: port tactic contract_simpl
-- TODO: port tactic result_to_option

end ConCert.Execution.ContractCommon
