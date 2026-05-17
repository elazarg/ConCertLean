/- Port of examples/iTokenBuggy/iTokenBuggy.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Utils.Extras

namespace ConCert.Examples.ITokenBuggy

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Utils.Extras

variable [Base : ChainBase]

inductive Msg where
  | transfer_from (from_ to_ : Base.Address) (amount : Nat)
  | approve (delegate : Base.Address) (amount : Nat)
  | mint (amount : Nat)
  | burn (amount : Nat)
  deriving Serializable

structure State where
  total_supply : Nat
  balances : FMap Base.Address Nat
  allowances : FMap Base.Address (FMap Base.Address Nat)
  deriving Serializable

structure Setup where
  owner : Base.Address
  init_amount : Nat
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

def init (_chain : Chain) (_ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  .Ok
    { total_supply := setup.init_amount,
      balances := FMap.add setup.owner setup.init_amount FMap.empty,
      allowances := FMap.empty }

def try_mint (caller : Base.Address) (amount : Nat) (state : @State Base) :
    Result (@State Base) Error :=
  let new_balances :=
    FMap.partial_alter
      (fun balance => some (with_default 0 balance + amount))
      caller state.balances
  .Ok
    { state with
      total_supply := state.total_supply + amount,
      balances := new_balances }

def try_burn (caller : Base.Address) (burn_amount : Nat) (state : @State Base) :
    Result (@State Base) Error :=
  let caller_balance := with_default 0 (FMap.find caller state.balances)
  if caller_balance < burn_amount then
    .Err default_error
  else
    let new_balances := FMap.add caller (caller_balance - burn_amount) state.balances
    .Ok
      { state with
        total_supply := state.total_supply - burn_amount,
        balances := new_balances }

def try_transfer_from_buggy
    (delegate from_ to_ : Base.Address) (amount : Nat) (state : @State Base) :
    Result (@State Base) Error :=
  match FMap.find from_ state.allowances with
  | none => .Err default_error
  | some from_allowances_map =>
      match FMap.find delegate from_allowances_map with
      | none => .Err default_error
      | some delegate_allowance =>
          let from_balance := with_default 0 (FMap.find from_ state.balances)
          let to_balance := with_default 0 (FMap.find to_ state.balances)
          if ((delegate_allowance < amount) && !(Base.address_eqb from_ to_)) ||
              (from_balance < amount) then
            .Err default_error
          else
            let new_allowances :=
              FMap.add delegate (delegate_allowance - amount) from_allowances_map
            let new_balances := FMap.add from_ (from_balance - amount) state.balances
            let new_balances := FMap.add to_ (to_balance + amount) new_balances
            .Ok
              { state with
                balances := new_balances,
                allowances := FMap.add from_ new_allowances state.allowances }

def try_approve
    (caller delegate : Base.Address) (amount : Nat) (state : @State Base) :
    Result (@State Base) Error :=
  match FMap.find caller state.allowances with
  | some caller_allowances =>
      .Ok
        { state with
          allowances :=
            FMap.add caller (FMap.add delegate amount caller_allowances)
              state.allowances }
  | none =>
      .Ok
        { state with
          allowances :=
            FMap.add caller (FMap.add delegate amount FMap.empty)
              state.allowances }

def receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let sender := ctx.ctx_from
  if ctx.ctx_amount > 0 then
    .Err default_error
  else
    match maybe_msg with
    | some (.transfer_from from_ to_ amount) =>
        without_actions (Base := Base)
          (try_transfer_from_buggy sender from_ to_ amount state)
    | some (.approve delegate amount) =>
        without_actions (Base := Base) (try_approve sender delegate amount state)
    | some (.mint amount) =>
        without_actions (Base := Base) (try_mint sender amount state)
    | some (.burn amount) =>
        without_actions (Base := Base) (try_burn sender amount state)
    | none =>
        .Err default_error

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

def sum_balances (state : @State Base) : Nat :=
  ((FMap.elements state.balances).map (fun p : Base.Address × Nat => p.2)).sum

end ConCert.Examples.ITokenBuggy
