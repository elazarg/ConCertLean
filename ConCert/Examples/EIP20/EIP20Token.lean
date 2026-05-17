/- Port of examples/eip20/EIP20Token.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Utils.Extras

namespace ConCert.Examples.EIP20.EIP20Token

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Utils.Extras

variable [Base : ChainBase]

abbrev TokenValue : Type := Nat

inductive Msg where
  | transfer (to_ : Base.Address) (amount : TokenValue)
  | transfer_from (from_ to_ : Base.Address) (amount : TokenValue)
  | approve (delegate : Base.Address) (amount : TokenValue)
  deriving Serializable

structure State where
  total_supply : TokenValue
  balances : AddressMap.AddrMap (Base := Base) TokenValue
  allowances : AddressMap.AddrMap (Base := Base)
    (AddressMap.AddrMap (Base := Base) TokenValue)
  deriving Serializable

structure Setup where
  owner : Base.Address
  init_amount : TokenValue
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

def error {T : Type} : Result T Error :=
  .Err default_error

def init (_chain : Chain) (_ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  .Ok
    { total_supply := setup.init_amount,
      balances := AddressMap.add setup.owner setup.init_amount AddressMap.empty,
      allowances := AddressMap.empty }

def increment_balance
    (m : AddressMap.AddrMap (Base := Base) TokenValue)
    (addr : Base.Address) (inc : TokenValue) :
    AddressMap.AddrMap (Base := Base) TokenValue :=
  match AddressMap.find addr m with
  | some old => AddressMap.add addr (old + inc) m
  | none => AddressMap.add addr inc m

def try_transfer
    (from_ to_ : Base.Address) (amount : TokenValue) (state : @State Base) :
    Result (@State Base) Error :=
  let from_balance := with_default 0 (AddressMap.find from_ state.balances)
  if from_balance < amount then
    error
  else
    let new_balances := AddressMap.add from_ (from_balance - amount) state.balances
    let new_balances := increment_balance new_balances to_ amount
    .Ok { state with balances := new_balances }

def try_transfer_from
    (delegate from_ to_ : Base.Address) (amount : TokenValue) (state : @State Base) :
    Result (@State Base) Error :=
  match AddressMap.find from_ state.allowances with
  | none => .Err default_error
  | some from_allowances_map =>
      match AddressMap.find delegate from_allowances_map with
      | none => .Err default_error
      | some delegate_allowance =>
          let from_balance := with_default 0 (AddressMap.find from_ state.balances)
          if (delegate_allowance < amount) || (from_balance < amount) then
            error
          else
            let new_allowances :=
              AddressMap.add delegate (delegate_allowance - amount) from_allowances_map
            let new_balances := AddressMap.add from_ (from_balance - amount) state.balances
            let new_balances := increment_balance new_balances to_ amount
            .Ok
              { state with
                balances := new_balances,
                allowances := AddressMap.add from_ new_allowances state.allowances }

def try_approve
    (caller delegate : Base.Address) (amount : TokenValue) (state : @State Base) :
    Result (@State Base) Error :=
  match AddressMap.find caller state.allowances with
  | some caller_allowances =>
      .Ok
        { state with
          allowances :=
            AddressMap.add caller
              (AddressMap.add delegate amount caller_allowances)
              state.allowances }
  | none =>
      .Ok
        { state with
          allowances :=
            AddressMap.add caller
              (AddressMap.add delegate amount AddressMap.empty)
              state.allowances }

def receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let sender := ctx.ctx_from
  if ctx.ctx_amount > 0 then
    error
  else
    match maybe_msg with
    | some (.transfer to_ amount) =>
        without_actions (Base := Base) (try_transfer sender to_ amount state)
    | some (.transfer_from from_ to_ amount) =>
        without_actions (Base := Base) (try_transfer_from sender from_ to_ amount state)
    | some (.approve delegate amount) =>
        without_actions (Base := Base) (try_approve sender delegate amount state)
    | none =>
        error

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

def sum_balances (state : @State Base) : Nat :=
  ((FMap.elements state.balances).map (fun p : Base.Address × TokenValue => p.2)).sum

def get_allowance (state : @State Base) (from_ delegate : Base.Address) : TokenValue :=
  with_default 0
    (FMap.find delegate
      (with_default (FMap.empty : AddressMap.AddrMap (Base := Base) TokenValue)
        (FMap.find from_ state.allowances)))

end ConCert.Examples.EIP20.EIP20Token
