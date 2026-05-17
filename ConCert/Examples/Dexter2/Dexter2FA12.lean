/- Port of examples/dexter2/Dexter2FA12.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Utils.Extras

namespace ConCert.Examples.Dexter2.FA12

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Utils.Extras

variable [Base : ChainBase]

def non_zero_amount (amt : Amount) : Bool := decide (0 < amt)

structure Callback where
  return_addr : Base.Address
  deriving Serializable

instance : Coe (@Callback Base) Base.Address where
  coe c := c.return_addr

structure TransferParam where
  from_ : Base.Address
  to_ : Base.Address
  value : Nat
  deriving Serializable

structure ApproveParam where
  spender : Base.Address
  value_ : Nat
  deriving Serializable

structure MintOrBurnParam where
  quantity : Int
  target : Base.Address
  deriving Serializable

structure GetAllowanceParam where
  request : Base.Address × Base.Address
  allowance_callback : @Callback Base
  deriving Serializable

structure GetBalanceParam where
  owner_ : Base.Address
  balance_callback : @Callback Base
  deriving Serializable

structure GetTotalSupplyParam where
  request_ : Unit
  supply_callback : @Callback Base
  deriving Serializable

structure State where
  tokens : AddressMap.AddrMap (Base := Base) Nat
  allowances : FMap (Base.Address × Base.Address) Nat
  admin : Base.Address
  total_supply : Nat
  deriving Serializable

structure Setup where
  admin_ : Base.Address
  lqt_provider : Base.Address
  initial_pool : Nat
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

inductive FA12ReceiverMsg (Msg' : Type) where
  | receive_allowance (n : Nat)
  | receive_balance_of (n : Nat)
  | receive_total_supply (n : Nat)
  | other_msg (msg : Msg')
  deriving Serializable

inductive Msg where
  | msg_transfer (param : @TransferParam Base)
  | msg_approve (param : @ApproveParam Base)
  | msg_mint_or_burn (param : @MintOrBurnParam Base)
  | msg_get_allowance (param : @GetAllowanceParam Base)
  | msg_get_balance (param : @GetBalanceParam Base)
  | msg_get_total_supply (param : @GetTotalSupplyParam Base)
  deriving Serializable

def mintedOrBurnedTokens : Option (@Msg Base) → Int
  | some (.msg_mint_or_burn param) => param.quantity
  | _ => 0

def find_allowance
    (k : Base.Address × Base.Address)
    (m : FMap (Base.Address × Base.Address) Nat) : Option Nat :=
  FMap.find k m

def update_allowance
    (k : Base.Address × Base.Address) (val : Option Nat)
    (m : FMap (Base.Address × Base.Address) Nat) :
    FMap (Base.Address × Base.Address) Nat :=
  FMap.update k val m

def empty_allowance : FMap (Base.Address × Base.Address) Nat := FMap.empty

def try_transfer
    (sender : Base.Address) (param : @TransferParam Base) (state : @State Base) :
    Result (@State Base) Error :=
  let allowances_ := state.allowances
  let tokens_ := state.tokens
  let allowancesResult : Result (FMap (Base.Address × Base.Address) Nat) Error :=
    if Base.address_eqb sender param.from_ then
      .Ok allowances_
    else
      let allowance_key := (param.from_, sender)
      let authorized_value := with_default 0 (find_allowance allowance_key allowances_)
      if authorized_value < param.value then
        .Err default_error
      else
        .Ok (update_allowance allowance_key
          (maybe (authorized_value - param.value)) allowances_)
  match allowancesResult with
  | .Err e => .Err e
  | .Ok allowances_ =>
      let from_balance := with_default 0 (AddressMap.find param.from_ tokens_)
      if from_balance < param.value then
        .Err default_error
      else
        let tokens_ :=
          AddressMap.update param.from_ (maybe (from_balance - param.value)) tokens_
        let to_balance := with_default 0 (AddressMap.find param.to_ tokens_)
        let tokens_ :=
          AddressMap.update param.to_ (maybe (to_balance + param.value)) tokens_
        .Ok { state with tokens := tokens_, allowances := allowances_ }

def try_approve
    (sender : Base.Address) (param : @ApproveParam Base) (state : @State Base) :
    Result (@State Base) Error :=
  let allowance_key := (sender, param.spender)
  let previous_value := with_default 0 (find_allowance allowance_key state.allowances)
  if (0 < previous_value) && (0 < param.value_) then
    .Err default_error
  else
    let allowances_ := update_allowance allowance_key (maybe param.value_) state.allowances
    .Ok { state with allowances := allowances_ }

def try_mint_or_burn
    (sender : Base.Address) (param : @MintOrBurnParam Base)
    (state : @State Base) : Result (@State Base) Error :=
  if !(Base.address_eqb sender state.admin) then
    .Err default_error
  else
    let old_balance := with_default 0 (AddressMap.find param.target state.tokens)
    let new_balance := Int.ofNat old_balance + param.quantity
    if new_balance < 0 then
      .Err default_error
    else
      let tokens_ :=
        AddressMap.update param.target (maybe new_balance.toNat) state.tokens
      let total_supply_ :=
        (Int.ofNat state.total_supply + param.quantity).natAbs
      .Ok { state with tokens := tokens_, total_supply := total_supply_ }

def mk_callback
    (to_addr : Base.Address) (msg : FA12ReceiverMsg Unit) :
    @ActionBody Base :=
  .act_call to_addr 0 (serialize msg)

def receive_allowance_ (n : Nat) : FA12ReceiverMsg Unit := .receive_allowance n
def receive_balance_of_ (n : Nat) : FA12ReceiverMsg Unit := .receive_balance_of n
def receive_total_supply_ (n : Nat) : FA12ReceiverMsg Unit := .receive_total_supply n

def try_get_allowance
    (_sender : Base.Address) (param : @GetAllowanceParam Base) (state : @State Base) :
    List (@ActionBody Base) :=
  let value := with_default 0 (find_allowance param.request state.allowances)
  [mk_callback param.allowance_callback.return_addr (receive_allowance_ value)]

def try_get_balance
    (_sender : Base.Address) (param : @GetBalanceParam Base) (state : @State Base) :
    List (@ActionBody Base) :=
  let value := with_default 0 (AddressMap.find param.owner_ state.tokens)
  [mk_callback param.balance_callback.return_addr (receive_balance_of_ value)]

def try_get_total_supply
    (_sender : Base.Address) (param : @GetTotalSupplyParam Base) (state : @State Base) :
    List (@ActionBody Base) :=
  [mk_callback param.supply_callback.return_addr
    (receive_total_supply_ state.total_supply)]

def init (_chain : Chain) (_ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  .Ok
    { tokens := AddressMap.add setup.lqt_provider setup.initial_pool AddressMap.empty,
      allowances := empty_allowance,
      admin := setup.admin_,
      total_supply := setup.initial_pool }

def receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let sender := ctx.ctx_from
  if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else
    match maybe_msg with
    | some (.msg_transfer param) =>
        without_actions (Base := Base) (try_transfer sender param state)
    | some (.msg_approve param) =>
        without_actions (Base := Base) (try_approve sender param state)
    | some (.msg_mint_or_burn param) =>
        without_actions (Base := Base) (try_mint_or_burn sender param state)
    | some (.msg_get_allowance param) =>
        .Ok (state, try_get_allowance sender param state)
    | some (.msg_get_balance param) =>
        .Ok (state, try_get_balance sender param state)
    | some (.msg_get_total_supply param) =>
        .Ok (state, try_get_total_supply sender param state)
    | none =>
        .Err default_error

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

def get_balance (addr : Base.Address) (state : @State Base) : Nat :=
  with_default 0 (FMap.find addr state.tokens)

def get_allowance
    (owner spender : Base.Address) (state : @State Base) : Nat :=
  with_default 0 (FMap.find (owner, spender) state.allowances)

end ConCert.Examples.Dexter2.FA12
