/- Executable port of examples/cis1/CIS1wccd.v plus core CIS1 data shapes. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Examples.CIS1.CIS1Utils
import ConCert.Utils.Extras

namespace ConCert.Examples.CIS1

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Utils.Extras

abbrev TokenAmount : Type := Nat

namespace WCCD

variable [Base : ChainBase]

abbrev TokenID : Type := Unit

structure TransferParam where
  token_id : TokenID
  amount : TokenAmount
  from_ : Base.Address
  to_ : Base.Address
  deriving Serializable

inductive OpUpdateKind where
  | opAdd
  | opDelete
  deriving Serializable

inductive Msg where
  | wccd_msg_transfer (params : List (@TransferParam Base))
  | wccd_msg_balanceOf (query : List Base.Address) (send_results_to : Base.Address)
  | wccd_msg_updateOperator (params : List (OpUpdateKind × Base.Address))
  | wccd_msg_mint (receiver : Base.Address)
  | wccd_msg_burn (amount : TokenAmount)
  deriving Serializable

structure AddressState where
  wccd_balance : TokenAmount
  wccd_operators : List Base.Address
  deriving DecidableEq, Serializable

abbrev State : Type := AddressMap.AddrMap (Base := Base) (@AddressState Base)
abbrev Error : Type := Unit

def requireTrue (cond : Bool) : Option Unit :=
  if cond then some () else none

def removeAddress (addr : Base.Address) (operators : List Base.Address) :
    List Base.Address :=
  operators.filter (fun op => !(Base.address_eqb addr op))

def increment_balance
    (st : @State Base) (addr : Base.Address) (inc : TokenAmount) : @State Base :=
  match AddressMap.find addr st with
  | some old =>
      AddressMap.add addr { old with wccd_balance := old.wccd_balance + inc } st
  | none =>
      AddressMap.add addr { wccd_balance := inc, wccd_operators := [] } st

def decrement_balance
    (st : @State Base) (addr : Base.Address) (dec : TokenAmount) :
    Option (@State Base) := do
  let old ← AddressMap.find addr st
  let old_balance := old.wccd_balance
  let _ ← requireTrue (dec <= old_balance)
  some (AddressMap.add addr { old with wccd_balance := old_balance - dec } st)

def is_operator (addr owner : Base.Address) (st : @State Base) : Bool :=
  match AddressMap.find owner st with
  | some v => v.wccd_operators.any (fun x => Base.address_eqb addr x)
  | none => false

def wccd_transfer_single
    (_token_id : TokenID) (amount : TokenAmount)
    (owner from_ to_ : Base.Address) (prev_st : @State Base) :
    Option (@State Base) := do
  let _ ← requireTrue (Base.address_eqb owner from_ || is_operator from_ owner prev_st)
  let st ← decrement_balance prev_st from_ amount
  some (increment_balance st to_ amount)

def wccd_transfer
    (ctx : @ContractCallContext Base) (transfers : List (@TransferParam Base))
    (prev_st : @State Base) : Option (@State Base) :=
  transfers.foldl
    (fun acc transfer =>
      match acc with
      | none => none
      | some st =>
          wccd_transfer_single () transfer.amount ctx.ctx_from
            transfer.from_ transfer.to_ st)
    (some prev_st)

def get_balance_opt (addr : Base.Address) (st : @State Base) :
    Option TokenAmount :=
  match AddressMap.find addr st with
  | some data => some data.wccd_balance
  | none => none

def wccd_balanceOf (query : List Base.Address) (st : @State Base) :
    List (TokenID × Base.Address × TokenAmount) :=
  query.map (fun addr => ((), addr, with_default 0 (get_balance_opt addr st)))

def add_remove (operators : List Base.Address)
    (param : OpUpdateKind × Base.Address) : List Base.Address :=
  match param.1 with
  | .opAdd => param.2 :: operators
  | .opDelete => removeAddress param.2 operators

def wccd_updateOperator
    (owner : Base.Address) (params : List (OpUpdateKind × Base.Address))
    (prev_st : @State Base) : Option (@State Base) := do
  let owner_data ← AddressMap.find owner prev_st
  let updated_owner_data :=
    { owner_data with
      wccd_operators := params.foldl add_remove owner_data.wccd_operators }
  some (AddressMap.add owner updated_owner_data prev_st)

def wccd_receive_option
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (prev_st : @State Base) (msg : Option Msg) :
    Option (@State Base × List (@ActionBody Base)) :=
  match msg with
  | some (.wccd_msg_transfer params) => do
      let next_st ← wccd_transfer ctx params prev_st
      let contract_accounts := params.filter (fun x => Base.address_is_contract x.to_)
      let mk_callback (x : @TransferParam Base) :=
        let payload : TokenID × TokenAmount × Base.Address :=
          ((), x.amount, x.from_)
        ActionBody.act_call x.to_ 0 (serialize payload)
      some (next_st, contract_accounts.map mk_callback)
  | some (.wccd_msg_balanceOf query send_to) => do
      let balances := wccd_balanceOf query prev_st
      let _ ← requireTrue (Base.address_is_contract send_to)
      some (prev_st, [.act_call send_to 0 (serialize balances)])
  | some (.wccd_msg_updateOperator params) => do
      let next_st ← wccd_updateOperator ctx.ctx_from params prev_st
      some (next_st, [])
  | some (.wccd_msg_mint receiver) => do
      let _ ← requireTrue (!(Base.address_eqb receiver ctx.ctx_from))
      let next_st := increment_balance prev_st receiver ctx.ctx_amount.toNat
      some (next_st, [])
  | some (.wccd_msg_burn amount) => do
      let next_st ← decrement_balance prev_st ctx.ctx_from amount
      some (next_st, [.act_transfer ctx.ctx_from (Int.ofNat amount)])
  | none => none

def init
    (_chain : Chain) (_ctx : @ContractCallContext Base) (_setup : Unit) :
    Result (@State Base) Error :=
  .Ok FMap.empty

def receive
    (chain : Chain) (ctx : @ContractCallContext Base)
    (prev_st : @State Base) (msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match wccd_receive_option chain ctx prev_st msg with
  | some res => .Ok res
  | none => .Err ()

def contract : @Contract Base Unit Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

def balance_of (addr : Base.Address) (st : @State Base) : TokenAmount :=
  with_default 0 (get_balance_opt addr st)

def operators_of (addr : Base.Address) (st : @State Base) :
    List Base.Address :=
  match AddressMap.find addr st with
  | some data => data.wccd_operators
  | none => []

end WCCD

end ConCert.Examples.CIS1
