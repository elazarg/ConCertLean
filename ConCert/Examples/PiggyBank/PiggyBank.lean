/- Port of examples/piggybank/PiggyBank.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable

namespace ConCert.Examples.PiggyBank

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.SerializableInstances

variable [Base : ChainBase]

inductive PiggyState where
  | Intact
  | Smashed
  deriving DecidableEq

inductive Msg where
  | Insert
  | Smash
  deriving DecidableEq

structure State where
  balance : Amount
  owner : Base.Address
  piggyState : PiggyState

abbrev Setup : Type := Unit
abbrev Error : Type := Nat
abbrev PiggyResult : Type :=
  Result (@State Base × List (@ActionBody Base)) Error

def error_no_msg : Error := 1
def error_not_owner : Error := 2
def error_already_smashed : Error := 3
def error_amount_not_positive : Error := 4
def error_amount_not_zero : Error := 5

/-- Encode `PiggyState` using Rocq `Derive Ser`'s constructor-tag wire shape. -/
private def piggy_state_serialize : PiggyState → SerializedValue
  | .Intact => serialize_constructor0 0
  | .Smashed => serialize_constructor0 1

private def piggy_state_deserialize (v : SerializedValue) : Option PiggyState :=
  match deserialize_constructor0 0 v with
  | some _ => some .Intact
  | none =>
    match deserialize_constructor0 1 v with
    | some _ => some .Smashed
    | none => none

omit Base in
theorem piggy_state_round_trip :
    ∀ (s : PiggyState), piggy_state_deserialize (piggy_state_serialize s) = some s := by
  intro s
  cases s <;> simp [piggy_state_deserialize, piggy_state_serialize,
    deserialize_constructor0_serialize_constructor0]

instance PiggyState_serializable : Serializable PiggyState where
  serialize := piggy_state_serialize
  deserialize := piggy_state_deserialize
  deserialize_serialize := piggy_state_round_trip

/-- Encode `State` using Rocq `Derive Ser`'s constructor-tag wire shape. -/
private def state_serialize (s : @State Base) : SerializedValue :=
  serialize_constructor3 0 s.balance s.owner s.piggyState

private def state_deserialize (v : SerializedValue) : Option (@State Base) :=
  (deserialize_constructor3 0 v : Option (Amount × Base.Address × PiggyState)).map
    (fun p => { balance := p.1, owner := p.2.1, piggyState := p.2.2 })

theorem state_round_trip :
    ∀ (s : @State Base), state_deserialize (state_serialize s) = some s := by
  intro s
  cases s
  simp [state_deserialize, state_serialize, deserialize_serialize_constructor3]

instance State_serializable : Serializable (@State Base) where
  serialize := state_serialize
  deserialize := state_deserialize
  deserialize_serialize := state_round_trip

/-- Encode `Msg` using Rocq `Derive Ser`'s constructor-tag wire shape. -/
private def msg_serialize : Msg → SerializedValue
  | .Insert => serialize_constructor0 0
  | .Smash => serialize_constructor0 1

private def msg_deserialize (v : SerializedValue) : Option Msg :=
  match deserialize_constructor0 0 v with
  | some _ => some .Insert
  | none =>
    match deserialize_constructor0 1 v with
    | some _ => some .Smash
    | none => none

omit Base in
theorem msg_round_trip :
    ∀ (m : Msg), msg_deserialize (msg_serialize m) = some m := by
  intro m
  cases m <;> simp [msg_deserialize, msg_serialize,
    deserialize_constructor0_serialize_constructor0]

instance Msg_serializable : Serializable Msg where
  serialize := msg_serialize
  deserialize := msg_deserialize
  deserialize_serialize := msg_round_trip

def is_smashed (state : @State Base) : Bool :=
  match state.piggyState with
  | .Intact => false
  | .Smashed => true

def insert (state : @State Base) (ctx : @ContractCallContext Base) : PiggyResult :=
  let amount := ctx.ctx_amount
  match throwIf (amount < 0) error_amount_not_positive with
  | .Err err => .Err err
  | .Ok _ =>
    match throwIf (is_smashed state) error_already_smashed with
    | .Err err => .Err err
    | .Ok _ => .Ok ({ state with balance := state.balance + amount }, [])

def smash (state : @State Base) (ctx : @ContractCallContext Base) : PiggyResult :=
  let owner := state.owner
  match throwIf (!(Base.address_eqb ctx.ctx_from owner)) error_not_owner with
  | .Err err => .Err err
  | .Ok _ =>
    match throwIf (is_smashed state) error_already_smashed with
    | .Err err => .Err err
    | .Ok _ =>
      let acts := [ActionBody.act_transfer owner (state.balance + ctx.ctx_amount)]
      .Ok ({ state with balance := 0, piggyState := .Smashed }, acts)

def receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (msg : Option Msg) : PiggyResult :=
  match msg with
  | some .Insert => insert state ctx
  | some .Smash => smash state ctx
  | none => .Err error_no_msg

def init
    (_chain : Chain) (ctx : @ContractCallContext Base) (_setup : Setup) :
    Result (@State Base) Error :=
  .Ok
    { balance := ctx.ctx_amount,
      owner := ctx.ctx_from,
      piggyState := .Intact }

def contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

end ConCert.Examples.PiggyBank
