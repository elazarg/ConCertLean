/- Shallow executable counterpart of examples/crowdfunding/Crowdfunding.v.

The Rocq example defines this contract through the removed MetaRocq/deep
embedding stack. This module keeps the same state, messages, and transition
behavior as executable Lean code over ConCert's normal execution layer. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Utils.Extras

namespace ConCert.Examples.Crowdfunding

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

structure State where
  balance : Amount
  donations : FMap Base.Address Amount
  owner : Base.Address
  deadline : Nat
  done : Bool
  goal : Amount
  deriving Serializable

inductive Msg where
  | Donate
  | GetFunds
  | Claim
  deriving Serializable

structure Setup where
  deadline : Nat
  goal : Amount
  deriving Serializable

abbrev Error : Type := Unit

def init (_chain : Chain) (ctx : @ContractCallContext Base) (setup : @Setup) :
    Result (@State Base) Error :=
  .Ok
    { balance := 0,
      donations := FMap.empty,
      owner := ctx.ctx_from,
      deadline := setup.deadline,
      done := false,
      goal := setup.goal }

def add_donation (sender : Base.Address) (amount : Amount)
    (donations : FMap Base.Address Amount) : FMap Base.Address Amount :=
  let previous := (FMap.find sender donations).getD 0
  FMap.add sender (previous + amount) donations

def receive
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let now := chain.current_slot
  let tx_amount := ctx.ctx_amount
  let sender := ctx.ctx_from
  match maybe_msg with
  | some .GetFunds =>
      if Base.address_eqb state.owner sender &&
          state.deadline < now &&
          state.goal ≤ state.balance then
        .Ok
          ({ state with balance := 0, done := true },
            [.act_transfer sender state.balance])
      else
        .Err ()
  | some .Donate =>
      if now ≤ state.deadline then
        let new_donations := add_donation sender tx_amount state.donations
        .Ok
          ({ state with
              balance := tx_amount + state.balance,
              donations := new_donations },
            [])
      else
        .Err ()
  | some .Claim =>
      if state.deadline < now && state.balance < state.goal && !state.done then
        match FMap.find sender state.donations with
        | some v =>
            .Ok
              ({ state with
                  balance := state.balance - v,
                  donations := FMap.add sender 0 state.donations },
                [.act_transfer sender v])
        | none => .Err ()
      else
        .Err ()
  | none => .Err ()

def contract : @Contract Base (@Setup) Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

def donation_of (addr : Base.Address) (state : @State Base) : Amount :=
  (FMap.find addr state.donations).getD 0

def sum_donations (state : @State Base) : Amount :=
  ((FMap.elements state.donations).map (fun p : Base.Address × Amount => p.2)).sum

end ConCert.Examples.Crowdfunding
