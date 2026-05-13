/- Port of examples/escrow/Escrow.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Utils.RecordUpdate

namespace ConCert.Examples.Escrow

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.ResultMonad

variable [Base : ChainBase]

structure Setup where
  setup_buyer : Base.Address

inductive NextStep where
  | buyer_commit
  | buyer_confirm
  | withdrawals
  | no_next_step
  deriving DecidableEq

structure State where
  last_action         : Nat
  next_step           : NextStep
  seller              : Base.Address
  buyer               : Base.Address
  seller_withdrawable : Amount
  buyer_withdrawable  : Amount

abbrev Error : Type := Nat
def default_error : Error := 1

inductive Msg where
  | commit_money
  | confirm_item_received
  | withdraw

/-- Setup encodes as a single Address. -/
private def setup_serialize (s : @Setup Base) : SerializedValue := serialize s.setup_buyer
private def setup_deserialize (v : SerializedValue) : Option (@Setup Base) :=
  (deserialize v : Option Base.Address).map (fun a => { setup_buyer := a })
axiom setup_round_trip :
  ∀ (s : @Setup Base), setup_deserialize (setup_serialize s) = some s

instance Setup_serializable : Serializable (@Setup Base) where
  serialize := setup_serialize
  deserialize := setup_deserialize
  deserialize_serialize := setup_round_trip

/-- NextStep encodes as a tag in {0,1,2,3}. -/
private def nextstep_serialize : NextStep → SerializedValue
  | .buyer_commit  => serialize (0 : Nat)
  | .buyer_confirm => serialize (1 : Nat)
  | .withdrawals   => serialize (2 : Nat)
  | .no_next_step  => serialize (3 : Nat)
private def nextstep_deserialize (v : SerializedValue) : Option NextStep :=
  (deserialize v : Option Nat) >>= fun n =>
    match n with
    | 0 => some .buyer_commit
    | 1 => some .buyer_confirm
    | 2 => some .withdrawals
    | 3 => some .no_next_step
    | _ => none
axiom nextstep_round_trip :
  ∀ (s : NextStep), nextstep_deserialize (nextstep_serialize s) = some s

instance NextStep_serializable : Serializable NextStep where
  serialize := nextstep_serialize
  deserialize := nextstep_deserialize
  deserialize_serialize := nextstep_round_trip

/-- State encodes as a 6-tuple. -/
private def state_serialize (s : @State Base) : SerializedValue :=
  serialize (((s.last_action, s.next_step), (s.seller, s.buyer)),
             (s.seller_withdrawable, s.buyer_withdrawable))

private def state_deserialize (v : SerializedValue) : Option (@State Base) :=
  (deserialize v :
      Option (((Nat × NextStep) × (Base.Address × Base.Address)) × (Amount × Amount))).map
    (fun p =>
      { last_action := p.1.1.1, next_step := p.1.1.2,
        seller := p.1.2.1, buyer := p.1.2.2,
        seller_withdrawable := p.2.1, buyer_withdrawable := p.2.2 })

axiom state_round_trip :
  ∀ (s : @State Base), state_deserialize (state_serialize s) = some s

instance State_serializable : Serializable (@State Base) where
  serialize := state_serialize
  deserialize := state_deserialize
  deserialize_serialize := state_round_trip

/-- Msg encodes as a tag in {0,1,2}. -/
private def msg_serialize : Msg → SerializedValue
  | .commit_money          => serialize (0 : Nat)
  | .confirm_item_received => serialize (1 : Nat)
  | .withdraw              => serialize (2 : Nat)
private def msg_deserialize (v : SerializedValue) : Option Msg :=
  (deserialize v : Option Nat) >>= fun n =>
    match n with
    | 0 => some .commit_money
    | 1 => some .confirm_item_received
    | 2 => some .withdraw
    | _ => none
axiom msg_round_trip :
  ∀ (m : Msg), msg_deserialize (msg_serialize m) = some m

instance Msg_serializable : Serializable Msg where
  serialize := msg_serialize
  deserialize := msg_deserialize
  deserialize_serialize := msg_round_trip

def init (chain : Chain) (ctx : @ContractCallContext Base) (setup : @Setup Base)
    : Result (@State Base) Error :=
  let seller := ctx.ctx_from
  let buyer  := setup.setup_buyer
  if Base.address_eqb buyer seller then .Err default_error
  else if ctx.ctx_amount == 0 then .Err default_error
  else if !(ctx.ctx_amount % 2 == 0) then .Err default_error
  else
    .Ok
      { last_action         := chain.current_slot
        next_step           := NextStep.buyer_commit
        seller              := seller
        buyer               := buyer
        seller_withdrawable := 0
        buyer_withdrawable  := 0 }

def subAmountOption (n m : Amount) : Option Amount :=
  if n < m then none else some (n - m)

def receive (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (msg : Option Msg)
    : Result (@State Base × List (@ActionBody Base)) Error :=
  match msg, state.next_step with
  | some Msg.commit_money, NextStep.buyer_commit =>
    match subAmountOption ctx.ctx_contract_balance ctx.ctx_amount with
    | none => .Err default_error
    | some diff_ =>
      let item_price := diff_ / 2
      let expected   := item_price * 2
      if !Base.address_eqb ctx.ctx_from state.buyer then .Err default_error
      else if ctx.ctx_amount != expected then .Err default_error
      else
        .Ok
          ({ state with next_step := NextStep.buyer_confirm
                        last_action := chain.current_slot }, [])

  | some Msg.confirm_item_received, NextStep.buyer_confirm =>
    let item_price := ctx.ctx_contract_balance / 4
    if !Base.address_eqb ctx.ctx_from state.buyer then .Err default_error
    else if ctx.ctx_amount != 0 then .Err default_error
    else
      .Ok
        ({ state with next_step := NextStep.withdrawals
                      buyer_withdrawable  := item_price
                      seller_withdrawable := item_price * 3 }, [])

  | some Msg.withdraw, NextStep.withdrawals =>
    if ctx.ctx_amount != 0 then .Err default_error
    else
      let frm := ctx.ctx_from
      let to_pay_st : Result (Amount × @State Base) Error :=
        if Base.address_eqb frm state.buyer then
          .Ok (state.buyer_withdrawable, { state with buyer_withdrawable := 0 })
        else if Base.address_eqb frm state.seller then
          .Ok (state.seller_withdrawable, { state with seller_withdrawable := 0 })
        else
          .Err default_error
      match to_pay_st with
      | .Err e => .Err e
      | .Ok (to_pay, new_state) =>
        if !(0 < to_pay) then .Err default_error
        else
          let new_state :=
            if new_state.buyer_withdrawable == 0 ∧ new_state.seller_withdrawable == 0
            then { new_state with next_step := NextStep.no_next_step }
            else new_state
          .Ok (new_state, [ActionBody.act_transfer ctx.ctx_from to_pay])

  | some Msg.withdraw, NextStep.buyer_commit =>
    if ctx.ctx_amount != 0 then .Err default_error
    else if !(state.last_action + 50 ≥ chain.current_slot) then .Err default_error
    else if !Base.address_eqb ctx.ctx_from state.seller then .Err default_error
    else
      let balance := ctx.ctx_contract_balance
      .Ok
        ({ state with next_step := NextStep.no_next_step },
         [ActionBody.act_transfer state.seller balance])

  | _, _ => .Err default_error

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

end ConCert.Examples.Escrow
