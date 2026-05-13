/- Port of examples/escrow/EscrowCorrect.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.BlockchainBuilder
import ConCert.Execution.ResultMonad
import ConCert.Execution.ContractCommon
import ConCert.Execution.ContractProperties
import ConCert.Examples.Escrow.Escrow
import ConCert.Utils.Automation
import ConCert.Utils.Extras

namespace ConCert.Examples.Escrow.EscrowCorrectness

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainBuilder
open ConCert.Execution.SerializableBase
open ConCert.Execution.ResultMonad
open ConCert.Examples.Escrow
open ConCert.Execution.ContractProperties
open ConCert.Utils.Extras

variable [Base : ChainBase]

axiom escrow_nonrecursive : NonRecursive (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _)

def txs_to (to_ : Base.Address) (txs : List (@Tx Base)) : List (@Tx Base) :=
  txs.filter (fun tx => Base.address_eqb tx.tx_to to_)

axiom txs_to_cons :
  ∀ (addr : Base.Address) (tx : @Tx Base) (txs : List (@Tx Base)),
    txs_to addr (tx :: txs) =
      (if Base.address_eqb tx.tx_to addr then [tx] else []) ++ txs_to addr txs

def txs_from (frm : Base.Address) (txs : List (@Tx Base)) : List (@Tx Base) :=
  txs.filter (fun tx => Base.address_eqb tx.tx_from frm)

axiom txs_from_cons :
  ∀ (addr : Base.Address) (tx : @Tx Base) (txs : List (@Tx Base)),
    txs_from addr (tx :: txs) =
      (if Base.address_eqb tx.tx_from addr then [tx] else []) ++ txs_from addr txs

def buyer_confirmed
    (inc_calls : List (@ContractCallInfo Base Msg)) (buyer : Base.Address) : Bool :=
  inc_calls.any (fun call =>
    Base.address_eqb call.call_from buyer &&
    (match call.call_msg with
     | some Msg.confirm_item_received => true
     | _ => false))

def transfer_acts_to
    (addr : Base.Address) (acts : List (@ActionBody Base)) : List (@ActionBody Base) :=
  acts.filter (fun a =>
    match a with
    | .act_transfer to_ _ => Base.address_eqb to_ addr
    | _ => false)

axiom transfer_acts_to_cons :
  ∀ (addr : Base.Address) (act : @ActionBody Base) (acts : List (@ActionBody Base)),
    transfer_acts_to addr (act :: acts) =
      (if (match act with
           | .act_transfer to_ _ => Base.address_eqb to_ addr
           | _ => false)
       then [act] else []) ++ transfer_acts_to addr acts

/-- Net money paid out by the contract to a particular address
    (outgoing txs + queued transfers). -/
def money_to {bstate_from bstate_to : @ChainState Base}
    (trace : ChainTrace bstate_from bstate_to) (caddr addr : Base.Address) : Amount :=
  sumZ (fun tx => tx.tx_amount) (txs_to addr (outgoing_txs trace caddr)) +
  sumZ (fun a => act_body_amount a)
       (transfer_acts_to addr (outgoing_acts bstate_to caddr))

/-- Strong correctness: case-by-case invariants on `cstate.next_step`. -/
axiom escrow_correct_strong :
  ∀ (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate),
    bstate.env_contracts caddr =
      some (contract_to_weak_contract (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _)) →
    ∃ (cstate : @State Base) (depinfo : @DeploymentInfo Base (@Setup Base))
      (inc_calls : List (@ContractCallInfo Base Msg)),
      deployment_info (@Setup Base) trace caddr = some depinfo ∧
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr = some cstate ∧
      incoming_calls Msg trace caddr = some inc_calls ∧
      let item_worth  := depinfo.deployment_amount / 2
      let seller_addr := depinfo.deployment_from
      let buyer_addr  := depinfo.deployment_setup.setup_buyer
      depinfo.deployment_amount = 2 * item_worth ∧
      item_worth > 0 ∧
      cstate.seller = seller_addr ∧
      cstate.buyer  = buyer_addr ∧
      buyer_addr ≠ seller_addr ∧
      (outgoing_acts bstate caddr).all
        (fun act => match act with
                    | .act_transfer _ _ => true
                    | _ => false) = true ∧
      (match cstate.next_step with
       | .buyer_commit =>
         bstate.env_account_balances caddr = 2 * item_worth ∧
         outgoing_acts bstate caddr = [] ∧
         outgoing_txs trace caddr = [] ∧
         inc_calls = []
       | .buyer_confirm =>
         bstate.env_account_balances caddr = 4 * item_worth ∧
         outgoing_acts bstate caddr = [] ∧
         outgoing_txs trace caddr = [] ∧
         ∃ origin, inc_calls =
           [{ call_origin := origin, call_from := buyer_addr,
              call_amount := 2 * item_worth,
              call_msg := some Msg.commit_money }]
       | .withdrawals =>
         buyer_confirmed inc_calls buyer_addr = true ∧
         (∃ origin, inc_calls.filter (fun c => !(c.call_amount == 0)) =
           [{ call_origin := origin, call_from := buyer_addr,
              call_amount := 2 * item_worth,
              call_msg := some Msg.commit_money }]) ∧
         money_to trace caddr seller_addr + cstate.seller_withdrawable = 3 * item_worth ∧
         money_to trace caddr buyer_addr  + cstate.buyer_withdrawable  = 1 * item_worth
       | .no_next_step =>
         (buyer_confirmed inc_calls buyer_addr = true ∧
          (∃ origin, inc_calls.filter (fun c => !(c.call_amount == 0)) =
            [{ call_origin := origin, call_from := buyer_addr,
               call_amount := 2 * item_worth,
               call_msg := some Msg.commit_money }]) ∧
          money_to trace caddr seller_addr = 3 * item_worth ∧
          money_to trace caddr buyer_addr  = 1 * item_worth) ∨
         ((∃ origin, inc_calls =
            [{ call_origin := origin, call_from := seller_addr,
               call_amount := 0,
               call_msg := some Msg.withdraw }]) ∧
          money_to trace caddr seller_addr = 2 * item_worth ∧
          money_to trace caddr buyer_addr  = 0))

def is_escrow_finished (cstate : @State Base) : Bool :=
  match cstate.next_step with
  | .no_next_step => true
  | _ => false

def net_balance_effect {frm to_ : @ChainState Base}
    (trace : ChainTrace frm to_) (caddr addr : Base.Address) : Amount :=
  sumZ (fun tx => tx.tx_amount) (txs_to addr (outgoing_txs trace caddr))
  - sumZ (fun tx => tx.tx_amount) (txs_from addr (incoming_txs trace caddr))

/-- Functional correctness in the `ChainBuilderType` corollary shape. -/
axiom escrow_correct :
  ∀ {Cb : @ChainBuilderType Base} (prev new : Cb.builder_type)
    (header : @BlockHeader Base) (acts : List (@Action Base)),
    Cb.builder_add_block prev header acts = .Ok new →
    let trace := Cb.builder_trace new
    ∀ (caddr : Base.Address),
      (Cb.builder_env new).env_contracts caddr =
        some (contract_to_weak_contract (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _)) →
      ∃ (depinfo : @DeploymentInfo Base (@Setup Base)) (cstate : @State Base)
        (inc_calls : List (@ContractCallInfo Base Msg)),
        deployment_info (@Setup Base) trace caddr = some depinfo ∧
        @contract_state Base (@State Base) _ (Cb.builder_env new) caddr = some cstate ∧
        incoming_calls Msg trace caddr = some inc_calls ∧
        let item_worth := depinfo.deployment_amount / 2
        let seller     := depinfo.deployment_from
        let buyer      := depinfo.deployment_setup.setup_buyer
        is_escrow_finished cstate = true →
          ((buyer_confirmed inc_calls buyer = true ∧
            net_balance_effect trace caddr seller = item_worth ∧
            net_balance_effect trace caddr buyer  = -item_worth) ∨
           (buyer_confirmed inc_calls buyer = false ∧
            net_balance_effect trace caddr seller = 0 ∧
            net_balance_effect trace caddr buyer  = 0))

end ConCert.Examples.Escrow.EscrowCorrectness
