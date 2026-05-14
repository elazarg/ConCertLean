/- Port of examples/escrow/EscrowCorrect.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.BlockchainBuilder
import ConCert.Execution.BlockchainTheories
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
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.BlockchainTheories
open ConCert.Utils.Extras

variable [Base : ChainBase]

theorem escrow_receive_nonrecursive_acts
    (chain : Chain) (ctx : @ContractCallContext Base)
    (prev_state new_state : @State Base) (msg : Option Msg)
    (new_acts : List (@ActionBody Base)) :
    ctx.ctx_from ≠ ctx.ctx_contract_address →
    (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _).receive
      chain ctx prev_state msg = .Ok (new_state, new_acts) →
    new_acts.Forall (fun act_body =>
      match act_body with
      | .act_transfer to_ _ => Base.address_eqb to_ ctx.ctx_contract_address = false
      | .act_call to_ _ _   => Base.address_eqb to_ ctx.ctx_contract_address = false
      | _ => True) := by
  intro hnot_self hreceive
  unfold Escrow.contract at hreceive
  simp only at hreceive
  unfold Escrow.receive at hreceive
  cases msg with
  | none => simp at hreceive
  | some m =>
      cases m with
      | commit_money =>
          cases hstep : prev_state.next_step with
          | buyer_commit =>
              simp [hstep] at hreceive
              repeat split at hreceive <;> simp_all
          | buyer_confirm => simp [hstep] at hreceive
          | withdrawals => simp [hstep] at hreceive
          | no_next_step => simp [hstep] at hreceive
      | confirm_item_received =>
          cases hstep : prev_state.next_step with
          | buyer_commit => simp [hstep] at hreceive
          | buyer_confirm =>
              simp [hstep] at hreceive
              repeat split at hreceive <;> simp_all
          | withdrawals => simp [hstep] at hreceive
          | no_next_step => simp [hstep] at hreceive
      | withdraw =>
          cases hstep : prev_state.next_step with
          | buyer_commit =>
              simp [hstep] at hreceive
              repeat split at hreceive <;> simp_all
              rcases hreceive with ⟨_, hacts⟩
              subst new_acts
              have hseller_ne : prev_state.seller ≠ ctx.ctx_contract_address := by
                intro hseller
                apply hnot_self
                have hfrom_seller : ctx.ctx_from = prev_state.seller := by
                  exact (Base.address_eqb_spec _ _).mp (by assumption)
                exact hfrom_seller.trans hseller
              simp [Address.address_eq_ne _ _ hseller_ne]
          | buyer_confirm => simp [hstep] at hreceive
          | withdrawals =>
              simp [hstep] at hreceive
              split at hreceive <;> simp_all
              by_cases hbuyer : Base.address_eqb ctx.ctx_from prev_state.buyer = true
              · simp [hbuyer] at hreceive
                repeat split at hreceive <;> simp_all
                rcases hreceive with ⟨_, hacts⟩
                subst new_acts
                simp [Address.address_eq_ne _ _ hnot_self]
              · simp [hbuyer] at hreceive
                by_cases hseller : Base.address_eqb ctx.ctx_from prev_state.seller = true
                · simp [hseller] at hreceive
                  repeat split at hreceive <;> simp_all
                  rcases hreceive with ⟨_, hacts⟩
                  subst new_acts
                  simp [Address.address_eq_ne _ _ hnot_self]
                · simp [hseller] at hreceive
          | no_next_step => simp [hstep] at hreceive

theorem escrow_nonrecursive : NonRecursive (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _) := by
  intro bstate caddr hr hdeployed
  obtain ⟨trace⟩ := hr
  let Q : @ActionBody Base → Prop := fun act_body =>
    match act_body with
    | .act_transfer to_ _ => Base.address_eqb to_ caddr = false
    | .act_call to_ _ _   => Base.address_eqb to_ caddr = false
    | _ => True
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base (@Setup Base) →
      @State Base → Amount → List (@ActionBody Base) →
      List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ caddr _ _ _ out_queue _ _ =>
      out_queue.Forall (fun act_body =>
        match act_body with
        | .act_transfer to_ _ => Base.address_eqb to_ caddr = false
        | .act_call to_ _ _   => Base.address_eqb to_ caddr = false
        | _ => True)
  have hcases : ContractInductionCases
      (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _)
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True) P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
          cases eval with
          | eval_transfer => trivial
          | eval_deploy => trivial
          | eval_call => intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro old_h old_s old_f new_h new_s new_f caddr dep_info state balance
        inc_calls out_txs facts ih _
      exact ih
    · intro chain ctx setup result facts hinit _
      simp [P]
    · intro height slot fin_height caddr dep_info cstate balance out_act out_acts
        inc_calls prev_out_txs tx ih hfrom hamount hmatch _
      have hall : (out_act :: out_acts).Forall (fun act_body =>
          match act_body with
          | .act_transfer to_ _ => Base.address_eqb to_ caddr = false
          | .act_call to_ _ _   => Base.address_eqb to_ caddr = false
          | _ => True) := by
        simpa [P] using ih
      have htail : out_acts.Forall (fun act_body =>
          match act_body with
          | .act_transfer to_ _ => Base.address_eqb to_ caddr = false
          | .act_call to_ _ _   => Base.address_eqb to_ caddr = false
          | _ => True) := by
        rw [List.forall_iff_forall_mem] at hall ⊢
        intro act hmem
        exact hall act (List.mem_cons_of_mem _ hmem)
      simpa [P] using htail
    · intro chain ctx dep_info prev_state msg prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts hnot_self facts ih hreceive _
      have hnew := escrow_receive_nonrecursive_acts
        (Base := Base) chain ctx prev_state new_state msg new_acts hnot_self hreceive
      have hprev : prev_out_queue.Forall (fun act_body =>
          match act_body with
          | .act_transfer to_ _ => Base.address_eqb to_ ctx.ctx_contract_address = false
          | .act_call to_ _ _   => Base.address_eqb to_ ctx.ctx_contract_address = false
          | _ => True) := by
        simpa [P] using ih
      simpa [P] using
        (ConCert.Utils.Extras.Forall_app
          (fun act_body =>
            match act_body with
            | .act_transfer to_ _ => Base.address_eqb to_ ctx.ctx_contract_address = false
            | .act_call to_ _ _   => Base.address_eqb to_ ctx.ctx_contract_address = false
            | _ => True)
          new_acts prev_out_queue).mp ⟨hnew, hprev⟩
    · intro chain ctx dep_info prev_state msg head prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts hself facts ih haction hreceive _
      cases head with
      | act_transfer to_ amount =>
          rcases haction with ⟨hto, hamount, hmsg⟩
          subst to_
          have hall :
              (ActionBody.act_transfer ctx.ctx_contract_address amount :: prev_out_queue).Forall
                (fun act_body =>
                  match act_body with
                  | .act_transfer to_ _ => Base.address_eqb to_ ctx.ctx_contract_address = false
                  | .act_call to_ _ _   => Base.address_eqb to_ ctx.ctx_contract_address = false
                  | _ => True) := by
            simpa [P] using ih
          rw [List.forall_iff_forall_mem] at hall
          have hhead :=
            hall (ActionBody.act_transfer ctx.ctx_contract_address amount) (by simp)
          have hfalse : False := by
            simp [Address.address_eq_refl] at hhead
          cases hfalse
      | act_call to_ amount msg_ser =>
          rcases haction with ⟨hto, hamount, hmsg_ne, hdes⟩
          subst to_
          have hall :
              (ActionBody.act_call ctx.ctx_contract_address amount msg_ser :: prev_out_queue).Forall
                (fun act_body =>
                  match act_body with
                  | .act_transfer to_ _ => Base.address_eqb to_ ctx.ctx_contract_address = false
                  | .act_call to_ _ _   => Base.address_eqb to_ ctx.ctx_contract_address = false
                  | _ => True) := by
            simpa [P] using ih
          rw [List.forall_iff_forall_mem] at hall
          have hhead :=
            hall (ActionBody.act_call ctx.ctx_contract_address amount msg_ser) (by simp)
          have hfalse : False := by
            simp [Address.address_eq_refl] at hhead
          cases hfalse
      | act_deploy amount wc setup =>
          cases haction
    · intro height slot fin_height caddr dep_info cstate balance out_queue
        inc_calls out_txs out_queue' ih hperm _
      exact ConCert.Utils.Extras.forall_respects_permutation _ _ _ hperm ih
  obtain ⟨_, _, _, _, _, _, hP⟩ :=
    contract_induction
      (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _)
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True)
      P hcases bstate caddr trace hdeployed
  simpa [P] using hP

def txs_to (to_ : Base.Address) (txs : List (@Tx Base)) : List (@Tx Base) :=
  txs.filter (fun tx => Base.address_eqb tx.tx_to to_)

theorem txs_to_cons :
  ∀ (addr : Base.Address) (tx : @Tx Base) (txs : List (@Tx Base)),
    txs_to addr (tx :: txs) =
      (if Base.address_eqb tx.tx_to addr then [tx] else []) ++ txs_to addr txs := by
  intros addr tx txs
  by_cases h : Base.address_eqb tx.tx_to addr = true
  · simp [txs_to, h]
  · simp [txs_to, h]

def txs_from (frm : Base.Address) (txs : List (@Tx Base)) : List (@Tx Base) :=
  txs.filter (fun tx => Base.address_eqb tx.tx_from frm)

theorem txs_from_cons :
  ∀ (addr : Base.Address) (tx : @Tx Base) (txs : List (@Tx Base)),
    txs_from addr (tx :: txs) =
      (if Base.address_eqb tx.tx_from addr then [tx] else []) ++ txs_from addr txs := by
  intros addr tx txs
  by_cases h : Base.address_eqb tx.tx_from addr = true
  · simp [txs_from, h]
  · simp [txs_from, h]

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

theorem transfer_acts_to_cons :
  ∀ (addr : Base.Address) (act : @ActionBody Base) (acts : List (@ActionBody Base)),
    transfer_acts_to addr (act :: acts) =
      (if (match act with
           | .act_transfer to_ _ => Base.address_eqb to_ addr
           | _ => false)
       then [act] else []) ++ transfer_acts_to addr acts := by
  intros addr act acts
  cases act with
  | act_transfer to_ amount =>
      by_cases h : Base.address_eqb to_ addr = true
      · simp [transfer_acts_to, h]
      · simp [transfer_acts_to, h]
  | act_deploy amount wc setup =>
      simp [transfer_acts_to]
  | act_call to_ amount msg =>
      simp [transfer_acts_to]

theorem action_all_transfer_perm
    (xs ys : List (@ActionBody Base)) (hperm : xs.Perm ys) :
    xs.all (fun act => match act with | .act_transfer _ _ => true | _ => false) = true →
    ys.all (fun act => match act with | .act_transfer _ _ => true | _ => false) = true := by
  intro hall
  rw [List.all_eq_true] at hall ⊢
  intro act hmem
  exact hall act (hperm.symm.mem_iff.mp hmem)

theorem sum_transfer_acts_to_perm
    (addr : Base.Address) (xs ys : List (@ActionBody Base)) (hperm : xs.Perm ys) :
    sumZ (fun a => act_body_amount a) (transfer_acts_to addr xs) =
      sumZ (fun a => act_body_amount a) (transfer_acts_to addr ys) := by
  unfold transfer_acts_to
  exact sumZ_permutation (hperm.filter (fun a =>
    match a with
    | .act_transfer to_ _ => Base.address_eqb to_ addr
    | _ => false))

/-- Net money paid out by the contract to a particular address
    (outgoing txs + queued transfers). -/
def money_to {bstate_from bstate_to : @ChainState Base}
    (trace : ChainTrace bstate_from bstate_to) (caddr addr : Base.Address) : Amount :=
  sumZ (fun tx => tx.tx_amount) (txs_to addr (outgoing_txs trace caddr)) +
  sumZ (fun a => act_body_amount a)
       (transfer_acts_to addr (outgoing_acts bstate_to caddr))

/-- Strong correctness: case-by-case invariants on `cstate.next_step`. -/
theorem escrow_correct_strong :
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
          money_to trace caddr buyer_addr  = 0)) := by
  intro bstate caddr trace hdeployed
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base (@Setup Base) →
      @State Base → Amount → List (@ActionBody Base) →
      List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ depinfo cstate balance out_acts inc_calls out_txs =>
      let item_worth  := depinfo.deployment_amount / 2
      let seller_addr := depinfo.deployment_from
      let buyer_addr  := depinfo.deployment_setup.setup_buyer
      depinfo.deployment_amount = 2 * item_worth ∧
      item_worth > 0 ∧
      cstate.seller = seller_addr ∧
      cstate.buyer  = buyer_addr ∧
      buyer_addr ≠ seller_addr ∧
      out_acts.all
        (fun act => match act with
                    | .act_transfer _ _ => true
                    | _ => false) = true ∧
      (match cstate.next_step with
       | .buyer_commit =>
         balance = 2 * item_worth ∧
         out_acts = [] ∧
         out_txs = [] ∧
         inc_calls = []
       | .buyer_confirm =>
         balance = 4 * item_worth ∧
         out_acts = [] ∧
         out_txs = [] ∧
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
         sumZ (fun tx => tx.tx_amount) (txs_to seller_addr out_txs) +
           sumZ (fun a => act_body_amount a) (transfer_acts_to seller_addr out_acts) +
           cstate.seller_withdrawable = 3 * item_worth ∧
         sumZ (fun tx => tx.tx_amount) (txs_to buyer_addr out_txs) +
           sumZ (fun a => act_body_amount a) (transfer_acts_to buyer_addr out_acts) +
           cstate.buyer_withdrawable = 1 * item_worth
       | .no_next_step =>
         (buyer_confirmed inc_calls buyer_addr = true ∧
          (∃ origin, inc_calls.filter (fun c => !(c.call_amount == 0)) =
            [{ call_origin := origin, call_from := buyer_addr,
               call_amount := 2 * item_worth,
               call_msg := some Msg.commit_money }]) ∧
          sumZ (fun tx => tx.tx_amount) (txs_to seller_addr out_txs) +
            sumZ (fun a => act_body_amount a) (transfer_acts_to seller_addr out_acts) =
              3 * item_worth ∧
          sumZ (fun tx => tx.tx_amount) (txs_to buyer_addr out_txs) +
            sumZ (fun a => act_body_amount a) (transfer_acts_to buyer_addr out_acts) =
              1 * item_worth) ∨
         ((∃ origin, inc_calls =
            [{ call_origin := origin, call_from := seller_addr,
               call_amount := 0,
               call_msg := some Msg.withdraw }]) ∧
          sumZ (fun tx => tx.tx_amount) (txs_to seller_addr out_txs) +
            sumZ (fun a => act_body_amount a) (transfer_acts_to seller_addr out_acts) =
              2 * item_worth ∧
          sumZ (fun tx => tx.tx_amount) (txs_to buyer_addr out_txs) +
            sumZ (fun a => act_body_amount a) (transfer_acts_to buyer_addr out_acts) =
              0))
  have hcases : NonRecursiveContractInductionCases
      (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _)
      (fun _ _ _ _ _ _ => True)
      (fun _ ctx => ctx.ctx_amount >= 0)
      (fun _ _ _ _ _ => True)
      P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
          cases eval with
          | eval_transfer => trivial
          | eval_deploy _ _ _ _ _ _ _ hnonneg _ _ _ _ _ _ _ => exact hnonneg
          | eval_call => intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · -- Coq: New block; invariant is unchanged.
      intros
      assumption
    · -- Coq: Deployment; unfold `Escrow.init`, split address/amount/evenness.
      intro chain ctx setup result hctx hinit _
      unfold Escrow.contract at hinit
      simp only at hinit
      unfold Escrow.init at hinit
      repeat split at hinit <;> simp_all [P]
      subst result
      have hmod : ctx.ctx_amount % 2 = 0 := by assumption
      have hnot_zero : ¬ctx.ctx_amount = 0 := by assumption
      have haddr : Base.address_eqb setup.setup_buyer ctx.ctx_from = false := by assumption
      have heven : Even ctx.ctx_amount := Int.even_iff.mpr hmod
      have hamount : ctx.ctx_amount = 2 * (ctx.ctx_amount / 2) := by
        simpa [Int.mul_comm] using (Int.two_mul_ediv_two_of_even heven).symm
      have hpositive_amount : 0 < ctx.ctx_amount :=
        lt_of_le_of_ne hctx (Ne.symm hnot_zero)
      have hpositive_item : 0 < ctx.ctx_amount / 2 := by
        nlinarith [hamount, hpositive_amount]
      have hbuyer_seller : setup.setup_buyer ≠ ctx.ctx_from :=
        (Address.address_eq_ne' setup.setup_buyer ctx.ctx_from).mpr haddr
      exact ⟨hamount, hpositive_item, rfl, rfl, hbuyer_seller, hamount⟩
    · -- Coq: Transfer from contract; use `txs_to_cons` and
      -- `transfer_acts_to_cons` plus balance arithmetic.
      intro height slot fin_height caddr dep_info cstate balance out_act out_acts
        inc_calls prev_out_txs tx ih hfrom hamount hmatch _
      dsimp [P] at ih
      dsimp [P]
      rcases ih with ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne, hall, hcase⟩
      cases out_act with
      | act_transfer to_ amount =>
          rcases hmatch with ⟨htx_to, htx_amount, hbody⟩
          simp at hall
          have hall_tail :
              out_acts.all (fun act =>
                match act with
                | .act_transfer _ _ => true
                | _ => false) = true := by
            rw [List.all_eq_true]
            exact hall
          refine ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne, hall_tail, ?_⟩
          cases hstep : cstate.next_step <;> simp [hstep] at hcase ⊢
          · rcases hcase with ⟨hconfirmed, hcommit, hseller_sum, hbuyer_sum⟩
            refine ⟨hconfirmed, hcommit, ?_, ?_⟩
            · by_cases hs : Base.address_eqb to_ dep_info.deployment_from = true
              · simp [txs_to_cons, transfer_acts_to_cons, htx_to, htx_amount,
                  hs, act_body_amount, sumZ] at hseller_sum ⊢
                omega
              · simp [txs_to_cons, transfer_acts_to_cons, htx_to,
                  hs, act_body_amount] at hseller_sum ⊢
                omega
            · by_cases hb : Base.address_eqb to_ dep_info.deployment_setup.setup_buyer = true
              · simp [txs_to_cons, transfer_acts_to_cons, htx_to, htx_amount,
                  hb, act_body_amount, sumZ] at hbuyer_sum ⊢
                omega
              · simp [txs_to_cons, transfer_acts_to_cons, htx_to,
                  hb, act_body_amount] at hbuyer_sum ⊢
                omega
          · rcases hcase with hfinal | hrefund
            · rcases hfinal with ⟨hconfirmed, hcommit, hseller_sum, hbuyer_sum⟩
              left
              refine ⟨hconfirmed, hcommit, ?_, ?_⟩
              · by_cases hs : Base.address_eqb to_ dep_info.deployment_from = true
                · simp [txs_to_cons, transfer_acts_to_cons, htx_to, htx_amount,
                    hs, act_body_amount, sumZ] at hseller_sum ⊢
                  omega
                · simp [txs_to_cons, transfer_acts_to_cons, htx_to,
                    hs, act_body_amount] at hseller_sum ⊢
                  omega
              · by_cases hb : Base.address_eqb to_ dep_info.deployment_setup.setup_buyer = true
                · simp [txs_to_cons, transfer_acts_to_cons, htx_to, htx_amount,
                    hb, act_body_amount, sumZ] at hbuyer_sum ⊢
                  omega
                · simp [txs_to_cons, transfer_acts_to_cons, htx_to,
                    hb, act_body_amount] at hbuyer_sum ⊢
                  omega
            · rcases hrefund with ⟨hwithdraw, hseller_sum, hbuyer_sum⟩
              right
              refine ⟨hwithdraw, ?_, ?_⟩
              · by_cases hs : Base.address_eqb to_ dep_info.deployment_from = true
                · simp [txs_to_cons, transfer_acts_to_cons, htx_to, htx_amount,
                    hs, act_body_amount, sumZ] at hseller_sum ⊢
                  omega
                · simp [txs_to_cons, transfer_acts_to_cons, htx_to,
                    hs, act_body_amount] at hseller_sum ⊢
                  omega
              · by_cases hb : Base.address_eqb to_ dep_info.deployment_setup.setup_buyer = true
                · simp [txs_to_cons, transfer_acts_to_cons, htx_to, htx_amount,
                    hb, act_body_amount, sumZ] at hbuyer_sum ⊢
                  omega
                · simp [txs_to_cons, transfer_acts_to_cons, htx_to,
                    hb, act_body_amount] at hbuyer_sum ⊢
                  omega
      | act_deploy amount wc setup =>
          simp at hall
      | act_call to_ amount msg =>
          simp at hall
    · -- Coq: Nonrecursive call; split `Escrow.receive` by message and
      -- `next_step`.
      intro chain ctx dep_info prev_state msg prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts hnot_self hfacts ih hreceive _
      dsimp [P] at ih
      dsimp [P]
      rcases ih with ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne, hall, hcase⟩
      unfold Escrow.contract at hreceive
      simp only at hreceive
      unfold Escrow.receive at hreceive
      cases msg with
      | none => simp at hreceive
      | some m =>
          cases m with
          | commit_money =>
              cases hstep : prev_state.next_step <;> simp [hstep] at hcase hreceive ⊢
              rcases hcase with ⟨hbal, hqueue, hout, hinc⟩
              unfold subAmountOption at hreceive
              by_cases hsub : ctx.ctx_contract_balance < ctx.ctx_amount
              · rw [if_pos hsub] at hreceive
                cases hreceive
              · rw [if_neg hsub] at hreceive
                cases hb : Base.address_eqb ctx.ctx_from prev_state.buyer
                · simp [hb] at hreceive
                · simp [hb] at hreceive
                  by_cases hproper :
                      ctx.ctx_amount =
                        (ctx.ctx_contract_balance - ctx.ctx_amount) / 2 * 2
                  · rw [if_pos hproper] at hreceive
                    cases hreceive
                    have hfrom :
                        ctx.ctx_from = dep_info.deployment_setup.setup_buyer := by
                      exact ((Base.address_eqb_spec _ _).mp hb).trans hbuyer
                    have hdiv :
                        (2 * (dep_info.deployment_amount / 2)) / 2 * 2 =
                          2 * (dep_info.deployment_amount / 2) := by
                      exact Int.ediv_mul_cancel_of_dvd
                        (by refine ⟨dep_info.deployment_amount / 2, ?_⟩; ring)
                    have hamount :
                        ctx.ctx_amount = 2 * (dep_info.deployment_amount / 2) := by
                      calc
                        ctx.ctx_amount =
                            (ctx.ctx_contract_balance - ctx.ctx_amount) / 2 * 2 :=
                          hproper
                        _ = (2 * (dep_info.deployment_amount / 2)) / 2 * 2 := by
                          rw [hbal]
                        _ = 2 * (dep_info.deployment_amount / 2) := hdiv
                    have hbalance :
                        ctx.ctx_contract_balance =
                          4 * (dep_info.deployment_amount / 2) := by
                      linarith
                    refine
                      ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne,
                        ?_, ?_⟩
                    · simp [hqueue]
                    · exact
                        ⟨hbalance, ⟨rfl, hqueue⟩, hout,
                         ⟨hfrom, hamount⟩, hinc⟩
                  · rw [if_neg hproper] at hreceive
                    cases hreceive
          | confirm_item_received =>
              cases hstep : prev_state.next_step <;> simp [hstep] at hcase hreceive ⊢
              rcases hcase with ⟨hbal, hqueue, hout, hcommit⟩
              cases hb : Base.address_eqb ctx.ctx_from prev_state.buyer
              · simp [hb] at hreceive
              · simp [hb] at hreceive
                by_cases hzero : ctx.ctx_amount = 0
                · rw [if_pos hzero] at hreceive
                  cases hreceive
                  have hfrom :
                      ctx.ctx_from = dep_info.deployment_setup.setup_buyer := by
                    exact ((Base.address_eqb_spec _ _).mp hb).trans hbuyer
                  have hbalance :
                      ctx.ctx_contract_balance =
                        4 * (dep_info.deployment_amount / 2) := by
                    linarith
                  have hquarter :
                      ctx.ctx_contract_balance / 4 =
                        dep_info.deployment_amount / 2 := by
                    rw [hbalance]
                    exact Int.mul_ediv_cancel_left
                      (dep_info.deployment_amount / 2) (by norm_num)
                  rcases hcommit with ⟨origin, hinc_prev⟩
                  have hcommit_nonzero :
                      (2 * (dep_info.deployment_amount / 2) == 0) = false := by
                    simp [show 2 * (dep_info.deployment_amount / 2) ≠ 0 by
                      nlinarith [hitem_pos]]
                  refine
                    ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne,
                      ?_, ?_⟩
                  · simp [hqueue]
                  · refine ⟨?_, ?_, ?_, ?_⟩
                    · simp [buyer_confirmed, hfrom, Address.address_eq_refl]
                    · refine ⟨origin, ?_⟩
                      simp [hzero, hinc_prev, hcommit_nonzero]
                    · simp [hqueue, hout, hquarter, sumZ, txs_to,
                        transfer_acts_to]
                      ring
                    · simp [hqueue, hout, hquarter, sumZ, txs_to,
                        transfer_acts_to]
                · rw [if_neg hzero] at hreceive
                  cases hreceive
          | withdraw =>
              cases hstep : prev_state.next_step <;> simp [hstep] at hcase hreceive ⊢
              · rcases hcase with ⟨hbal, hqueue, hout, hinc⟩
                by_cases hzero : ctx.ctx_amount = 0
                · rw [if_pos hzero] at hreceive
                  by_cases htimeout : prev_state.last_action + 50 < chain.current_slot
                  · rw [if_pos htimeout] at hreceive
                    cases hreceive
                  · rw [if_neg htimeout] at hreceive
                    cases hs : Base.address_eqb ctx.ctx_from prev_state.seller
                    · simp [hs] at hreceive
                    · simp [hs] at hreceive
                      rcases hreceive with ⟨hstate, hacts⟩
                      subst new_state
                      subst new_acts
                      have hfrom : ctx.ctx_from = dep_info.deployment_from := by
                        exact ((Base.address_eqb_spec _ _).mp hs).trans hseller
                      have hbalance :
                          ctx.ctx_contract_balance =
                            2 * (dep_info.deployment_amount / 2) := by
                        linarith
                      have hseller_buyer_ne :
                          prev_state.seller ≠
                            dep_info.deployment_setup.setup_buyer := by
                        intro heq
                        apply haddr_ne
                        rw [← heq]
                        exact hseller
                      refine
                        ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne,
                          ?_, ?_⟩
                      · simp [hqueue]
                      · right
                        refine ⟨⟨⟨hfrom, hzero⟩, hinc⟩, ?_, ?_⟩
                        · simp [hqueue, hout, transfer_acts_to, txs_to, sumZ,
                            act_body_amount, hseller, Address.address_eq_refl,
                            hbalance]
                        · simp [hqueue, hout, transfer_acts_to, txs_to, sumZ,
                            act_body_amount,
                            Address.address_eq_ne _ _ hseller_buyer_ne]
                · rw [if_neg hzero] at hreceive
                  cases hreceive
              · rcases hcase with ⟨hconfirmed, hcommit, hseller_sum, hbuyer_sum⟩
                have hall_mem :
                    ∀ x ∈ prev_out_queue,
                      (match x with
                       | ActionBody.act_transfer _ _ => true
                       | _ => false) = true := by
                  rw [List.all_eq_true] at hall
                  exact hall
                by_cases hzero : ctx.ctx_amount = 0
                · rw [if_pos hzero] at hreceive
                  cases hb : Base.address_eqb ctx.ctx_from prev_state.buyer
                  · simp [hb] at hreceive
                    cases hs : Base.address_eqb ctx.ctx_from prev_state.seller
                    · simp [hs] at hreceive
                    · simp [hs] at hreceive
                      by_cases hpaybad : prev_state.seller_withdrawable ≤ 0
                      · rw [if_pos hpaybad] at hreceive
                        cases hreceive
                      · rw [if_neg hpaybad] at hreceive
                        by_cases hbuyer_done : prev_state.buyer_withdrawable = 0
                        · rw [if_pos hbuyer_done] at hreceive
                          cases hreceive
                          have hfrom :
                              ctx.ctx_from = dep_info.deployment_from := by
                            exact ((Base.address_eqb_spec _ _).mp hs).trans hseller
                          have hseller_ne_buyer :
                              dep_info.deployment_from ≠
                                dep_info.deployment_setup.setup_buyer := by
                            intro h
                            exact haddr_ne h.symm
                          refine
                            ⟨hdep_amount, hitem_pos, hseller, hbuyer,
                              haddr_ne, ?_, ?_⟩
                          · constructor
                            · intro x hx
                              simp at hx
                              rcases hx with rfl
                              simp
                            · exact hall_mem
                          · left
                            refine ⟨?_, ?_, ?_, ?_⟩
                            · simpa [buyer_confirmed, hzero] using hconfirmed
                            · rcases hcommit with ⟨origin, hcommit_eq⟩
                              refine ⟨origin, ?_⟩
                              simp [hzero, hcommit_eq]
                            · simp [transfer_acts_to_cons, hfrom,
                                Address.address_eq_refl, act_body_amount, sumZ]
                                at hseller_sum ⊢
                              linarith
                            · simp [transfer_acts_to_cons, hfrom,
                                Address.address_eq_ne _ _ hseller_ne_buyer,
                                act_body_amount, hbuyer_done]
                                at hbuyer_sum ⊢
                              linarith
                        · rw [if_neg hbuyer_done] at hreceive
                          cases hreceive
                          have hfrom :
                              ctx.ctx_from = dep_info.deployment_from := by
                            exact ((Base.address_eqb_spec _ _).mp hs).trans hseller
                          have hseller_ne_buyer :
                              dep_info.deployment_from ≠
                                dep_info.deployment_setup.setup_buyer := by
                            intro h
                            exact haddr_ne h.symm
                          refine
                            ⟨hdep_amount, hitem_pos, hseller, hbuyer,
                              haddr_ne, ?_, ?_⟩
                          · constructor
                            · intro x hx
                              simp at hx
                              rcases hx with rfl
                              simp
                            · exact hall_mem
                          · refine ⟨?_, ?_, ?_, ?_⟩
                            · simpa [buyer_confirmed, hzero] using hconfirmed
                            · rcases hcommit with ⟨origin, hcommit_eq⟩
                              refine ⟨origin, ?_⟩
                              simp [hzero, hcommit_eq]
                            · simp [transfer_acts_to_cons, hfrom,
                                Address.address_eq_refl, act_body_amount, sumZ]
                                at hseller_sum ⊢
                              linarith
                            · simp [transfer_acts_to_cons, hfrom,
                                Address.address_eq_ne _ _ hseller_ne_buyer,
                                act_body_amount] at hbuyer_sum ⊢
                              linarith
                  · simp [hb] at hreceive
                    by_cases hpaybad : prev_state.buyer_withdrawable ≤ 0
                    · rw [if_pos hpaybad] at hreceive
                      cases hreceive
                    · rw [if_neg hpaybad] at hreceive
                      by_cases hseller_done :
                          prev_state.seller_withdrawable = 0
                      · rw [if_pos hseller_done] at hreceive
                        cases hreceive
                        have hfrom :
                            ctx.ctx_from =
                              dep_info.deployment_setup.setup_buyer := by
                          exact ((Base.address_eqb_spec _ _).mp hb).trans hbuyer
                        refine
                          ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne,
                            ?_, ?_⟩
                        · constructor
                          · intro x hx
                            simp at hx
                            rcases hx with rfl
                            simp
                          · exact hall_mem
                        · left
                          refine ⟨?_, ?_, ?_, ?_⟩
                          · simpa [buyer_confirmed, hzero] using hconfirmed
                          · rcases hcommit with ⟨origin, hcommit_eq⟩
                            refine ⟨origin, ?_⟩
                            simp [hzero, hcommit_eq]
                          · simp [transfer_acts_to_cons, hfrom,
                              Address.address_eq_ne _ _ haddr_ne,
                              act_body_amount, hseller_done]
                              at hseller_sum ⊢
                            linarith
                          · simp [transfer_acts_to_cons, hfrom,
                              Address.address_eq_refl, act_body_amount, sumZ]
                              at hbuyer_sum ⊢
                            linarith
                      · rw [if_neg hseller_done] at hreceive
                        cases hreceive
                        have hfrom :
                            ctx.ctx_from =
                              dep_info.deployment_setup.setup_buyer := by
                          exact ((Base.address_eqb_spec _ _).mp hb).trans hbuyer
                        refine
                          ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne,
                            ?_, ?_⟩
                        · constructor
                          · intro x hx
                            simp at hx
                            rcases hx with rfl
                            simp
                          · exact hall_mem
                        · refine ⟨?_, ?_, ?_, ?_⟩
                          · simpa [buyer_confirmed, hzero] using hconfirmed
                          · rcases hcommit with ⟨origin, hcommit_eq⟩
                            refine ⟨origin, ?_⟩
                            simp [hzero, hcommit_eq]
                          · simp [transfer_acts_to_cons, hfrom,
                              Address.address_eq_ne _ _ haddr_ne] at hseller_sum ⊢
                            linarith
                          · simp [transfer_acts_to_cons, hfrom,
                              Address.address_eq_refl, act_body_amount, sumZ]
                              at hbuyer_sum ⊢
                            linarith
                · rw [if_neg hzero] at hreceive
                  cases hreceive
    · -- Coq: Permuting queue; transfer-only and money sums are permutation
      -- invariant.
      intro height slot fin_height caddr dep_info cstate balance out_queue
        inc_calls out_txs out_queue' ih hperm _
      dsimp [P] at ih ⊢
      rcases ih with ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne, hall, hcase⟩
      refine
        ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne,
         action_all_transfer_perm out_queue out_queue' hperm hall, ?_⟩
      cases hstep : cstate.next_step <;> simp [hstep] at hcase ⊢
      · rcases hcase with ⟨hbal, hqueue, hout, hinc⟩
        have hqueue' : out_queue' = [] := by
          rw [hqueue] at hperm
          exact (List.nil_perm.mp hperm)
        exact ⟨hbal, hqueue', hout, hinc⟩
      · rcases hcase with ⟨hbal, hqueue, hout, hinc⟩
        have hqueue' : out_queue' = [] := by
          rw [hqueue] at hperm
          exact (List.nil_perm.mp hperm)
        exact ⟨hbal, hqueue', hout, hinc⟩
      · rcases hcase with ⟨hconfirmed, hcommit, hseller_sum, hbuyer_sum⟩
        have hseller_perm :=
          sum_transfer_acts_to_perm dep_info.deployment_from out_queue out_queue' hperm
        have hbuyer_perm :=
          sum_transfer_acts_to_perm dep_info.deployment_setup.setup_buyer
            out_queue out_queue' hperm
        refine ⟨hconfirmed, hcommit, ?_, ?_⟩
        · rw [← hseller_perm]
          exact hseller_sum
        · rw [← hbuyer_perm]
          exact hbuyer_sum
      · rcases hcase with hfinal | hrefund
        · rcases hfinal with ⟨hconfirmed, hcommit, hseller_sum, hbuyer_sum⟩
          have hseller_perm :=
            sum_transfer_acts_to_perm dep_info.deployment_from out_queue out_queue' hperm
          have hbuyer_perm :=
            sum_transfer_acts_to_perm dep_info.deployment_setup.setup_buyer
              out_queue out_queue' hperm
          left
          refine ⟨hconfirmed, hcommit, ?_, ?_⟩
          · rw [← hseller_perm]
            exact hseller_sum
          · rw [← hbuyer_perm]
            exact hbuyer_sum
        · rcases hrefund with ⟨hwithdraw, hseller_sum, hbuyer_sum⟩
          have hseller_perm :=
            sum_transfer_acts_to_perm dep_info.deployment_from out_queue out_queue' hperm
          have hbuyer_perm :=
            sum_transfer_acts_to_perm dep_info.deployment_setup.setup_buyer
              out_queue out_queue' hperm
          right
          refine ⟨hwithdraw, ?_, ?_⟩
          · rw [← hseller_perm]
            exact hseller_sum
          · rw [← hbuyer_perm]
            exact hbuyer_sum
  obtain ⟨depinfo, cstate, inc_calls, hdep, hstate, hcalls, hP⟩ :=
    nonrecursive_contract_induction
      (Escrow.contract : @Contract Base _ _ _ _ _ _ _ _)
      (fun _ _ _ _ _ _ => True)
      (fun _ ctx => ctx.ctx_amount >= 0)
      (fun _ _ _ _ _ => True)
      P
      escrow_nonrecursive hcases bstate caddr trace hdeployed
  exact ⟨cstate, depinfo, inc_calls, hdep, hstate, hcalls, hP⟩

def is_escrow_finished (cstate : @State Base) : Bool :=
  match cstate.next_step with
  | .no_next_step => true
  | _ => false

def net_balance_effect {frm to_ : @ChainState Base}
    (trace : ChainTrace frm to_) (caddr addr : Base.Address) : Amount :=
  sumZ (fun tx => tx.tx_amount) (txs_to addr (outgoing_txs trace caddr))
  - sumZ (fun tx => tx.tx_amount) (txs_from addr (incoming_txs trace caddr))

private theorem sum_txs_from_triples
    (addr : Base.Address) (txs : List (@Tx Base)) :
    sumZ (fun tx => tx.tx_amount) (txs_from addr txs) =
      sumZ (fun t : Base.Address × Base.Address × Amount => t.2.2)
        ((txs.map (fun tx => (tx.tx_from, tx.tx_to, tx.tx_amount))).filter
          (fun t => Base.address_eqb t.1 addr)) := by
  induction txs with
  | nil => simp [txs_from, sumZ]
  | cons tx txs ih =>
      rw [txs_from_cons]
      by_cases h : Base.address_eqb tx.tx_from addr = true
      · simp [h, sumZ]
        rw [ih]
      · simpa [h] using ih

private theorem sum_call_triples_filter
    (addr caddr : Base.Address) (calls : List (@ContractCallInfo Base Msg)) :
    sumZ (fun t : Base.Address × Base.Address × Amount => t.2.2)
        ((calls.map (fun call => (call.call_from, caddr, call.call_amount))).filter
          (fun t => Base.address_eqb t.1 addr)) =
      sumZ (fun call => call.call_amount)
        (calls.filter (fun call => Base.address_eqb call.call_from addr)) := by
  induction calls with
  | nil => simp [sumZ]
  | cons call calls ih =>
      by_cases h : Base.address_eqb call.call_from addr = true
      · simp [h, sumZ]
        rw [ih]
      · simpa [h] using ih

private theorem sum_incoming_txs_from_eq
    {bstate : @ChainState Base} (trace : ChainTrace empty_state bstate)
    (caddr addr : Base.Address)
    (depinfo : @DeploymentInfo Base (@Setup Base))
    (inc_calls : List (@ContractCallInfo Base Msg))
    (hdep : deployment_info (@Setup Base) trace caddr = some depinfo)
    (hcalls : incoming_calls Msg trace caddr = some inc_calls) :
    sumZ (fun tx => tx.tx_amount) (txs_from addr (incoming_txs trace caddr)) =
      sumZ (fun call => call.call_amount)
          (inc_calls.filter (fun call => Base.address_eqb call.call_from addr)) +
        (if Base.address_eqb depinfo.deployment_from addr
         then depinfo.deployment_amount else 0) := by
  rw [sum_txs_from_triples]
  rw [incoming_txs_contract caddr bstate trace (@Setup Base) depinfo Msg inc_calls
    hdep hcalls]
  rw [List.filter_append, sumZ_app]
  rw [sum_call_triples_filter]
  by_cases hfrom : Base.address_eqb depinfo.deployment_from addr = true
  · simp [hfrom, sumZ]
  · simp [hfrom, sumZ]

private theorem sum_filter_ignore_zero_calls
    (xs : List (@ContractCallInfo Base Msg))
    (p : @ContractCallInfo Base Msg → Bool) :
    sumZ (fun c => c.call_amount) (xs.filter p) =
      sumZ (fun c => c.call_amount)
        ((xs.filter (fun c => !(c.call_amount == 0))).filter p) := by
  induction xs with
  | nil => simp [sumZ]
  | cons x xs ih =>
      by_cases hzero : x.call_amount = 0
      · cases hp : p x <;> simp [List.filter, hp, hzero, sumZ, ih]
      · have hnonzero : (x.call_amount == 0) = false := by
          simp [hzero]
        cases hp : p x <;> simp [List.filter, hp, hnonzero, sumZ, ih]

/-- Functional correctness in the `ChainBuilderType` corollary shape. -/
theorem escrow_correct :
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
            net_balance_effect trace caddr buyer  = 0)) := by
  intro Cb prev new header acts hadd
  dsimp
  intro caddr hdeployed
  let trace := Cb.builder_trace new
  let bstate : @ChainState Base :=
    { toEnvironment := Cb.builder_env new, chain_state_queue := [] }
  have hstrong := escrow_correct_strong bstate caddr trace hdeployed
  obtain ⟨cstate, depinfo, inc_calls, hdep, hstate, hcalls, hcases⟩ := hstrong
  refine ⟨depinfo, cstate, inc_calls, hdep, hstate, hcalls, ?_⟩
  intro hfinished
  unfold is_escrow_finished at hfinished
  rcases hcases with
    ⟨hdep_amount, hitem_pos, hseller, hbuyer, haddr_ne, hall, hcase⟩
  cases hstep : cstate.next_step <;>
    simp [hstep, bstate, outgoing_acts, money_to, transfer_acts_to, sumZ]
      at hfinished hcase
  rcases hcase with hfinal | hrefund
  · rcases hfinal with ⟨hconfirmed, hcommit, hseller_out, hbuyer_out⟩
    rcases hcommit with ⟨origin, hcommit_eq⟩
    have hseller_in :
        sumZ (fun tx => tx.tx_amount)
            (txs_from depinfo.deployment_from (incoming_txs trace caddr)) =
          2 * (depinfo.deployment_amount / 2) := by
      rw [sum_incoming_txs_from_eq trace caddr depinfo.deployment_from
        depinfo inc_calls hdep hcalls]
      rw [sum_filter_ignore_zero_calls]
      rw [hcommit_eq]
      simp [Address.address_eq_ne _ _ haddr_ne, Address.address_eq_refl, sumZ]
      exact hdep_amount
    have hbuyer_in :
        sumZ (fun tx => tx.tx_amount)
            (txs_from depinfo.deployment_setup.setup_buyer
              (incoming_txs trace caddr)) =
          2 * (depinfo.deployment_amount / 2) := by
      rw [sum_incoming_txs_from_eq trace caddr
        depinfo.deployment_setup.setup_buyer depinfo inc_calls hdep hcalls]
      rw [sum_filter_ignore_zero_calls]
      rw [hcommit_eq]
      simp [Address.address_eq_refl, Address.address_eq_ne _ _ haddr_ne.symm,
        sumZ]
    left
    refine ⟨hconfirmed, ?_, ?_⟩
    · change
        net_balance_effect trace caddr depinfo.deployment_from =
          depinfo.deployment_amount / 2
      unfold net_balance_effect
      rw [hseller_out, hseller_in]
      linarith
    · change
        net_balance_effect trace caddr depinfo.deployment_setup.setup_buyer =
          -(depinfo.deployment_amount / 2)
      unfold net_balance_effect
      rw [hbuyer_out, hbuyer_in]
      linarith
  · rcases hrefund with ⟨hwithdraw, hseller_out, hbuyer_out⟩
    rcases hwithdraw with ⟨origin, hwithdraw_eq⟩
    have hseller_in :
        sumZ (fun tx => tx.tx_amount)
            (txs_from depinfo.deployment_from (incoming_txs trace caddr)) =
          2 * (depinfo.deployment_amount / 2) := by
      rw [sum_incoming_txs_from_eq trace caddr depinfo.deployment_from
        depinfo inc_calls hdep hcalls]
      rw [hwithdraw_eq]
      simp [Address.address_eq_refl, sumZ]
      exact hdep_amount
    have hbuyer_in :
        sumZ (fun tx => tx.tx_amount)
            (txs_from depinfo.deployment_setup.setup_buyer
              (incoming_txs trace caddr)) =
          0 := by
      rw [sum_incoming_txs_from_eq trace caddr
        depinfo.deployment_setup.setup_buyer depinfo inc_calls hdep hcalls]
      rw [hwithdraw_eq]
      simp [Address.address_eq_ne _ _ haddr_ne.symm, sumZ]
    right
    refine ⟨?_, ?_, ?_⟩
    · simp [buyer_confirmed, hwithdraw_eq,
        Address.address_eq_ne _ _ haddr_ne.symm]
    · change net_balance_effect trace caddr depinfo.deployment_from = 0
      unfold net_balance_effect
      rw [hseller_out, hseller_in]
      linarith
    · change
        net_balance_effect trace caddr depinfo.deployment_setup.setup_buyer = 0
      unfold net_balance_effect
      rw [hbuyer_out, hbuyer_in]
      rfl

end ConCert.Examples.Escrow.EscrowCorrectness
