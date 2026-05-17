/- Port of execution/theories/BlockchainBFS.v.

   Note: the Coq file is named `BlockchainBFS.v` but its `Section DepthFirst`
   defines DFS-related predicates (`NoPermutations`, `NoPermutations'`,
   `NoPermutations''`, `DFSChainTrace`). BFS-related predicates live in the
   sibling `BlockchainDFS.v` (similar misnomer). This module mirrors the Coq
   layout. -/

import ConCert.Execution.BlockchainBase
import ConCert.Execution.BlockchainTheories
import ConCert.Execution.BlockchainInduction
import ConCert.Execution.ChainedList
import ConCert.Execution.ResultMonad
import ConCert.Execution.SerializableBase
import ConCert.Utils.Extras

namespace ConCert.Execution.BlockchainBFS

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.SerializableBase
open ConCert.Execution.ChainedList

variable [Base : ChainBase]

/-- A trace contains no permutation step. Defined as a `Fixpoint`-style
    structural recursion: every `step_permute` makes the property `False`. -/
def NoPermutations : ∀ {frm to_ : @ChainState Base}, ChainTrace frm to_ → Prop
  | _, _, .clnil      => True
  | _, _, .snoc xs s  =>
    match s with
    | .step_permute _ _ => False
    | _ => NoPermutations xs

/-- Identical to `NoPermutations`; the Coq source ships both forms. -/
abbrev NoPermutations' := @NoPermutations

inductive StepNotPermute :
    ∀ {frm to_ : @ChainState Base}, ChainStep frm to_ → Prop
  | snp_block : ∀ {frm to_ : @ChainState Base}
                  (h : @BlockHeader Base)
                  (h1 : frm.chain_state_queue = [])
                  (h2 : IsValidNextBlock h (env_chain frm.toEnvironment))
                  (h3 : to_.chain_state_queue.Forall act_is_from_account)
                  (h4 : to_.chain_state_queue.Forall act_origin_is_eq_from)
                  (h5 : EnvironmentEquiv to_.toEnvironment
                         (add_new_block_to_env h frm.toEnvironment)),
                  StepNotPermute (ChainStep.step_block h h1 h2 h3 h4 h5)
  | snp_action : ∀ {frm to_ : @ChainState Base}
                   (act : @Action Base) (acts new_acts : List (@Action Base))
                   (h1 : frm.chain_state_queue = act :: acts)
                   (h2 : ActionEvaluation frm.toEnvironment act to_.toEnvironment new_acts)
                   (h3 : to_.chain_state_queue = new_acts ++ acts),
                   StepNotPermute (ChainStep.step_action act acts new_acts h1 h2 h3)
  -- Deviation: upstream's `snp_action_invalid` constructor appears to target
  -- `step_action` by mistake. This port targets `step_action_invalid`.
  | snp_action_invalid : ∀ {frm to_ : @ChainState Base}
                           (act : @Action Base) (acts : List (@Action Base))
                           (h1 : EnvironmentEquiv to_.toEnvironment frm.toEnvironment)
                           (h2 : frm.chain_state_queue = act :: acts)
                           (h3 : to_.chain_state_queue = acts)
                           (h4 : act_is_from_account act)
                           (h5 : ∀ bstate new_acts,
                                  ActionEvaluation frm.toEnvironment act bstate new_acts → False),
                           StepNotPermute (ChainStep.step_action_invalid act acts h1 h2 h3 h4 h5)

inductive NoPermutations'' :
    ∀ {frm to_ : @ChainState Base}, ChainTrace frm to_ → Prop
  | trace_nil  : ∀ {x : @ChainState Base},
                   NoPermutations'' (ChainedList.clnil (p := x))
  | trace_step : ∀ {frm mid to_ : @ChainState Base}
                   (trace : ChainTrace frm mid) (step : ChainStep mid to_),
                   NoPermutations'' trace →
                   StepNotPermute step →
                   NoPermutations'' (ChainedList.snoc trace step)

def DFSChainTrace (frm to_ : @ChainState Base) : Type :=
  { trace : ChainTrace frm to_ // NoPermutations'' trace }

def DFSChainTrace_to_ChainTrace {frm to_ : @ChainState Base}
    (trace : DFSChainTrace frm to_) : ChainTrace frm to_ :=
  trace.val

/-- Coq direction: if a property `P` holds over *all* traces, then it
    also holds when restricted to DFS (permutation-free) traces. This is
    a weakening of an all-traces theorem to DFS-traces. -/
theorem DFS_weaken
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (P :
       Nat → Nat → Nat →
       Base.Address →
       @DeploymentInfo Base Setup →
       State →
       Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop)
    (hAll : ∀ (bstate : @ChainState Base) (caddr : Base.Address)
       (trace : ChainTrace empty_state bstate),
       bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
       ∃ dep cstate inc_calls,
         deployment_info Setup trace caddr = some dep ∧
         @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
         incoming_calls Msg trace caddr = some inc_calls ∧
         P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
           dep cstate (bstate.env_account_balances caddr)
           (outgoing_acts bstate caddr) inc_calls (outgoing_txs trace caddr))
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate)
    (_hnp : NoPermutations'' trace)
    (h_deployed : bstate.env_contracts caddr = some (contract_to_weak_contract contract)) :
    ∃ dep cstate inc_calls,
      deployment_info Setup trace caddr = some dep ∧
      @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
      incoming_calls Msg trace caddr = some inc_calls ∧
      P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
        dep cstate (bstate.env_account_balances caddr)
        (outgoing_acts bstate caddr) inc_calls (outgoing_txs trace caddr) :=
  hAll bstate caddr trace h_deployed

private theorem contract_state_env_equiv
    {State : Type} [Serializable State]
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env')
    (addr : Base.Address) :
    @contract_state Base State _ env addr =
      @contract_state Base State _ env' addr := by
  unfold contract_state
  rw [henv.contract_states_eq addr]

private theorem chain_height_env_equiv
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env') :
    env.chain_height = env'.chain_height := by
  simpa [env_chain] using congrArg Chain.chain_height henv.chain_eq

private theorem current_slot_env_equiv
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env') :
    env.current_slot = env'.current_slot := by
  simpa [env_chain] using congrArg Chain.current_slot henv.chain_eq

private theorem finalized_height_env_equiv
    {env env' : @Environment Base} (henv : EnvironmentEquiv env env') :
    env.finalized_height = env'.finalized_height := by
  simpa [env_chain] using congrArg Chain.finalized_height henv.chain_eq

omit Base in
private theorem forall_cons_head
    {A : Type} {P : A → Prop} {x : A} {xs : List A}
    (h : (x :: xs).Forall P) : P x := by
  rw [← ConCert.Utils.Extras.All_Forall] at h
  exact h.1

omit Base in
private theorem forall_cons_tail
    {A : Type} {P : A → Prop} {x : A} {xs : List A}
    (h : (x :: xs).Forall P) : xs.Forall P := by
  rw [← ConCert.Utils.Extras.All_Forall] at h ⊢
  exact h.2

private def call_action_body (to_addr : Base.Address) (amount : Amount) :
    Option SerializedValue → @ActionBody Base
  | none => .act_transfer to_addr amount
  | some msg_ser => .act_call to_addr amount msg_ser

private theorem call_action_body_tx_msg
    (to_addr : Base.Address) (amount : Amount) (msg : Option SerializedValue) :
    (match call_action_body (Base := Base) to_addr amount msg with
     | .act_call _ _ msg_ser => some msg_ser
     | _ => none) = msg := by
  cases msg <;> rfl

private theorem call_action_match_tx_msg
    (to_addr : Base.Address) (amount : Amount) (msg : Option SerializedValue) :
    (match (match msg with
            | none => ActionBody.act_transfer to_addr amount
            | some msg_ser => ActionBody.act_call to_addr amount msg_ser) with
     | .act_call _ _ msg_ser => some msg_ser
     | _ => none) = msg := by
  cases msg <;> rfl

private theorem mapped_actions_outgoing_self
    (origin addr : Base.Address) (bodies : List (@ActionBody Base)) :
    ((bodies.map (fun b =>
        ({ act_origin := origin, act_from := addr, act_body := b } : @Action Base))).filter
      (fun a => Base.address_eqb a.act_from addr)).map (fun a => a.act_body) =
      bodies := by
  induction bodies with
  | nil => simp
  | cons body bodies ih =>
      simp [Address.address_eq_refl addr, ih]

/-- Core DFS induction principle.

    Direct permutation-free variant of `contract_induction`. -/
theorem dfs_contract_induction_core :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (AddBlockFacts : Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    (P :
       Nat → Nat → Nat →
       Base.Address →
       @DeploymentInfo Base Setup →
       State →
       Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop),
    DFSContractInductionCases contract AddBlockFacts DeployFacts CallFacts P →
    ∀ (bstate : @ChainState Base) (caddr : Base.Address)
      (trace : ChainTrace empty_state bstate),
      NoPermutations'' trace →
      bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
      ∃ dep cstate inc_calls,
        deployment_info Setup trace caddr = some dep ∧
        @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
        incoming_calls Msg trace caddr = some inc_calls ∧
        P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
          dep cstate (bstate.env_account_balances caddr)
          (outgoing_acts bstate caddr) inc_calls (outgoing_txs trace caddr) := by
  intro Setup Msg State Error _ _ _ _ contract AddBlockFacts DeployFacts CallFacts P hCases
    bstate caddr trace hnp hdeployed
  induction hnp with
  | trace_nil =>
      simp [empty_state] at hdeployed
  | trace_step tail step _hnp_tail hstep_not_perm ih =>
      rename_i mid to_
      have hfacts := hCases.establish_facts step tail TagFacts.tag_facts
      cases hstep_not_perm with
      | snp_block header hq_empty hvalid hqueue_accounts _hqueue_origins henv =>
          have hpre_deployed :
              mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
            have hdeployed' :
                (add_new_block_to_env header mid.toEnvironment).env_contracts caddr =
                  some (contract_to_weak_contract contract) := by
              rw [← henv.contracts_eq caddr]
              exact hdeployed
            simpa [add_new_block_to_env] using hdeployed'
          obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ := ih hpre_deployed
          refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
          · simpa [deployment_info, step_deployment_info] using hdep
          · rw [contract_state_env_equiv henv caddr]
            simpa [add_new_block_to_env] using hstate
          · simp [incoming_calls, step_incoming_calls, hinc]
          · have haddr_contract : Base.address_is_contract caddr = true :=
              contract_addr_format caddr (contract_to_weak_contract contract)
                (trace_reachable (ChainedList.snoc tail
                  (ChainStep.step_block header hq_empty hvalid hqueue_accounts
                    _hqueue_origins henv))) hdeployed
            have hqueue_mid : outgoing_acts mid caddr = [] := by
              simp [outgoing_acts, hq_empty]
            have hqueue_to : outgoing_acts to_ caddr = [] :=
              outgoing_acts_after_block_nil to_ caddr hqueue_accounts haddr_contract
            have hne_creator : caddr ≠ header.block_creator := by
              intro heq
              rw [heq, hvalid.valid_creator] at haddr_contract
              cases haddr_contract
            have hbalance :
                to_.env_account_balances caddr = mid.env_account_balances caddr := by
              rw [henv.account_balances_eq caddr]
              simp [add_new_block_to_env, add_balance,
                Address.address_eq_ne caddr header.block_creator hne_creator]
            have hheight : to_.chain_height = header.block_height := by
              simpa [add_new_block_to_env] using chain_height_env_equiv henv
            have hslot : to_.current_slot = header.block_slot := by
              simpa [add_new_block_to_env] using current_slot_env_equiv henv
            have hfin : to_.finalized_height = header.block_finalized_height := by
              simpa [add_new_block_to_env] using finalized_height_env_equiv henv
            have hP_old :
                P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                  (mid.env_account_balances caddr) [] inc_calls (outgoing_txs tail caddr) := by
              simpa [hqueue_mid] using hP
            have hP_new :=
              hCases.add_block_case mid.chain_height mid.current_slot mid.finalized_height
                header.block_height header.block_slot header.block_finalized_height
                caddr dep cstate (mid.env_account_balances caddr) inc_calls
                (outgoing_txs tail caddr)
                (by simpa [stepFactsPred] using hfacts) hP_old TagAddBlock.tag_add_block
            simpa [hheight, hslot, hfin, hbalance, hqueue_to,
              outgoing_txs, trace_txs, step_txs] using hP_new
      | snp_action act acts new_acts hq_prev eval hq_next =>
          have hreachable_to : reachable to_ :=
            trace_reachable (ChainedList.snoc tail
              (ChainStep.step_action act acts new_acts hq_prev eval hq_next))
          cases eval with
          | eval_transfer origin from_addr to_addr amount hamount hbalance hnot_contract hact henv hnew =>
              have hpre_deployed :
                  mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
                have hdeployed' :
                    (transfer_balance from_addr to_addr amount mid.toEnvironment).env_contracts
                        caddr =
                      some (contract_to_weak_contract contract) := by
                  rw [← henv.contracts_eq caddr]
                  exact hdeployed
                simpa [transfer_balance] using hdeployed'
              obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ := ih hpre_deployed
              have haddr_contract : Base.address_is_contract caddr = true :=
                contract_addr_format caddr (contract_to_weak_contract contract)
                  hreachable_to hdeployed
              have hne_to : caddr ≠ to_addr := by
                intro heq
                rw [heq, hnot_contract] at haddr_contract
                cases haddr_contract
              refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
              · simpa [deployment_info, step_deployment_info, eval_tx,
                  Address.address_eq_ne to_addr caddr (Ne.symm hne_to)] using hdep
              · rw [contract_state_env_equiv henv caddr]
                simpa [transfer_balance] using hstate
              · simp [incoming_calls, step_incoming_calls, eval_tx,
                  Address.address_eq_ne to_addr caddr (Ne.symm hne_to), hinc]
              · have hheight : to_.chain_height = mid.chain_height := by
                  simpa [transfer_balance] using chain_height_env_equiv henv
                have hslot : to_.current_slot = mid.current_slot := by
                  simpa [transfer_balance] using current_slot_env_equiv henv
                have hfin : to_.finalized_height = mid.finalized_height := by
                  simpa [transfer_balance] using finalized_height_env_equiv henv
                by_cases hfrom_eq : caddr = from_addr
                · subst from_addr
                  have hqueue_old :
                      outgoing_acts mid caddr =
                        ActionBody.act_transfer to_addr amount :: outgoing_acts to_ caddr := by
                    simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                      Address.address_eq_refl caddr]
                  have hbalance_to :
                      to_.env_account_balances caddr =
                        mid.env_account_balances caddr -
                          act_body_amount (ActionBody.act_transfer to_addr amount) := by
                    rw [henv.account_balances_eq caddr]
                    simp [transfer_balance, add_balance, act_body_amount,
                      Address.address_eq_refl caddr,
                      Address.address_eq_ne caddr to_addr hne_to]
                    ring
                  have hP_old :
                      P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                        (mid.env_account_balances caddr)
                        (ActionBody.act_transfer to_addr amount :: outgoing_acts to_ caddr)
                        inc_calls (outgoing_txs tail caddr) := by
                    simpa [hqueue_old] using hP
                  let tx : @Tx Base :=
                    { tx_origin := origin, tx_from := caddr, tx_to := to_addr,
                      tx_amount := amount, tx_body := .tx_empty }
                  have hP_new :=
                    hCases.outgoing_act_case mid.chain_height mid.current_slot
                      mid.finalized_height caddr dep cstate
                      (mid.env_account_balances caddr)
                      (ActionBody.act_transfer to_addr amount) (outgoing_acts to_ caddr)
                      inc_calls (outgoing_txs tail caddr) tx
                      hP_old rfl rfl (And.intro rfl (And.intro rfl (Or.inl rfl)))
                      TagOutgoingAct.tag_outgoing_act
                  simpa [hheight, hslot, hfin, hbalance_to, outgoing_txs, trace_txs,
                    step_txs, eval_tx, tx, Address.address_eq_refl caddr] using hP_new
                · have hfrom_false_caddr :
                      Base.address_eqb from_addr caddr = false :=
                    Address.address_eq_ne from_addr caddr (Ne.symm hfrom_eq)
                  have hfrom_false :
                      Base.address_eqb caddr from_addr = false :=
                    Address.address_eq_ne caddr from_addr hfrom_eq
                  have hto_false :
                      Base.address_eqb caddr to_addr = false :=
                    Address.address_eq_ne caddr to_addr hne_to
                  have hqueue_eq :
                      outgoing_acts mid caddr = outgoing_acts to_ caddr := by
                    simp [outgoing_acts, hq_prev, hq_next, hnew, hact, hfrom_false_caddr]
                  have hbalance_to :
                      to_.env_account_balances caddr = mid.env_account_balances caddr := by
                    rw [henv.account_balances_eq caddr]
                    simp [transfer_balance, add_balance, hfrom_false, hto_false]
                  simpa [hheight, hslot, hfin, hbalance_to, hqueue_eq, outgoing_txs,
                    trace_txs, step_txs, eval_tx, hfrom_false_caddr] using hP
          | eval_deploy origin from_addr to_addr amount wc setup state hamount hbalance hcontract_addr hnot_deployed hact hinit henv hnew =>
              have hheight : to_.chain_height = mid.chain_height := by
                simpa [set_contract_state, add_contract, transfer_balance] using
                  chain_height_env_equiv henv
              have hslot : to_.current_slot = mid.current_slot := by
                simpa [set_contract_state, add_contract, transfer_balance] using
                  current_slot_env_equiv henv
              have hfin : to_.finalized_height = mid.finalized_height := by
                simpa [set_contract_state, add_contract, transfer_balance] using
                  finalized_height_env_equiv henv
              by_cases hto_eq : caddr = to_addr
              · subst to_addr
                have hwc : wc = contract_to_weak_contract contract := by
                  have hdeployed' :
                      (set_contract_state caddr state
                          (add_contract caddr wc
                            (transfer_balance from_addr caddr amount mid.toEnvironment))).env_contracts
                          caddr =
                        some (contract_to_weak_contract contract) := by
                    rw [← henv.contracts_eq caddr]
                    exact hdeployed
                  exact Option.some.inj
                    (by
                      simpa [set_contract_state, add_contract,
                        Address.address_eq_refl caddr] using hdeployed')
                subst wc
                obtain ⟨setup_strong, result_strong, hsetup, hstate_ser, hinit_strong⟩ :=
                  wc_init_strong (contract := contract) hinit
                let dep : @DeploymentInfo Base Setup :=
                  { deployment_origin := origin, deployment_from := from_addr,
                    deployment_amount := amount, deployment_setup := setup_strong }
                let ctx : @ContractCallContext Base :=
                  { ctx_origin := origin, ctx_from := from_addr,
                    ctx_contract_address := caddr,
                    ctx_contract_balance := amount, ctx_amount := amount }
                have hno_out_queue :=
                  undeployed_contract_no_out_queue caddr mid (trace_reachable tail)
                    hcontract_addr hnot_deployed
                have hno_out_queue_cons :
                    ({ act_origin := origin, act_from := from_addr,
                       act_body := ActionBody.act_deploy amount
                         (contract_to_weak_contract contract) setup } :: acts).Forall
                      (fun a => Base.address_eqb a.act_from caddr = false) := by
                  simpa [hq_prev, hact] using hno_out_queue
                have hfrom_false :
                    Base.address_eqb from_addr caddr = false := by
                  let deployedAction : @Action Base :=
                    { act_origin := origin, act_from := from_addr,
                      act_body := ActionBody.act_deploy amount
                        (contract_to_weak_contract contract) setup }
                  have hno_out_queue_cons' :
                      (deployedAction :: acts).Forall
                        (fun a => Base.address_eqb a.act_from caddr = false) := by
                    simpa [deployedAction] using hno_out_queue_cons
                  have hhead :
                      Base.address_eqb deployedAction.act_from caddr = false :=
                    @forall_cons_head (@Action Base)
                      (fun a => Base.address_eqb a.act_from caddr = false)
                      deployedAction acts hno_out_queue_cons'
                  simpa [deployedAction] using hhead
                have hfrom_false_sym :
                    Base.address_eqb caddr from_addr = false := by
                  rw [Address.address_eq_sym]
                  exact hfrom_false
                have hacts_no_out :
                    acts.Forall (fun a => Base.address_eqb a.act_from caddr = false) :=
                  forall_cons_tail hno_out_queue_cons
                have hqueue_to_no_out :
                    to_.chain_state_queue.Forall
                      (fun a => Base.address_eqb a.act_from caddr = false) := by
                  rw [hq_next, hnew]
                  simpa using hacts_no_out
                have hqueue_to : outgoing_acts to_ caddr = [] :=
                  outgoing_acts_after_deploy_nil to_ caddr hqueue_to_no_out
                have hin_tail : incoming_calls Msg tail caddr = some [] :=
                  undeployed_contract_no_in_calls caddr tail hcontract_addr hnot_deployed
                have hout_tail : outgoing_txs tail caddr = [] :=
                  undeployed_contract_no_out_txs caddr tail hcontract_addr hnot_deployed
                have hbalance_zero :
                    mid.env_account_balances caddr = 0 :=
                  undeployed_contract_balance_0 mid caddr (trace_reachable tail)
                    hcontract_addr hnot_deployed
                have hbalance_to : to_.env_account_balances caddr = amount := by
                  rw [henv.account_balances_eq caddr]
                  simp [set_contract_state, add_contract, transfer_balance, add_balance,
                    Address.address_eq_refl caddr, hfrom_false_sym, hbalance_zero]
                refine ⟨dep, result_strong, [], ?_, ?_, ?_, ?_⟩
                · simp [dep, deployment_info, step_deployment_info, eval_tx,
                    Address.address_eq_refl caddr, hsetup]
                · rw [contract_state_env_equiv henv caddr]
                  simp [contract_state, set_contract_state, set_chain_contract_state,
                    Address.address_eq_refl caddr, ← hstate_ser,
                    Serializable.deserialize_serialize]
                · simp [incoming_calls, step_incoming_calls, eval_tx,
                    Address.address_eq_refl caddr, hin_tail]
                · have hdeploy_facts :
                      DeployFacts
                        (transfer_balance from_addr caddr amount mid.toEnvironment).toChain ctx := by
                    simpa [stepFactsPred, ctx] using hfacts
                  have hP_init :=
                    hCases.init_case
                      (transfer_balance from_addr caddr amount mid.toEnvironment).toChain
                      ctx setup_strong result_strong hdeploy_facts hinit_strong
                      TagDeployment.tag_deployment
                  have hout_trace :
                      outgoing_txs
                          (ChainedList.snoc tail
                            (ChainStep.step_action act acts new_acts hq_prev
                              (ActionEvaluation.eval_deploy origin from_addr caddr amount
                                (contract_to_weak_contract contract) setup state
                                hamount hbalance hcontract_addr hnot_deployed hact hinit henv hnew)
                              hq_next))
                          caddr = [] := by
                    simp [outgoing_txs, trace_txs, step_txs, eval_tx, hfrom_false]
                    simpa [outgoing_txs] using hout_tail
                  simpa [ctx, dep, hheight, hslot, hfin, hbalance_to, hqueue_to,
                    hout_trace, transfer_balance] using hP_init
              · have hto_false_caddr :
                    Base.address_eqb to_addr caddr = false :=
                  Address.address_eq_ne to_addr caddr (Ne.symm hto_eq)
                have hto_false :
                    Base.address_eqb caddr to_addr = false :=
                  Address.address_eq_ne caddr to_addr hto_eq
                have hpre_deployed :
                    mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
                  have hdeployed' :
                      (set_contract_state to_addr state
                          (add_contract to_addr wc
                            (transfer_balance from_addr to_addr amount mid.toEnvironment))).env_contracts
                          caddr =
                        some (contract_to_weak_contract contract) := by
                    rw [← henv.contracts_eq caddr]
                    exact hdeployed
                  simpa [set_contract_state, add_contract, hto_false] using hdeployed'
                obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ :=
                  ih hpre_deployed
                refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
                · simpa [deployment_info, step_deployment_info, eval_tx,
                    hto_false_caddr] using hdep
                · rw [contract_state_env_equiv henv caddr]
                  simpa [contract_state, set_contract_state, set_chain_contract_state,
                    hto_false] using hstate
                · simp [incoming_calls, step_incoming_calls, eval_tx,
                    hto_false_caddr, hinc]
                · by_cases hfrom_eq : caddr = from_addr
                  · subst from_addr
                    have hqueue_old :
                        outgoing_acts mid caddr =
                          ActionBody.act_deploy amount wc setup :: outgoing_acts to_ caddr := by
                      simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                        Address.address_eq_refl caddr]
                    have hbalance_to :
                        to_.env_account_balances caddr =
                          mid.env_account_balances caddr -
                            act_body_amount (ActionBody.act_deploy amount wc setup) := by
                      rw [henv.account_balances_eq caddr]
                      simp [set_contract_state, add_contract, transfer_balance,
                        add_balance, act_body_amount, Address.address_eq_refl caddr,
                        hto_false]
                      ring
                    have hP_old :
                        P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                          (mid.env_account_balances caddr)
                          (ActionBody.act_deploy amount wc setup :: outgoing_acts to_ caddr)
                          inc_calls (outgoing_txs tail caddr) := by
                      simpa [hqueue_old] using hP
                    let tx : @Tx Base :=
                      { tx_origin := origin, tx_from := caddr, tx_to := to_addr,
                        tx_amount := amount, tx_body := .tx_deploy wc setup }
                    have hP_new :=
                      hCases.outgoing_act_case mid.chain_height mid.current_slot
                        mid.finalized_height caddr dep cstate
                        (mid.env_account_balances caddr)
                        (ActionBody.act_deploy amount wc setup) (outgoing_acts to_ caddr)
                        inc_calls (outgoing_txs tail caddr) tx
                        hP_old rfl rfl (And.intro rfl rfl)
                        TagOutgoingAct.tag_outgoing_act
                    simpa [hheight, hslot, hfin, hbalance_to, outgoing_txs, trace_txs,
                      step_txs, eval_tx, tx, Address.address_eq_refl caddr] using hP_new
                  · have hfrom_false_caddr :
                        Base.address_eqb from_addr caddr = false :=
                      Address.address_eq_ne from_addr caddr (Ne.symm hfrom_eq)
                    have hfrom_false :
                        Base.address_eqb caddr from_addr = false :=
                      Address.address_eq_ne caddr from_addr hfrom_eq
                    have hqueue_eq :
                        outgoing_acts mid caddr = outgoing_acts to_ caddr := by
                      simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                        hfrom_false_caddr]
                    have hbalance_to :
                        to_.env_account_balances caddr = mid.env_account_balances caddr := by
                      rw [henv.account_balances_eq caddr]
                      simp [set_contract_state, add_contract, transfer_balance,
                        add_balance, hfrom_false, hto_false]
                    simpa [hheight, hslot, hfin, hbalance_to, hqueue_eq, outgoing_txs,
                      trace_txs, step_txs, eval_tx, hfrom_false_caddr] using hP
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state resp_acts hamount hbalance hcontract hstate hact hreceive hnew henv =>
              have hheight : to_.chain_height = mid.chain_height := by
                simpa [set_contract_state, transfer_balance] using
                  chain_height_env_equiv henv
              have hslot : to_.current_slot = mid.current_slot := by
                simpa [set_contract_state, transfer_balance] using
                  current_slot_env_equiv henv
              have hfin : to_.finalized_height = mid.finalized_height := by
                simpa [set_contract_state, transfer_balance] using
                  finalized_height_env_equiv henv
              have hpre_deployed :
                  mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
                have hdeployed' :
                    (set_contract_state to_addr new_state
                        (transfer_balance from_addr to_addr amount mid.toEnvironment)).env_contracts
                        caddr =
                      some (contract_to_weak_contract contract) := by
                  rw [← henv.contracts_eq caddr]
                  exact hdeployed
                simpa [set_contract_state, transfer_balance] using hdeployed'
              obtain ⟨dep, cstate, inc_calls, hdep, hstate_old, hinc, hP⟩ :=
                ih hpre_deployed
              by_cases hto_eq : caddr = to_addr
              · subst to_addr
                have hwc : wc = contract_to_weak_contract contract := by
                  exact Option.some.inj (hcontract.symm.trans hpre_deployed)
                subst wc
                obtain ⟨prev_state_strong, msg_strong, new_state_strong,
                  hprev_deser, hmsg_rel, hnew_state_ser, hreceive_strong⟩ :=
                  wc_receive_strong (contract := contract) hreceive
                have hprev_contract_state :
                    @contract_state Base State _ mid.toEnvironment caddr =
                      some prev_state_strong := by
                  unfold contract_state
                  rw [hstate]
                  exact hprev_deser
                have hcstate_eq : cstate = prev_state_strong :=
                  Option.some.inj (hstate_old.symm.trans hprev_contract_state)
                subst prev_state_strong
                let chain : Chain :=
                  (transfer_balance from_addr caddr amount mid.toEnvironment).toChain
                let ctx : @ContractCallContext Base :=
                  { ctx_origin := origin, ctx_from := from_addr,
                    ctx_contract_address := caddr,
                    ctx_contract_balance :=
                      (transfer_balance from_addr caddr amount
                        mid.toEnvironment).env_account_balances caddr,
                    ctx_amount := amount }
                let callInfo : @ContractCallInfo Base Msg :=
                  { call_origin := origin, call_from := from_addr,
                    call_amount := amount, call_msg := msg_strong }
                have hctx_balance :
                    to_.env_account_balances caddr =
                      (transfer_balance from_addr caddr amount
                        mid.toEnvironment).env_account_balances caddr := by
                  rw [henv.account_balances_eq caddr]
                  simp [set_contract_state]
                have hreceive_ctx :
                    contract.receive chain ctx cstate msg_strong =
                      .Ok (new_state_strong, resp_acts) := by
                  simpa [chain, ctx, hctx_balance] using hreceive_strong
                refine ⟨dep, new_state_strong, callInfo :: inc_calls, ?_, ?_, ?_, ?_⟩
                · simpa [deployment_info, step_deployment_info, eval_tx,
                    Address.address_eq_refl caddr] using hdep
                · rw [contract_state_env_equiv henv caddr]
                  simp [contract_state, set_contract_state, set_chain_contract_state,
                    Address.address_eq_refl caddr, ← hnew_state_ser,
                    Serializable.deserialize_serialize]
                · cases msg_strong with
                  | none =>
                      have hmsg_none : msg = none := by
                        simpa using hmsg_rel
                      simp [incoming_calls, step_incoming_calls, eval_tx,
                        Address.address_eq_refl caddr, hmsg_none, hinc, callInfo]
                  | some msg_typed =>
                      have hbind : (msg >>= deserialize) = some msg_typed := by
                        simpa using hmsg_rel
                      cases msg with
                      | none =>
                          simp at hbind
                      | some msg_ser =>
                          cases hdes : (deserialize msg_ser : Option Msg) with
                          | none =>
                              simp [hdes] at hbind
                          | some msg_typed' =>
                              simp [hdes] at hbind
                              cases hbind
                              simp [incoming_calls, step_incoming_calls, eval_tx,
                                Address.address_eq_refl caddr, hinc, hdes, callInfo]
                · by_cases hfrom_eq : from_addr = caddr
                  · subst from_addr
                    let head : @ActionBody Base := call_action_body caddr amount msg
                    let prev_queue : List (@ActionBody Base) :=
                      (acts.filter (fun a => Base.address_eqb a.act_from caddr)).map
                        (fun a => a.act_body)
                    have hhead_match :
                        (match head with
                         | .act_transfer to_ amount' =>
                             to_ = ctx.ctx_contract_address ∧
                             amount' = ctx.ctx_amount ∧ msg_strong = none
                         | .act_call to_ amount' msg_ser =>
                             to_ = ctx.ctx_contract_address ∧
                             amount' = ctx.ctx_amount ∧
                             msg_strong ≠ none ∧ deserialize msg_ser = msg_strong
                         | _ => False) := by
                      cases hmsg : msg with
                      | none =>
                          cases msg_strong with
                          | none =>
                              simp only [head, call_action_body, hmsg]
                              simp [ctx]
                          | some msg_typed =>
                              simp [hmsg] at hmsg_rel
                      | some msg_ser =>
                          cases msg_strong with
                          | none =>
                              simp [hmsg] at hmsg_rel
                          | some msg_typed =>
                              have hdes : deserialize msg_ser = some msg_typed := by
                                simpa [hmsg] using hmsg_rel
                              simp only [head, call_action_body, hmsg]
                              change caddr = ctx.ctx_contract_address ∧
                                amount = ctx.ctx_amount ∧
                                (some msg_typed ≠ (none : Option Msg)) ∧
                                deserialize msg_ser = some msg_typed
                              simp [ctx, hdes]
                    have hqueue_mid :
                        outgoing_acts mid caddr = head :: prev_queue := by
                      simp [outgoing_acts, hq_prev, hact, head, prev_queue,
                        call_action_body, Address.address_eq_refl caddr]
                      rfl
                    have hqueue_to :
                        outgoing_acts to_ caddr = resp_acts ++ prev_queue := by
                      simp [outgoing_acts, hq_next, hnew, prev_queue,
                        mapped_actions_outgoing_self]
                    have hcall_balance_old :
                        mid.env_account_balances caddr =
                          (transfer_balance caddr caddr amount
                            mid.toEnvironment).env_account_balances caddr := by
                      simp [transfer_balance, add_balance, Address.address_eq_refl caddr]
                    have hcall_facts :
                        CallFacts chain ctx cstate (head :: prev_queue) (some inc_calls) := by
                      have hfacts_call := hfacts cstate hpre_deployed hstate_old
                      simpa [stepFactsPred, chain, ctx, hinc, hqueue_mid] using hfacts_call
                    have hP_old :
                        P chain.chain_height chain.current_slot chain.finalized_height
                          caddr dep cstate ctx.ctx_contract_balance
                          (head :: prev_queue) inc_calls (outgoing_txs tail caddr) := by
                      simpa [chain, ctx, hcall_balance_old, hqueue_mid] using hP
                    have hP_new :=
                      hCases.recursive_call_case chain ctx dep cstate msg_strong
                        head prev_queue inc_calls (outgoing_txs tail caddr)
                        new_state_strong resp_acts rfl hcall_facts hP_old
                        hhead_match hreceive_ctx TagRecursiveCall.tag_recursive_call
                    cases msg <;>
                      simpa [chain, ctx, hheight, hslot, hfin, hctx_balance, hqueue_to,
                        outgoing_txs, trace_txs, step_txs, eval_tx, transfer_balance,
                        Address.address_eq_refl caddr, callInfo, head,
                        call_action_body, call_action_body_tx_msg,
                        call_action_match_tx_msg] using hP_new
                  · let prev_queue : List (@ActionBody Base) := outgoing_acts mid caddr
                    have hfrom_false_caddr :
                        Base.address_eqb from_addr caddr = false :=
                      Address.address_eq_ne from_addr caddr hfrom_eq
                    have hfrom_false :
                        Base.address_eqb caddr from_addr = false :=
                      Address.address_eq_ne caddr from_addr (Ne.symm hfrom_eq)
                    have hqueue_to :
                        outgoing_acts to_ caddr = resp_acts ++ prev_queue := by
                      simp [outgoing_acts, hq_prev, hq_next, hnew, hact, prev_queue,
                        hfrom_false_caddr, mapped_actions_outgoing_self]
                    have hcall_balance_old :
                        mid.env_account_balances caddr =
                          (transfer_balance from_addr caddr amount
                            mid.toEnvironment).env_account_balances caddr - amount := by
                      simp [transfer_balance, add_balance, hfrom_false,
                        Address.address_eq_refl caddr]
                    have hcall_facts :
                        CallFacts chain ctx cstate prev_queue (some inc_calls) := by
                      have hfacts_call := hfacts cstate hpre_deployed hstate_old
                      simpa [stepFactsPred, chain, ctx, hinc, prev_queue] using hfacts_call
                    have hP_old :
                        P chain.chain_height chain.current_slot chain.finalized_height
                          caddr dep cstate (ctx.ctx_contract_balance - ctx.ctx_amount)
                          prev_queue inc_calls (outgoing_txs tail caddr) := by
                      simpa [chain, ctx, hcall_balance_old, prev_queue] using hP
                    have hP_new :=
                      hCases.nonrecursive_call_case chain ctx dep cstate msg_strong
                        prev_queue inc_calls (outgoing_txs tail caddr)
                        new_state_strong resp_acts hfrom_eq hcall_facts hP_old
                        hreceive_ctx TagNonrecursiveCall.tag_nonrecursive_call
                    simpa [chain, ctx, hheight, hslot, hfin, hctx_balance, hqueue_to,
                      outgoing_txs, trace_txs, step_txs, eval_tx, hfrom_false_caddr,
                      callInfo] using hP_new
              · have hto_false_caddr :
                    Base.address_eqb to_addr caddr = false :=
                  Address.address_eq_ne to_addr caddr (Ne.symm hto_eq)
                have hto_false :
                    Base.address_eqb caddr to_addr = false :=
                  Address.address_eq_ne caddr to_addr hto_eq
                refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
                · simpa [deployment_info, step_deployment_info, eval_tx,
                    hto_false_caddr] using hdep
                · rw [contract_state_env_equiv henv caddr]
                  simpa [contract_state, set_contract_state, set_chain_contract_state,
                    hto_false] using hstate_old
                · simp [incoming_calls, step_incoming_calls, eval_tx,
                    hto_false_caddr, hinc]
                · by_cases hfrom_eq : caddr = from_addr
                  · subst from_addr
                    have hbalance_to :
                        to_.env_account_balances caddr =
                          mid.env_account_balances caddr - amount := by
                      rw [henv.account_balances_eq caddr]
                      simp [set_contract_state, transfer_balance, add_balance,
                        Address.address_eq_refl caddr, hto_false]
                      ring
                    cases msg with
                    | none =>
                        have hqueue_old :
                            outgoing_acts mid caddr =
                              ActionBody.act_transfer to_addr amount :: outgoing_acts to_ caddr := by
                          simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                            Address.address_eq_refl caddr, hto_false_caddr]
                        have hP_old :
                            P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                              (mid.env_account_balances caddr)
                              (ActionBody.act_transfer to_addr amount :: outgoing_acts to_ caddr)
                              inc_calls (outgoing_txs tail caddr) := by
                          simpa [hqueue_old] using hP
                        let tx : @Tx Base :=
                          { tx_origin := origin, tx_from := caddr, tx_to := to_addr,
                            tx_amount := amount, tx_body := .tx_call none }
                        have hP_new :=
                          hCases.outgoing_act_case mid.chain_height mid.current_slot
                            mid.finalized_height caddr dep cstate
                            (mid.env_account_balances caddr)
                            (ActionBody.act_transfer to_addr amount) (outgoing_acts to_ caddr)
                            inc_calls (outgoing_txs tail caddr) tx
                            hP_old rfl rfl
                            (And.intro rfl (And.intro rfl (Or.inr rfl)))
                            TagOutgoingAct.tag_outgoing_act
                        simpa [hheight, hslot, hfin, hbalance_to, outgoing_txs,
                          trace_txs, step_txs, eval_tx, tx,
                          Address.address_eq_refl caddr] using hP_new
                    | some msg_ser =>
                        have hqueue_old :
                            outgoing_acts mid caddr =
                              ActionBody.act_call to_addr amount msg_ser ::
                                outgoing_acts to_ caddr := by
                          simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                            Address.address_eq_refl caddr, hto_false_caddr]
                        have hP_old :
                            P mid.chain_height mid.current_slot mid.finalized_height caddr dep cstate
                              (mid.env_account_balances caddr)
                              (ActionBody.act_call to_addr amount msg_ser :: outgoing_acts to_ caddr)
                              inc_calls (outgoing_txs tail caddr) := by
                          simpa [hqueue_old] using hP
                        let tx : @Tx Base :=
                          { tx_origin := origin, tx_from := caddr, tx_to := to_addr,
                            tx_amount := amount, tx_body := .tx_call (some msg_ser) }
                        have hP_new :=
                          hCases.outgoing_act_case mid.chain_height mid.current_slot
                            mid.finalized_height caddr dep cstate
                            (mid.env_account_balances caddr)
                            (ActionBody.act_call to_addr amount msg_ser) (outgoing_acts to_ caddr)
                            inc_calls (outgoing_txs tail caddr) tx
                            hP_old rfl rfl (And.intro rfl (And.intro rfl rfl))
                            TagOutgoingAct.tag_outgoing_act
                        simpa [hheight, hslot, hfin, hbalance_to, outgoing_txs,
                          trace_txs, step_txs, eval_tx, tx,
                          Address.address_eq_refl caddr] using hP_new
                  · have hfrom_false_caddr :
                        Base.address_eqb from_addr caddr = false :=
                      Address.address_eq_ne from_addr caddr (Ne.symm hfrom_eq)
                    have hfrom_false :
                        Base.address_eqb caddr from_addr = false :=
                      Address.address_eq_ne caddr from_addr hfrom_eq
                    have hqueue_eq :
                        outgoing_acts mid caddr = outgoing_acts to_ caddr := by
                      simp [outgoing_acts, hq_prev, hq_next, hnew, hact,
                        hfrom_false_caddr, hto_false_caddr]
                    have hbalance_to :
                        to_.env_account_balances caddr = mid.env_account_balances caddr := by
                      rw [henv.account_balances_eq caddr]
                      simp [set_contract_state, transfer_balance, add_balance,
                        hfrom_false, hto_false]
                    simpa [hheight, hslot, hfin, hbalance_to, hqueue_eq, outgoing_txs,
                      trace_txs, step_txs, eval_tx, hfrom_false_caddr] using hP
      | snp_action_invalid act acts henv hq_prev hq_next hfrom_account hinvalid =>
          have hpre_deployed :
              mid.env_contracts caddr = some (contract_to_weak_contract contract) := by
            rw [← henv.contracts_eq caddr]
            exact hdeployed
          obtain ⟨dep, cstate, inc_calls, hdep, hstate, hinc, hP⟩ := ih hpre_deployed
          refine ⟨dep, cstate, inc_calls, ?_, ?_, ?_, ?_⟩
          · simpa [deployment_info, step_deployment_info] using hdep
          · rw [contract_state_env_equiv henv caddr]
            exact hstate
          · simp [incoming_calls, step_incoming_calls, hinc]
          · have haddr_contract : Base.address_is_contract caddr = true :=
              contract_addr_format caddr (contract_to_weak_contract contract)
                (trace_reachable (ChainedList.snoc tail
                  (ChainStep.step_action_invalid act acts henv hq_prev hq_next
                    hfrom_account hinvalid))) hdeployed
            have hact_not_from_contract :
                Base.address_eqb act.act_from caddr = false := by
              unfold act_is_from_account at hfrom_account
              apply Address.address_eq_ne
              intro heq
              rw [heq, haddr_contract] at hfrom_account
              cases hfrom_account
            have hqueue :
                outgoing_acts mid caddr = outgoing_acts to_ caddr := by
              simp [outgoing_acts, hq_prev, hq_next, hact_not_from_contract]
            have hheight : to_.chain_height = mid.chain_height :=
              chain_height_env_equiv henv
            have hslot : to_.current_slot = mid.current_slot :=
              current_slot_env_equiv henv
            have hfin : to_.finalized_height = mid.finalized_height :=
              finalized_height_env_equiv henv
            have hbalance :
                to_.env_account_balances caddr = mid.env_account_balances caddr :=
              henv.account_balances_eq caddr
            simpa [hheight, hslot, hfin, hbalance, hqueue, outgoing_txs, trace_txs,
              step_txs] using hP


/-- DFS-flavored contract induction. Restricted to traces without
    permutation steps; consequently the queue-permutation case is
    *not* required. Takes `DFSContractInductionCases`, which omits
    `permute_case`. -/
theorem dfs_contract_induction :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : Contract Setup Msg State Error)
    (AddBlockFacts : Nat → Nat → Nat → Nat → Nat → Nat → Prop)
    (DeployFacts : Chain → @ContractCallContext Base → Prop)
    (CallFacts :
       Chain → @ContractCallContext Base → State → List (@ActionBody Base) →
       Option (List (@ContractCallInfo Base Msg)) → Prop)
    (P :
       Nat → Nat → Nat →
       Base.Address →
       @DeploymentInfo Base Setup →
       State →
       Amount →
       List (@ActionBody Base) →
       List (@ContractCallInfo Base Msg) →
       List (@Tx Base) → Prop),
    DFSContractInductionCases contract AddBlockFacts DeployFacts CallFacts P →
    ∀ (bstate : @ChainState Base) (caddr : Base.Address)
      (trace : ChainTrace empty_state bstate),
      NoPermutations'' trace →
      bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
      ∃ dep cstate inc_calls,
        deployment_info Setup trace caddr = some dep ∧
        @contract_state Base State _ bstate.toEnvironment caddr = some cstate ∧
        incoming_calls Msg trace caddr = some inc_calls ∧
        P bstate.chain_height bstate.current_slot bstate.finalized_height caddr
          dep cstate (bstate.env_account_balances caddr)
          (outgoing_acts bstate caddr) inc_calls (outgoing_txs trace caddr) := by
  exact dfs_contract_induction_core

end ConCert.Execution.BlockchainBFS
