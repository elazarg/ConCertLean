/- Port of execution/theories/InterContractCommunication.v -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Serializable
import ConCert.Utils.Extras

namespace ConCert.Execution.InterContractCommunication

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

def txCallTo (addr : Base.Address) (tx : @Tx Base) : Bool :=
  match tx.tx_body with
  | .tx_call _ => Base.address_eqb tx.tx_to addr
  | _ => false

def actTo (addr : Base.Address) (act : @ActionBody Base) : Bool :=
  match act with
  | .act_transfer to_ _ => Base.address_eqb to_ addr
  | .act_call to_ _ _   => Base.address_eqb to_ addr
  | _ => false

def callFrom {Msg : Type} (addr : Base.Address) (ci : @ContractCallInfo Base Msg) : Bool :=
  Base.address_eqb ci.call_from addr

theorem deployed_incoming_calls_typed :
  ∀ (bstate : @ChainState Base) (caddr : Base.Address)
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error}
    (trace : ChainTrace empty_state bstate),
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    ∃ inc_calls, incoming_calls Msg trace caddr = some inc_calls := by
  intro bstate caddr Setup Msg State Error _ _ _ _ contract trace hdeployed
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
          State → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ _ _ _ _ _ _ => True
  have hcases : ContractInductionCases contract
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True) P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
          cases eval <;> try trivial
          intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intros; trivial
    · intros; trivial
    · intros; trivial
    · intros; trivial
    · intros; trivial
    · intros; trivial
  obtain ⟨_, _, inc_calls, _, _, hcalls, _⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  exact ⟨inc_calls, hcalls⟩

theorem undeployed_contract_no_state :
  ∀ (bstate : @ChainState Base) (caddr : Base.Address)
    (_trace : ChainTrace empty_state bstate),
    bstate.env_contracts caddr = none →
    bstate.env_contract_states caddr = none := by
  intros bstate caddr trace hnot
  cases hs : bstate.env_contract_states caddr with
  | none => rfl
  | some state =>
      have hr : reachable bstate := ⟨trace⟩
      obtain ⟨wc, hwc⟩ := contract_states_deployed bstate caddr state hr hs
      rw [hnot] at hwc
      cases hwc

theorem no_outgoing_txs_to_undeployed_contract :
  ∀ (bstate : @ChainState Base) (caddrA caddrB : Base.Address)
    (trace : ChainTrace empty_state bstate)
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error},
    bstate.env_contracts caddrA = some (contract_to_weak_contract contract) →
    bstate.env_contracts caddrB = none →
    (outgoing_txs trace caddrA).filter (txCallTo caddrB) = [] := by
  intros bstate caddrA caddrB trace Setup Msg State Error _ _ _ _ contract hA hB
  induction trace with
  | clnil =>
      simp [outgoing_txs, trace_txs]
  | @snoc mid next tail step ih =>
      cases step with
      | step_block hdr hq hvalid hfrom horigin henv =>
          have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contract) := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = none := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          simpa [outgoing_txs, trace_txs, step_txs] using ih hA' hB'
      | step_action act acts new_acts hq eval hqnext =>
          cases eval with
          | eval_transfer origin from_addr to_addr amount hnonneg hbal hnot_contract hact henv hnew =>
              have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contract) := by
                rw [henv.contracts_eq caddrA] at hA
                exact hA
              have hB' : mid.env_contracts caddrB = none := by
                rw [henv.contracts_eq caddrB] at hB
                exact hB
              simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo] using ih hA' hB'
          | eval_deploy origin from_addr to_addr amount wc setup state hnonneg hbal his_contract hnone hact hinit henv hnew =>
              by_cases hBA : to_addr = caddrA
              · subst to_addr
                rw [henv.contracts_eq caddrA] at hA
                have htail : outgoing_txs tail caddrA = [] :=
                  undeployed_contract_no_out_txs caddrA tail his_contract hnone
                simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo] using
                  congrArg (List.filter (txCallTo caddrB)) htail
              · have hA' : mid.env_contracts caddrA =
                    some (contract_to_weak_contract contract) := by
                    rw [henv.contracts_eq caddrA] at hA
                    simpa [add_contract, set_contract_state,
                      Address.address_eq_ne _ _ (fun h => hBA h.symm)] using hA
                by_cases hBB : to_addr = caddrB
                · subst to_addr
                  rw [henv.contracts_eq caddrB] at hB
                  simp [add_contract, set_contract_state, Address.address_eq_refl] at hB
                · have hB' : mid.env_contracts caddrB = none := by
                    rw [henv.contracts_eq caddrB] at hB
                    simpa [add_contract, set_contract_state,
                      Address.address_eq_ne _ _ (fun h => hBB h.symm)] using hB
                  simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo] using ih hA' hB'
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state resp_acts
              hnonneg hbal hcontract hstate hact hreceive hnew henv =>
              have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contract) := by
                rw [henv.contracts_eq caddrA] at hA
                exact hA
              have hB' : mid.env_contracts caddrB = none := by
                rw [henv.contracts_eq caddrB] at hB
                exact hB
              by_cases ht : to_addr = caddrB
              · subst to_addr
                rw [hcontract] at hB'
                cases hB'
              · simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo,
                  Address.address_eq_ne _ _ ht] using ih hA' hB'
      | step_action_invalid act acts henv hq hqnext hfrom hno =>
          have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contract) := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = none := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          simpa [outgoing_txs, trace_txs, step_txs] using ih hA' hB'
      | step_permute henv hperm =>
          have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contract) := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = none := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          simpa [outgoing_txs, trace_txs, step_txs] using ih hA' hB'

theorem no_incoming_calls_from_undeployed_contract :
  ∀ (bstate : @ChainState Base) (caddrA caddrB : Base.Address)
    (trace : ChainTrace empty_state bstate)
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error},
    bstate.env_contracts caddrA = none →
    Base.address_is_contract caddrA = true →
    bstate.env_contracts caddrB = some (contract_to_weak_contract contract) →
    ∃ inc_calls,
      incoming_calls Msg trace caddrB = some inc_calls ∧
      inc_calls.filter (callFrom caddrA) = [] := by
  intros bstate caddrA caddrB trace Setup Msg State Error _ _ _ _ contract hA hAfmt hB
  induction trace with
  | clnil =>
      cases hB
  | @snoc mid next tail step ih =>
      cases step with
      | step_block hdr hq hvalid hfrom horigin henv =>
          have hA' : mid.env_contracts caddrA = none := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contract) := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          obtain ⟨calls, hcalls, hfilter⟩ := ih hA' hB'
          refine ⟨calls, ?_, hfilter⟩
          simp [incoming_calls, step_incoming_calls, hcalls]
      | step_action act acts new_acts hq eval hqnext =>
          cases eval with
          | eval_transfer origin from_addr to_addr amount hnonneg hbal hnot_contract hact henv hnew =>
              have hA' : mid.env_contracts caddrA = none := by
                rw [henv.contracts_eq caddrA] at hA
                exact hA
              have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contract) := by
                rw [henv.contracts_eq caddrB] at hB
                exact hB
              obtain ⟨calls, hcalls, hfilter⟩ := ih hA' hB'
              refine ⟨calls, ?_, hfilter⟩
              simp [incoming_calls, step_incoming_calls, eval_tx, hcalls]
          | eval_deploy origin from_addr to_addr amount wc setup state hnonneg hbal his_contract hnone hact hinit henv hnew =>
              by_cases htoB : to_addr = caddrB
              · subst to_addr
                have hprior : incoming_calls Msg tail caddrB = some [] :=
                  undeployed_contract_no_in_calls caddrB tail his_contract hnone
                refine ⟨[], ?_, rfl⟩
                simp [incoming_calls, step_incoming_calls, eval_tx, hprior]
              · have hA' : mid.env_contracts caddrA = none := by
                  rw [henv.contracts_eq caddrA] at hA
                  by_cases htoA : to_addr = caddrA
                  · subst to_addr
                    simp [add_contract, set_contract_state, Address.address_eq_refl] at hA
                  · simpa [add_contract, set_contract_state,
                      Address.address_eq_ne caddrA to_addr (Ne.symm htoA)] using hA
                have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contract) := by
                  rw [henv.contracts_eq caddrB] at hB
                  simpa [add_contract, set_contract_state,
                    Address.address_eq_ne caddrB to_addr (Ne.symm htoB)] using hB
                obtain ⟨calls, hcalls, hfilter⟩ := ih hA' hB'
                refine ⟨calls, ?_, hfilter⟩
                simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                  Address.address_eq_ne _ _ htoB]
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state resp_acts
              hnonneg hbal hcontract hstate hact hreceive hnew henv =>
              have hA' : mid.env_contracts caddrA = none := by
                rw [henv.contracts_eq caddrA] at hA
                exact hA
              have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contract) := by
                rw [henv.contracts_eq caddrB] at hB
                exact hB
              have hfrom_ne : Base.address_eqb from_addr caddrA = false := by
                have hqforall := undeployed_contract_no_out_queue caddrA mid ⟨tail⟩ hAfmt hA'
                rw [hq] at hqforall
                rw [List.forall_iff_forall_mem] at hqforall
                have := hqforall act (by simp)
                simpa [hact] using this
              obtain ⟨calls, hcalls, hfilter⟩ := ih hA' hB'
              by_cases htoB : to_addr = caddrB
              · subst to_addr
                rw [hB'] at hcontract
                cases hcontract
                obtain ⟨ps, ms, ns, hps, hms, hns, hrec⟩ :=
                  wc_receive_strong (contract := contract) hreceive
                cases ms with
                | none =>
                    subst msg
                    refine ⟨{ call_origin := origin, call_from := from_addr,
                              call_amount := amount, call_msg := none } :: calls, ?_, ?_⟩
                    · simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                        Address.address_eq_refl]
                    · simp [callFrom, hfrom_ne, hfilter]
                | some m =>
                    cases msg with
                    | none => cases hms
                    | some ser =>
                        have hdes : (deserialize ser : Option Msg) = some m := by
                          simpa using hms
                        refine ⟨{ call_origin := origin, call_from := from_addr,
                                  call_amount := amount, call_msg := some m } :: calls, ?_, ?_⟩
                        · simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                            Address.address_eq_refl, hdes]
                        · simp [callFrom, hfrom_ne, hfilter]
              · refine ⟨calls, ?_, hfilter⟩
                simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                  Address.address_eq_ne _ _ htoB]
      | step_action_invalid act acts henv hq hqnext hfrom hno =>
          have hA' : mid.env_contracts caddrA = none := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contract) := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          obtain ⟨calls, hcalls, hfilter⟩ := ih hA' hB'
          exact ⟨calls, by simp [incoming_calls, step_incoming_calls, hcalls], hfilter⟩
      | step_permute henv hperm =>
          have hA' : mid.env_contracts caddrA = none := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contract) := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          obtain ⟨calls, hcalls, hfilter⟩ := ih hA' hB'
          exact ⟨calls, by simp [incoming_calls, step_incoming_calls, hcalls], hfilter⟩

def contract_call_info_to_tx
    {X : Type} [Serializable X]
    (caddr : Base.Address) (ci : @ContractCallInfo Base X) : @Tx Base :=
  let body : @TxBody Base :=
    match ci.call_msg with
    | some msg => .tx_call (some (serialize msg))
    | none => .tx_call none
  { tx_origin := ci.call_origin,
    tx_from := ci.call_from,
    tx_to := caddr,
    tx_amount := ci.call_amount,
    tx_body := body }

def tx_to_contract_call_info
    {X : Type} [Serializable X] (tx : @Tx Base) : Option (@ContractCallInfo Base X) :=
  match tx.tx_body with
  | .tx_call none =>
      some { call_origin := tx.tx_origin, call_from := tx.tx_from,
             call_amount := tx.tx_amount, call_msg := none }
  | .tx_call (some m) =>
      some { call_origin := tx.tx_origin, call_from := tx.tx_from,
             call_amount := tx.tx_amount,
             call_msg := (deserialize m : Option X) }
  | _ => none

theorem incomming_eq_outgoing :
  ∀ (bstate : @ChainState Base) (caddrA caddrB : Base.Address)
    (trace : ChainTrace empty_state bstate)
    {SetupA MsgA StateA ErrorA : Type}
    {SetupB MsgB StateB ErrorB : Type}
    [Serializable SetupA] [Serializable SetupB]
    [Serializable MsgA] [Serializable MsgB]
    [Serializable StateA] [Serializable StateB]
    [Serializable ErrorA] [Serializable ErrorB]
    {contractA : Contract SetupA MsgA StateA ErrorA}
    {contractB : Contract SetupB MsgB StateB ErrorB},
    (∀ (x : SerializedValue) (y : MsgB), (deserialize x : Option MsgB) = some y → x = serialize y) →
    bstate.env_contracts caddrA = some (contract_to_weak_contract contractA) →
    bstate.env_contracts caddrB = some (contract_to_weak_contract contractB) →
    ∃ inc_calls,
      incoming_calls MsgB trace caddrB = some inc_calls ∧
      (outgoing_txs trace caddrA).filter (txCallTo caddrB) =
        (inc_calls.filter (callFrom caddrA)).map (contract_call_info_to_tx caddrB) := by
  intros bstate caddrA caddrB trace SetupA MsgA StateA ErrorA SetupB MsgB StateB ErrorB
    _ _ _ _ _ _ _ _ contractA contractB hdeserialize hA hB
  induction trace with
  | clnil =>
      cases hA
  | @snoc mid next tail step ih =>
      cases step with
      | step_block hdr hq hvalid hfrom horigin henv =>
          have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contractA) := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contractB) := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          obtain ⟨calls, hcalls, heq⟩ := ih hA' hB'
          exact ⟨calls,
            by simp [incoming_calls, step_incoming_calls, hcalls],
            by simpa [outgoing_txs, trace_txs, step_txs] using heq⟩
      | step_action act acts new_acts hq eval hqnext =>
          cases eval with
          | eval_transfer origin from_addr to_addr amount hnonneg hbal hnot_contract hact henv hnew =>
              have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contractA) := by
                rw [henv.contracts_eq caddrA] at hA
                exact hA
              have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contractB) := by
                rw [henv.contracts_eq caddrB] at hB
                exact hB
              obtain ⟨calls, hcalls, heq⟩ := ih hA' hB'
              exact ⟨calls,
                by simp [incoming_calls, step_incoming_calls, eval_tx, hcalls],
                by simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo] using heq⟩
          | eval_deploy origin from_addr to_addr amount wc setup state
              hnonneg hbal his_contract hnone hact hinit henv hnew =>
              by_cases htoA : to_addr = caddrA
              · subst to_addr
                have hout : outgoing_txs tail caddrA = [] :=
                  undeployed_contract_no_out_txs caddrA tail his_contract hnone
                by_cases hAB : caddrA = caddrB
                · subst caddrB
                  have hin : incoming_calls MsgB tail caddrA = some [] :=
                    undeployed_contract_no_in_calls caddrA tail his_contract hnone
                  refine ⟨[], ?_, ?_⟩
                  · simp [incoming_calls, step_incoming_calls, eval_tx, hin]
                  · simp [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo]
                    intro tx hmem _hcall
                    exact Bool.eq_false_of_not_eq_true (fun hf => by
                      have hmem' : tx ∈ outgoing_txs tail caddrA := by
                        simp [outgoing_txs, hmem, hf]
                      rw [hout] at hmem'
                      cases hmem')
                · have hB' : mid.env_contracts caddrB =
                      some (contract_to_weak_contract contractB) := by
                    rw [henv.contracts_eq caddrB] at hB
                    simpa [add_contract, set_contract_state,
                      Address.address_eq_ne caddrB caddrA (Ne.symm hAB)] using hB
                  obtain ⟨calls, hcalls, hfilter⟩ :=
                    no_incoming_calls_from_undeployed_contract
                      mid caddrA caddrB tail hnone his_contract hB'
                  refine ⟨calls, ?_, ?_⟩
                  · simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                      Address.address_eq_ne caddrA caddrB hAB]
                  · simp [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo, hfilter]
                    intro tx hmem hcall
                    exact Bool.eq_false_of_not_eq_true (fun hf => by
                      have hmem' : tx ∈ (outgoing_txs tail caddrA).filter (txCallTo caddrB) := by
                        simp [outgoing_txs, txCallTo, hmem, hf, hcall]
                      rw [hout] at hmem'
                      cases hmem')
              · have hA' : mid.env_contracts caddrA =
                    some (contract_to_weak_contract contractA) := by
                  rw [henv.contracts_eq caddrA] at hA
                  simpa [add_contract, set_contract_state,
                    Address.address_eq_ne caddrA to_addr (Ne.symm htoA)] using hA
                by_cases htoB : to_addr = caddrB
                · subst to_addr
                  have hin : incoming_calls MsgB tail caddrB = some [] :=
                    undeployed_contract_no_in_calls caddrB tail his_contract hnone
                  have hout :
                      (outgoing_txs tail caddrA).filter (txCallTo caddrB) = [] :=
                    no_outgoing_txs_to_undeployed_contract
                      mid caddrA caddrB tail hA' hnone
                  refine ⟨[], ?_, ?_⟩
                  · simp [incoming_calls, step_incoming_calls, eval_tx, hin]
                  · simp [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo]
                    intro tx hmem hcall
                    exact Bool.eq_false_of_not_eq_true (fun hf => by
                      have hmem' : tx ∈ (outgoing_txs tail caddrA).filter (txCallTo caddrB) := by
                        simp [outgoing_txs, txCallTo, hmem, hf, hcall]
                      rw [hout] at hmem'
                      cases hmem')
                · have hB' : mid.env_contracts caddrB =
                      some (contract_to_weak_contract contractB) := by
                    rw [henv.contracts_eq caddrB] at hB
                    simpa [add_contract, set_contract_state,
                      Address.address_eq_ne caddrB to_addr (Ne.symm htoB)] using hB
                  obtain ⟨calls, hcalls, heq⟩ := ih hA' hB'
                  exact ⟨calls,
                    by simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                      Address.address_eq_ne to_addr caddrB htoB],
                    by simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo] using heq⟩
          | eval_call origin from_addr to_addr amount wc msg prev_state new_state resp_acts
              hnonneg hbal hcontract hstate hact hreceive hnew henv =>
              have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contractA) := by
                rw [henv.contracts_eq caddrA] at hA
                exact hA
              have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contractB) := by
                rw [henv.contracts_eq caddrB] at hB
                exact hB
              obtain ⟨calls, hcalls, heq⟩ := ih hA' hB'
              by_cases htoB : to_addr = caddrB
              · subst to_addr
                rw [hB'] at hcontract
                cases hcontract
                obtain ⟨ps, ms, ns, hps, hms, hns, hrec⟩ :=
                  wc_receive_strong (contract := contractB) hreceive
                by_cases hfromA : from_addr = caddrA
                · subst from_addr
                  cases ms with
                  | none =>
                      subst msg
                      refine ⟨{ call_origin := origin, call_from := caddrA,
                                call_amount := amount, call_msg := none } :: calls, ?_, ?_⟩
                      · simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                          Address.address_eq_refl]
                      · simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo,
                          callFrom, contract_call_info_to_tx, Address.address_eq_refl] using heq
                  | some m =>
                      cases msg with
                      | none => cases hms
                      | some ser =>
                          have hdes : (deserialize ser : Option MsgB) = some m := by
                            simpa using hms
                          refine ⟨{ call_origin := origin, call_from := caddrA,
                                    call_amount := amount, call_msg := some m } :: calls, ?_, ?_⟩
                          · simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                              Address.address_eq_refl, hdes]
                          · have hser : ser = serialize m := hdeserialize ser m hdes
                            simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo,
                              callFrom, contract_call_info_to_tx, Address.address_eq_refl,
                              hser] using heq
                · cases ms with
                  | none =>
                      subst msg
                      refine ⟨{ call_origin := origin, call_from := from_addr,
                                call_amount := amount, call_msg := none } :: calls, ?_, ?_⟩
                      · simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                          Address.address_eq_refl]
                      · simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo,
                          callFrom, Address.address_eq_ne from_addr caddrA hfromA] using heq
                  | some m =>
                      cases msg with
                      | none => cases hms
                      | some ser =>
                          have hdes : (deserialize ser : Option MsgB) = some m := by
                            simpa using hms
                          refine ⟨{ call_origin := origin, call_from := from_addr,
                                    call_amount := amount, call_msg := some m } :: calls, ?_, ?_⟩
                          · simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                              Address.address_eq_refl, hdes]
                          · simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo,
                              callFrom, Address.address_eq_ne from_addr caddrA hfromA] using heq
              · refine ⟨calls, ?_, ?_⟩
                · simp [incoming_calls, step_incoming_calls, eval_tx, hcalls,
                    Address.address_eq_ne to_addr caddrB htoB]
                · simpa [outgoing_txs, trace_txs, step_txs, eval_tx, txCallTo,
                    Address.address_eq_ne to_addr caddrB htoB] using heq
      | step_action_invalid act acts henv hq hqnext hfrom hno =>
          have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contractA) := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contractB) := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          obtain ⟨calls, hcalls, heq⟩ := ih hA' hB'
          exact ⟨calls,
            by simp [incoming_calls, step_incoming_calls, hcalls],
            by simpa [outgoing_txs, trace_txs, step_txs] using heq⟩
      | step_permute henv hperm =>
          have hA' : mid.env_contracts caddrA = some (contract_to_weak_contract contractA) := by
            rw [henv.contracts_eq caddrA] at hA
            exact hA
          have hB' : mid.env_contracts caddrB = some (contract_to_weak_contract contractB) := by
            rw [henv.contracts_eq caddrB] at hB
            exact hB
          obtain ⟨calls, hcalls, heq⟩ := ih hA' hB'
          exact ⟨calls,
            by simp [incoming_calls, step_incoming_calls, hcalls],
            by simpa [outgoing_txs, trace_txs, step_txs] using heq⟩

end ConCert.Execution.InterContractCommunication
