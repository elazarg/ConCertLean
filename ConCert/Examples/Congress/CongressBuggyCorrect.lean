/- Bug-witness facts for the buggy Congress variant. -/

import ConCert.Examples.Congress.Congress

namespace ConCert.Examples.Congress

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

namespace Buggy

def num_acts_created_in_proposals
    (calls : List (@ContractCallInfo Base (@Msg Base))) : Nat :=
  (calls.map (fun call => nr_cacts call.call_msg)).sum

theorem do_finish_proposal_appends_self_call
    {ctx : @ContractCallContext Base} {pid : ProposalId}
    {state : @State Base} {chain : Chain} {proposal : @Proposal Base}
    (hfind : FMap.find pid state.proposals = some proposal)
    (hdeadline :
      proposal.proposed_in + state.state_rules.debating_period_in_blocks ≤
        chain.current_slot)
    (hpassed : proposal_passed proposal state = true) :
    do_finish_proposal ctx pid state chain =
      .Ok
        (state,
          proposal.actions.map congress_action_to_chain_action ++
            [ActionBody.act_call ctx.ctx_contract_address 0
              (serialize (Msg.finish_proposal_remove pid))]) := by
  unfold do_finish_proposal
  rw [hfind]
  simp
  rw [if_neg (not_lt.mpr hdeadline), hpassed]
  rfl

theorem do_finish_proposal_violates_action_conservation
    {ctx : @ContractCallContext Base} {pid : ProposalId}
    {state : @State Base} {chain : Chain} {proposal : @Proposal Base}
    (hfind : FMap.find pid state.proposals = some proposal)
    (hdeadline :
      proposal.proposed_in + state.state_rules.debating_period_in_blocks ≤
        chain.current_slot)
    (hpassed : proposal_passed proposal state = true) :
    ∃ new_acts,
      do_finish_proposal ctx pid state chain = .Ok (state, new_acts) ∧
      receive_state_well_behaved state (some (Msg.finish_proposal pid))
        state new_acts = false := by
  let new_acts :=
    proposal.actions.map congress_action_to_chain_action ++
      [ActionBody.act_call ctx.ctx_contract_address 0
        (serialize (Msg.finish_proposal_remove pid))]
  refine ⟨new_acts, ?_, ?_⟩
  · exact do_finish_proposal_appends_self_call hfind hdeadline hpassed
  · unfold new_acts
    unfold receive_state_well_behaved nr_cacts
    simp

theorem do_finish_proposal_keeps_proposal
    {ctx : @ContractCallContext Base} {pid : ProposalId}
    {state new_state : @State Base} {chain : Chain}
    {new_acts : List (@ActionBody Base)}
    (h : do_finish_proposal ctx pid state chain =
      .Ok (new_state, new_acts)) :
    new_state = state := by
  unfold do_finish_proposal at h
  cases hfind : FMap.find pid state.proposals with
  | none =>
      simp [hfind] at h
  | some proposal =>
      simp [hfind] at h
      by_cases hdeadline :
          chain.current_slot <
            proposal.proposed_in +
              state.state_rules.debating_period_in_blocks
      · simp [hdeadline] at h
      · simp [hdeadline] at h
        split at h <;> cases h <;> (symm; assumption)

end Buggy

end ConCert.Examples.Congress
