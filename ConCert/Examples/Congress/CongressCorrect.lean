/- Port of examples/congress/CongressCorrect.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.BlockchainBuilder
import ConCert.Execution.BlockchainInduction
import ConCert.Execution.BlockchainTheories
import ConCert.Execution.Containers
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Examples.Congress.Congress
import ConCert.Utils.Automation
import ConCert.Utils.Extras
import Mathlib.Tactic.Linarith

namespace ConCert.Examples.Congress

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainBuilder
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

def num_acts_created_in_proposals
    (calls : List (@ContractCallInfo Base (@Msg Base))) : Nat :=
  (calls.map (fun call => nr_cacts call.call_msg)).sum

omit Base in
private theorem sum_map_perm {α : Type} (f : α → Nat) {xs ys : List α}
    (h : xs.Perm ys) :
    (xs.map f).sum = (ys.map f).sum := by
  simpa [List.sum_eq_foldr] using
    (List.Perm.foldr_op_eq
      (op := fun x y : Nat => x + y)
      (a := 0)
      (h.map f))

private def proposals_cacts (props : FMap Nat (@Proposal Base)) : Nat :=
  ((FMap.elements props).map
    (fun p : Nat × @Proposal Base => p.2.actions.length)).sum

private theorem proposals_cacts_eq_num (state : @State Base) :
    proposals_cacts state.proposals = num_cacts_in_state state := rfl

private theorem proposals_cacts_add_new
    (pid : ProposalId) (proposal : @Proposal Base)
    (props : FMap Nat (@Proposal Base))
    (hfind : FMap.find pid props = none) :
    proposals_cacts (FMap.add pid proposal props) =
      proposal.actions.length + proposals_cacts props := by
  unfold proposals_cacts
  have hperm := FMap.elements_add pid proposal props hfind
  have hsum := sum_map_perm (fun p : Nat × @Proposal Base => p.2.actions.length) hperm
  simpa using hsum

private theorem proposals_cacts_add_existing
    (pid : ProposalId) (oldProposal newProposal : @Proposal Base)
    (props : FMap Nat (@Proposal Base))
    (hfind : FMap.find pid props = some oldProposal) :
    proposals_cacts (FMap.add pid newProposal props) =
      newProposal.actions.length + proposals_cacts (FMap.remove pid props) := by
  unfold proposals_cacts
  have hperm := FMap.elements_add_existing pid oldProposal newProposal props hfind
  have hsum := sum_map_perm (fun p : Nat × @Proposal Base => p.2.actions.length) hperm
  simpa using hsum

private theorem proposals_cacts_existing
    (pid : ProposalId) (proposal : @Proposal Base)
    (props : FMap Nat (@Proposal Base))
    (hfind : FMap.find pid props = some proposal) :
    proposals_cacts props =
      proposal.actions.length + proposals_cacts (FMap.remove pid props) := by
  have hadd :=
    proposals_cacts_add_existing pid proposal proposal props hfind
  have hid : FMap.add pid proposal props = props := FMap.add_id pid proposal props hfind
  rwa [hid] at hadd

private theorem vote_on_proposal_state_rules
    (addr : Base.Address) (pid : ProposalId) (vote_val : Int)
    (state new_state : @State Base) :
    vote_on_proposal addr pid vote_val state = .Ok new_state →
    new_state.state_rules = state.state_rules := by
  intro hvote
  unfold vote_on_proposal at hvote
  cases hfind : FMap.find pid state.proposals with
  | none =>
      simp [hfind] at hvote
  | some proposal =>
      simp [hfind] at hvote
      cases hvote
      rfl

private theorem do_retract_vote_state_rules
    (addr : Base.Address) (pid : ProposalId)
    (state new_state : @State Base) :
    do_retract_vote addr pid state = .Ok new_state →
    new_state.state_rules = state.state_rules := by
  intro hretract
  unfold do_retract_vote at hretract
  cases hfind : FMap.find pid state.proposals with
  | none =>
      simp [hfind] at hretract
  | some proposal =>
      simp [hfind] at hretract
      cases hvote : FMap.find addr proposal.votes with
      | none =>
          simp [hvote] at hretract
      | some old_vote =>
          simp [hvote] at hretract
          cases hretract
          rfl

theorem rules_valid (bstate : @ChainState Base) (caddr : Base.Address) :
    reachable bstate →
    bstate.env_contracts caddr =
      some (contract_to_weak_contract (contract : @Contract Base _ _ _ _ _ _ _ _)) →
    ∃ cstate : @State Base,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr = some cstate ∧
      validate_rules cstate.state_rules = true := by
  intro hreach hcontract
  exact
    lift_contract_state_prop
      (Q := fun cstate : @State Base => validate_rules cstate.state_rules = true)
      (contract : @Contract Base _ _ _ _ _ _ _ _)
      bstate caddr
      (by
        intro chain ctx setup result hinit
        unfold contract init at hinit
        simp only at hinit
        by_cases hvalid : validate_rules setup.setup_rules = true
        · rw [if_pos hvalid] at hinit
          cases hinit
          exact hvalid
        · rw [if_neg hvalid] at hinit
          cases hinit)
      (by
        intro chain ctx cstate msg new_cstate acts hprev hreceive
        cases howner : Base.address_eqb ctx.ctx_from cstate.owner <;>
          cases hmember : FMap.mem ctx.ctx_from cstate.members <;>
          cases msg with
          | none =>
              simp [contract, receive] at hreceive
              cases hreceive
              subst_vars
              exact hprev
          | some msg' =>
              cases msg' with
              | transfer_ownership new_owner =>
                  simp [contract, receive, howner, hmember] at hreceive
                  all_goals
                    cases hreceive
                    subst_vars
                    simpa using hprev
              | change_rules new_rules =>
                  simp [contract, receive, howner, hmember] at hreceive
                  all_goals
                    by_cases hvalid : validate_rules new_rules = true
                    · simp [hvalid] at hreceive
                      all_goals
                        cases hreceive
                        subst_vars
                        exact hvalid
                    · simp [hvalid] at hreceive
              | add_member new_member =>
                  simp [contract, receive, howner, hmember] at hreceive
                  all_goals
                    cases hreceive
                    subst_vars
                    simpa using hprev
              | remove_member old_member =>
                  simp [contract, receive, howner, hmember] at hreceive
                  all_goals
                    cases hreceive
                    subst_vars
                    simpa using hprev
              | create_proposal actions =>
                  simp [contract, receive, howner, hmember] at hreceive
                  all_goals
                    cases hreceive
                    subst_vars
                    simpa [add_proposal] using hprev
              | vote_for_proposal pid =>
                  simp [contract, receive, howner, hmember, without_actions] at hreceive
                  all_goals
                    cases hvote : vote_on_proposal ctx.ctx_from pid 1 cstate with
                    | Err e =>
                        rw [hvote] at hreceive
                        cases hreceive
                    | Ok stateNew =>
                        rw [hvote] at hreceive
                        cases hreceive
                        rw [vote_on_proposal_state_rules
                          ctx.ctx_from pid 1 cstate new_cstate hvote]
                        exact hprev
              | vote_against_proposal pid =>
                  simp [contract, receive, howner, hmember, without_actions] at hreceive
                  all_goals
                    cases hvote : vote_on_proposal ctx.ctx_from pid (-1) cstate with
                    | Err e =>
                        rw [hvote] at hreceive
                        cases hreceive
                    | Ok stateNew =>
                        rw [hvote] at hreceive
                        cases hreceive
                        rw [vote_on_proposal_state_rules
                          ctx.ctx_from pid (-1) cstate new_cstate hvote]
                        exact hprev
              | retract_vote pid =>
                  simp [contract, receive, howner, hmember, without_actions] at hreceive
                  all_goals
                    cases hretract : do_retract_vote ctx.ctx_from pid cstate with
                    | Err e =>
                        rw [hretract] at hreceive
                        cases hreceive
                    | Ok stateNew =>
                        rw [hretract] at hreceive
                        cases hreceive
                        rw [do_retract_vote_state_rules
                          ctx.ctx_from pid cstate new_cstate hretract]
                        exact hprev
              | finish_proposal pid =>
                  simp [contract, receive, do_finish_proposal] at hreceive
                  cases hfind : FMap.find pid cstate.proposals with
                  | none =>
                      simp [hfind] at hreceive
                  | some proposal =>
                      simp [hfind] at hreceive
                      by_cases hslot :
                          chain.current_slot <
                            proposal.proposed_in +
                              cstate.state_rules.debating_period_in_blocks
                      · simp [hslot] at hreceive
                      · simp [hslot] at hreceive
                        cases hreceive
                        subst_vars
                        simpa using hprev)
      hreach hcontract

theorem num_cacts_in_state_deployment
    (chain : Chain) (ctx : @ContractCallContext Base) (setup : Setup)
    (state : @State Base) :
    init chain ctx setup = .Ok state →
    num_cacts_in_state state = 0 := by
  intro hinit
  unfold init at hinit
  by_cases hvalid : validate_rules setup.setup_rules = true
  · rw [if_pos hvalid] at hinit
    cases hinit
    simp [num_cacts_in_state, FMap.elements_empty]
  · rw [if_neg hvalid] at hinit
    cases hinit

theorem add_proposal_cacts
    (cacts : List (@CongressAction Base)) (chain : Chain)
    (state : @State Base) :
    num_cacts_in_state (add_proposal cacts chain state) ≤
      num_cacts_in_state state + cacts.length := by
  unfold add_proposal
  dsimp only
  change proposals_cacts (FMap.add state.next_proposal_id
      ({ actions := cacts, votes := FMap.empty, vote_result := 0,
         proposed_in := chain.current_slot } : @Proposal Base)
      state.proposals) ≤
    proposals_cacts state.proposals + cacts.length
  cases hfind : FMap.find state.next_proposal_id state.proposals with
  | none =>
      rw [proposals_cacts_add_new _ _ _ hfind]
      simp
      omega
  | some oldProposal =>
      rw [proposals_cacts_add_existing _ oldProposal _ _ hfind]
      rw [proposals_cacts_existing _ oldProposal _ hfind]
      simp
      omega

theorem vote_on_proposal_cacts_preserved
    (addr : Base.Address) (pid : ProposalId) (vote_val : Int)
    (state new_state : @State Base) :
    vote_on_proposal addr pid vote_val state = .Ok new_state →
    num_cacts_in_state new_state = num_cacts_in_state state := by
  intro hvote
  unfold vote_on_proposal at hvote
  cases hfind : FMap.find pid state.proposals with
  | none =>
      rw [hfind] at hvote
      cases hvote
  | some proposal =>
      rw [hfind] at hvote
      cases hvote
      change proposals_cacts (FMap.add pid
          ({ proposal with
             votes := FMap.add addr vote_val proposal.votes,
             vote_result :=
               proposal.vote_result -
                 (FMap.find addr proposal.votes).getD 0 + vote_val } : @Proposal Base)
          state.proposals) =
        proposals_cacts state.proposals
      rw [proposals_cacts_add_existing _ proposal _ _ hfind]
      rw [proposals_cacts_existing _ proposal _ hfind]

theorem do_retract_vote_cacts_preserved
    (addr : Base.Address) (pid : ProposalId)
    (state new_state : @State Base) :
    do_retract_vote addr pid state = .Ok new_state →
    num_cacts_in_state new_state = num_cacts_in_state state := by
  intro hretract
  unfold do_retract_vote at hretract
  cases hfind : FMap.find pid state.proposals with
  | none =>
      rw [hfind] at hretract
      cases hretract
  | some proposal =>
      rw [hfind] at hretract
      cases hvote : FMap.find addr proposal.votes with
      | none =>
          simp [hvote] at hretract
      | some old_vote =>
          simp [hvote] at hretract
          cases hretract
          change proposals_cacts (FMap.add pid
              ({ proposal with
                 votes := FMap.remove addr proposal.votes,
                 vote_result := proposal.vote_result - old_vote } : @Proposal Base)
              state.proposals) =
            proposals_cacts state.proposals
          rw [proposals_cacts_add_existing _ proposal _ _ hfind]
          rw [proposals_cacts_existing _ proposal _ hfind]

theorem remove_proposal_cacts
    (pid : ProposalId) (state : @State Base) (proposal : @Proposal Base) :
    FMap.find pid state.proposals = some proposal →
    num_cacts_in_state { state with proposals := FMap.remove pid state.proposals } +
      proposal.actions.length =
      num_cacts_in_state state := by
  intro hfind
  change proposals_cacts (FMap.remove pid state.proposals) +
      proposal.actions.length =
    proposals_cacts state.proposals
  rw [proposals_cacts_existing _ proposal _ hfind]
  omega

theorem receive_state_well_behaved_correct
    (chain : Chain) (ctx : @ContractCallContext Base) (state : @State Base)
    (msg : Option (@Msg Base)) (new_state : @State Base)
    (resp_acts : List (@ActionBody Base)) :
    receive chain ctx state msg = .Ok (new_state, resp_acts) →
    num_cacts_in_state new_state + resp_acts.length ≤
      num_cacts_in_state state + nr_cacts msg := by
  intro hreceive
  cases howner : Base.address_eqb ctx.ctx_from state.owner <;>
    cases hmember : FMap.mem ctx.ctx_from state.members <;>
    cases msg with
    | none =>
        simp [receive] at hreceive
        cases hreceive
        subst_vars
        simp [nr_cacts]
    | some msg' =>
        cases msg' with
        | transfer_ownership new_owner =>
            simp [receive, howner, hmember] at hreceive
            all_goals
              cases hreceive
              subst_vars
              simp [num_cacts_in_state, nr_cacts]
        | change_rules new_rules =>
            simp [receive, howner, hmember] at hreceive
            all_goals
              by_cases hvalid : validate_rules new_rules = true
              · simp [hvalid] at hreceive
                all_goals
                  cases hreceive
                  subst_vars
                  simp [num_cacts_in_state, nr_cacts]
              · simp [hvalid] at hreceive
        | add_member new_member =>
            simp [receive, howner, hmember] at hreceive
            all_goals
              cases hreceive
              subst_vars
              simp [num_cacts_in_state, nr_cacts]
        | remove_member old_member =>
            simp [receive, howner, hmember] at hreceive
            all_goals
              cases hreceive
              subst_vars
              simp [num_cacts_in_state, nr_cacts]
        | create_proposal actions =>
            simp [receive, howner, hmember] at hreceive
            all_goals
              cases hreceive
              subst_vars
              simpa [nr_cacts] using add_proposal_cacts actions chain state
        | vote_for_proposal pid =>
            simp [receive, howner, hmember, without_actions] at hreceive
            all_goals
              cases hvote : vote_on_proposal ctx.ctx_from pid 1 state with
              | Err e =>
                  rw [hvote] at hreceive
                  cases hreceive
              | Ok stateNew =>
                  rw [hvote] at hreceive
                  cases hreceive
                  have hpres := vote_on_proposal_cacts_preserved
                    ctx.ctx_from pid 1 state new_state hvote
                  rw [hpres]
                  simp [nr_cacts]
        | vote_against_proposal pid =>
            simp [receive, howner, hmember, without_actions] at hreceive
            all_goals
              cases hvote : vote_on_proposal ctx.ctx_from pid (-1) state with
              | Err e =>
                  rw [hvote] at hreceive
                  cases hreceive
              | Ok stateNew =>
                  rw [hvote] at hreceive
                  cases hreceive
                  have hpres := vote_on_proposal_cacts_preserved
                    ctx.ctx_from pid (-1) state new_state hvote
                  rw [hpres]
                  simp [nr_cacts]
        | retract_vote pid =>
            simp [receive, howner, hmember, without_actions] at hreceive
            all_goals
              cases hretract : do_retract_vote ctx.ctx_from pid state with
              | Err e =>
                  rw [hretract] at hreceive
                  cases hreceive
              | Ok stateNew =>
                  rw [hretract] at hreceive
                  cases hreceive
                  have hpres := do_retract_vote_cacts_preserved
                    ctx.ctx_from pid state new_state hretract
                  rw [hpres]
                  simp [nr_cacts]
        | finish_proposal pid =>
            simp [receive, do_finish_proposal] at hreceive
            cases hfind : FMap.find pid state.proposals with
            | none =>
                simp [hfind] at hreceive
            | some proposal =>
                simp [hfind] at hreceive
                by_cases hslot :
                    chain.current_slot <
                      proposal.proposed_in +
                        state.state_rules.debating_period_in_blocks
                · simp [hslot] at hreceive
                · simp [hslot] at hreceive
                  cases hreceive
                  subst_vars
                  have hremove := remove_proposal_cacts pid state proposal hfind
                  by_cases hpassed : proposal_passed proposal state = true
                  · simp [hpassed] at hremove ⊢
                    omega
                  · simp [hpassed] at hremove ⊢
                    omega

theorem congress_correct
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate) :
    bstate.env_contracts caddr =
      some (contract_to_weak_contract (contract : @Contract Base _ _ _ _ _ _ _ _)) →
    ∃ (cstate : @State Base) (inc_calls : List (@ContractCallInfo Base (@Msg Base))),
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr = some cstate ∧
      incoming_calls (@Msg Base) trace caddr = some inc_calls ∧
      num_cacts_in_state cstate +
        (outgoing_txs trace caddr).length +
        (outgoing_acts bstate caddr).length ≤
      num_acts_created_in_proposals inc_calls := by
  intro hdeployed
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
      @State Base → Amount → List (@ActionBody Base) →
      List (@ContractCallInfo Base (@Msg Base)) → List (@Tx Base) → Prop :=
    fun _ _ _ _ _ cstate _ out_queue inc_calls out_txs =>
      num_cacts_in_state cstate + out_txs.length + out_queue.length ≤
        num_acts_created_in_proposals inc_calls
  have hcases : ContractInductionCases
      (contract : @Contract Base _ _ _ _ _ _ _ _)
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
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _
      exact ih
    · intro chain ctx setup result _ hinit _
      have hzero := num_cacts_in_state_deployment chain ctx setup result hinit
      dsimp [P]
      rw [hzero]
      simp [num_acts_created_in_proposals]
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
      dsimp [P] at ih ⊢
      simp at ih ⊢
      omega
    · intro chain ctx dep_info prev_state msg prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts _ _ ih hreceive _
      dsimp [P] at ih ⊢
      have hrecv := receive_state_well_behaved_correct
        chain ctx prev_state msg new_state new_acts hreceive
      simp only [num_acts_created_in_proposals, List.map_cons, List.sum_cons,
        List.length_append] at ih ⊢
      omega
    · intro chain ctx dep_info prev_state msg head prev_out_queue prev_inc_calls
        prev_out_txs new_state new_acts _ _ ih _ hreceive _
      dsimp [P] at ih ⊢
      have hrecv := receive_state_well_behaved_correct
        chain ctx prev_state msg new_state new_acts hreceive
      simp only [num_acts_created_in_proposals, List.map_cons, List.sum_cons,
        List.length_append] at ih ⊢
      omega
    · intro _ _ _ _ _ _ _ out_queue inc_calls out_txs out_queue' ih hperm _
      dsimp [P] at ih ⊢
      have hlen : out_queue'.length = out_queue.length := hperm.length_eq.symm
      simpa [hlen] using ih
  obtain ⟨_, cstate, inc_calls, _, hstate, hcalls, hP⟩ :=
    contract_induction
      (contract : @Contract Base _ _ _ _ _ _ _ _)
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True)
      P hcases bstate caddr trace hdeployed
  exact ⟨cstate, inc_calls, hstate, hcalls, hP⟩

theorem congress_correct_after_block
    {Cb : @ChainBuilderType Base} (prev new : Cb.builder_type)
    (header : @BlockHeader Base) (acts : List (@Action Base)) :
    Cb.builder_add_block prev header acts = .Ok new →
    ∀ caddr : Base.Address,
      (Cb.builder_env new).env_contracts caddr =
        some (contract_to_weak_contract (contract : @Contract Base _ _ _ _ _ _ _ _)) →
      ∃ inc_calls : List (@ContractCallInfo Base (@Msg Base)),
        incoming_calls (@Msg Base) (Cb.builder_trace new) caddr = some inc_calls ∧
        (outgoing_txs (Cb.builder_trace new) caddr).length ≤
          num_acts_created_in_proposals inc_calls := by
  intro _ caddr hdeployed
  let bstate : @ChainState Base :=
    { toEnvironment := Cb.builder_env new, chain_state_queue := [] }
  have hgeneral := congress_correct bstate caddr (Cb.builder_trace new) hdeployed
  obtain ⟨cstate, inc_calls, hstate, hcalls, hbound⟩ := hgeneral
  refine ⟨inc_calls, hcalls, ?_⟩
  simp [bstate, outgoing_acts] at hbound
  omega

end ConCert.Examples.Congress
