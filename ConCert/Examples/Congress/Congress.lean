/- Port of examples/congress/Congress.v and the executable part of
examples/congress/Congress_Buggy.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Utils.Extras

namespace ConCert.Examples.Congress

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

abbrev ProposalId : Type := Nat

inductive CongressAction where
  | cact_transfer (to_ : Base.Address) (amount : Amount)
  | cact_call (to_ : Base.Address) (amount : Amount) (msg : SerializedValue)
  deriving DecidableEq, Serializable

structure Proposal where
  actions : List (@CongressAction Base)
  votes : FMap Base.Address Int
  vote_result : Int
  proposed_in : Nat
  deriving Serializable

structure Rules where
  min_vote_count_permille : Int
  margin_needed_permille : Int
  debating_period_in_blocks : Nat
  deriving DecidableEq, Serializable

structure Setup where
  setup_rules : Rules
  deriving DecidableEq, Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

inductive Msg where
  | transfer_ownership (new_owner : Base.Address)
  | change_rules (new_rules : Rules)
  | add_member (new_member : Base.Address)
  | remove_member (old_member : Base.Address)
  | create_proposal (actions : List (@CongressAction Base))
  | vote_for_proposal (pid : ProposalId)
  | vote_against_proposal (pid : ProposalId)
  | retract_vote (pid : ProposalId)
  | finish_proposal (pid : ProposalId)
  deriving DecidableEq, Serializable

structure State where
  owner : Base.Address
  state_rules : Rules
  proposals : FMap Nat (@Proposal Base)
  next_proposal_id : ProposalId
  members : FMap Base.Address Unit
  deriving Serializable

def validate_rules (rules : Rules) : Bool :=
  decide (0 ≤ rules.min_vote_count_permille) &&
    decide (rules.min_vote_count_permille ≤ 1000) &&
    decide (0 ≤ rules.margin_needed_permille) &&
    decide (rules.margin_needed_permille ≤ 1000)

def init (_chain : Chain) (ctx : @ContractCallContext Base) (setup : Setup) :
    Result (@State Base) Error :=
  if validate_rules setup.setup_rules then
    .Ok
      { owner := ctx.ctx_from,
        state_rules := setup.setup_rules,
        proposals := FMap.empty,
        next_proposal_id := 1,
        members := FMap.empty }
  else
    .Err default_error

def add_proposal
    (actions : List (@CongressAction Base)) (chain : Chain)
    (state : @State Base) : @State Base :=
  let id := state.next_proposal_id
  let proposal : @Proposal Base :=
    { actions := actions,
      votes := FMap.empty,
      vote_result := 0,
      proposed_in := chain.current_slot }
  { state with
    proposals := FMap.add id proposal state.proposals,
    next_proposal_id := state.next_proposal_id + 1 }

def vote_on_proposal
    (voter : Base.Address) (pid : ProposalId) (vote : Int)
    (state : @State Base) : Result (@State Base) Error :=
  match FMap.find pid state.proposals with
  | none => .Err default_error
  | some proposal =>
      let old_vote := (FMap.find voter proposal.votes).getD 0
      let new_votes := FMap.add voter vote proposal.votes
      let new_vote_result := proposal.vote_result - old_vote + vote
      let new_proposal :=
        { proposal with votes := new_votes, vote_result := new_vote_result }
      .Ok { state with proposals := FMap.add pid new_proposal state.proposals }

def do_retract_vote
    (voter : Base.Address) (pid : ProposalId)
    (state : @State Base) : Result (@State Base) Error :=
  match FMap.find pid state.proposals with
  | none => .Err default_error
  | some proposal =>
      match FMap.find voter proposal.votes with
      | none => .Err default_error
      | some old_vote =>
          let new_votes := FMap.remove voter proposal.votes
          let new_vote_result := proposal.vote_result - old_vote
          let new_proposal :=
            { proposal with votes := new_votes, vote_result := new_vote_result }
          .Ok { state with proposals := FMap.add pid new_proposal state.proposals }

def congress_action_to_chain_action :
    @CongressAction Base → @ActionBody Base
  | .cact_transfer to_ amount => .act_transfer to_ amount
  | .cact_call to_ amount msg => .act_call to_ amount msg

def proposal_passed (proposal : @Proposal Base) (state : @State Base) : Bool :=
  let rules := state.state_rules
  let total_votes_for_proposal := Int.ofNat (FMap.size proposal.votes)
  let total_members := Int.ofNat (FMap.size state.members)
  let aye_votes := (proposal.vote_result + total_votes_for_proposal) / 2
  let vote_count_permille := total_votes_for_proposal * 1000 / total_members
  let aye_permille := aye_votes * 1000 / total_votes_for_proposal
  let enough_voters :=
    decide (rules.min_vote_count_permille ≤ vote_count_permille)
  let enough_ayes :=
    decide (rules.margin_needed_permille ≤ aye_permille)
  enough_voters && enough_ayes

def do_finish_proposal
    (pid : ProposalId) (state : @State Base) (chain : Chain) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match FMap.find pid state.proposals with
  | none => .Err default_error
  | some proposal =>
      let debate_end :=
        proposal.proposed_in + state.state_rules.debating_period_in_blocks
      if chain.current_slot < debate_end then
        .Err default_error
      else
        let response_acts :=
          if proposal_passed proposal state then proposal.actions else []
        let response_chain_acts := response_acts.map congress_action_to_chain_action
        let new_state := { state with proposals := FMap.remove pid state.proposals }
        .Ok (new_state, response_chain_acts)

def receive
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let sender := ctx.ctx_from
  let is_from_owner := Base.address_eqb sender state.owner
  let is_from_member := FMap.mem sender state.members
  match maybe_msg, is_from_owner, is_from_member with
  | some (.transfer_ownership new_owner), true, _ =>
      .Ok ({ state with owner := new_owner }, [])
  | some (.change_rules new_rules), true, _ =>
      if validate_rules new_rules then
        .Ok ({ state with state_rules := new_rules }, [])
      else
        .Err default_error
  | some (.add_member new_member), true, _ =>
      .Ok ({ state with members := FMap.add new_member () state.members }, [])
  | some (.remove_member old_member), true, _ =>
      .Ok ({ state with members := FMap.remove old_member state.members }, [])
  | some (.create_proposal actions), _, true =>
      .Ok (add_proposal actions chain state, [])
  | some (.vote_for_proposal pid), _, true =>
      without_actions (Base := Base) (vote_on_proposal sender pid 1 state)
  | some (.vote_against_proposal pid), _, true =>
      without_actions (Base := Base) (vote_on_proposal sender pid (-1) state)
  | some (.retract_vote pid), _, true =>
      without_actions (Base := Base) (do_retract_vote sender pid state)
  | some (.finish_proposal pid), _, _ =>
      do_finish_proposal pid state chain
  | none, _, _ =>
      .Ok (state, [])
  | _, _, _ =>
      .Err default_error

def contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

def nr_cacts : Option (@Msg Base) → Nat
  | some (.create_proposal acts) => acts.length
  | _ => 0

def num_cacts_in_state (state : @State Base) : Nat :=
  ((FMap.elements state.proposals).map
    (fun p : Nat × @Proposal Base => p.2.actions.length)).sum

def receive_state_well_behaved
    (state : @State Base) (msg : Option (@Msg Base))
    (new_state : @State Base) (resp_acts : List (@ActionBody Base)) : Bool :=
  num_cacts_in_state new_state + resp_acts.length ≤
    num_cacts_in_state state + nr_cacts msg

namespace Buggy

inductive Msg where
  | transfer_ownership (new_owner : Base.Address)
  | change_rules (new_rules : Rules)
  | add_member (new_member : Base.Address)
  | remove_member (old_member : Base.Address)
  | create_proposal (actions : List (@CongressAction Base))
  | vote_for_proposal (pid : ProposalId)
  | vote_against_proposal (pid : ProposalId)
  | retract_vote (pid : ProposalId)
  | finish_proposal (pid : ProposalId)
  | finish_proposal_remove (pid : ProposalId)
  deriving DecidableEq, Serializable

def do_finish_proposal
    (ctx : @ContractCallContext Base) (pid : ProposalId)
    (state : @State Base) (chain : Chain) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match FMap.find pid state.proposals with
  | none => .Err default_error
  | some proposal =>
      let debate_end :=
        proposal.proposed_in + state.state_rules.debating_period_in_blocks
      if chain.current_slot < debate_end then
        .Err default_error
      else
        let response_acts :=
          if proposal_passed proposal state then proposal.actions else []
        let response_chain_acts := response_acts.map congress_action_to_chain_action
        let self_call_msg := serialize (Msg.finish_proposal_remove pid)
        let self_call := ActionBody.act_call ctx.ctx_contract_address 0 self_call_msg
        .Ok (state, response_chain_acts ++ [self_call])

def receive
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let sender := ctx.ctx_from
  let is_from_owner := Base.address_eqb sender state.owner
  let is_from_member := FMap.mem sender state.members
  match maybe_msg, is_from_owner, is_from_member with
  | some (.transfer_ownership new_owner), true, _ =>
      .Ok ({ state with owner := new_owner }, [])
  | some (.change_rules new_rules), true, _ =>
      if validate_rules new_rules then
        .Ok ({ state with state_rules := new_rules }, [])
      else
        .Err default_error
  | some (.add_member new_member), true, _ =>
      .Ok ({ state with members := FMap.add new_member () state.members }, [])
  | some (.remove_member old_member), true, _ =>
      .Ok ({ state with members := FMap.remove old_member state.members }, [])
  | some (.create_proposal actions), _, true =>
      .Ok (add_proposal actions chain state, [])
  | some (.vote_for_proposal pid), _, true =>
      without_actions (Base := Base) (vote_on_proposal sender pid 1 state)
  | some (.vote_against_proposal pid), _, true =>
      without_actions (Base := Base) (vote_on_proposal sender pid (-1) state)
  | some (.retract_vote pid), _, true =>
      without_actions (Base := Base) (do_retract_vote sender pid state)
  | some (.finish_proposal pid), _, _ =>
      do_finish_proposal ctx pid state chain
  | some (.finish_proposal_remove pid), _, _ =>
      if Base.address_eqb sender ctx.ctx_contract_address then
        .Ok ({ state with proposals := FMap.remove pid state.proposals }, [])
      else
        .Err default_error
  | _, _, _ =>
      .Err default_error

def contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

def nr_cacts : Option (@Msg Base) → Nat
  | some (.create_proposal acts) => acts.length
  | _ => 0

def receive_state_well_behaved
    (state : @State Base) (msg : Option (@Msg Base))
    (new_state : @State Base) (resp_acts : List (@ActionBody Base)) : Bool :=
  num_cacts_in_state new_state + resp_acts.length ≤
    num_cacts_in_state state + nr_cacts msg

abbrev ExploitSetup : Type := Unit
abbrev ExploitState : Type := Nat
abbrev ExploitMsg : Type := Unit
abbrev ExploitError : Type := Nat

def exploit_init
    (_chain : Chain) (_ctx : @ContractCallContext Base)
    (_setup : ExploitSetup) : Result ExploitState ExploitError :=
  .Ok 0

def exploit_receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : ExploitState) (_msg : Option ExploitMsg) :
    Result (ExploitState × List (@ActionBody Base)) ExploitError :=
  if 25 < state then
    .Ok (state, [])
  else
    let again : @Msg Base := .finish_proposal 1
    .Ok (state + 1, [.act_call ctx.ctx_from 0 (serialize again)])

def exploit_contract :
    @Contract Base ExploitSetup ExploitMsg ExploitState ExploitError _ _ _ _ :=
  { init := exploit_init, receive := exploit_receive }

end Buggy

end ConCert.Examples.Congress
