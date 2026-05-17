/- Port of examples/congress/tests/CongressGens.v over the local-chain backend. -/

import ConCert.Execution.Test.TraceGens
import ConCert.Examples.Congress.Congress
import ConCert.Examples.Congress.CongressPrinters

namespace ConCert.Examples.Congress.Gens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.Congress

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction
abbrev TestLocalChainBuilder := ConCert.Execution.Test.TraceGens.TestLocalChainBuilder
abbrev TestAddBlockError := ConCert.Execution.Test.TraceGens.TestAddBlockError

local instance : ChainBase := TestBase

def creator_addr : TestAddress := fixedUser10
def member_addr : TestAddress := fixedUser11
def candidate_addr : TestAddress := fixedLocalAddress 12 (by decide)
def recipient_addr : TestAddress := fixedLocalAddress 13 (by decide)
def spare_addr : TestAddress := fixedLocalAddress 14 (by decide)
def congress_addr : TestAddress := fixedContractBase

def account_candidates : List TestAddress :=
  [creator_addr, member_addr, candidate_addr, recipient_addr, spare_addr]

def gAccount : G TestAddress :=
  Plausible.Gen.elements account_candidates (by simp [account_candidates])

def gRules : G Rules := do
  let min_vote_count_permille ← chooseIntBetween 1 1000 (by decide)
  let margin_needed_permille ← chooseIntBetween 1 1000 (by decide)
  let debating_period_in_blocks ← chooseNatBetween 0 8 (by decide)
  return {
    min_vote_count_permille := min_vote_count_permille,
    margin_needed_permille := margin_needed_permille,
    debating_period_in_blocks := debating_period_in_blocks }

def gSetup : G Setup := do
  return { setup_rules := (← gRules) }

def setup_rules : Rules :=
  { min_vote_count_permille := 200,
    margin_needed_permille := 501,
    debating_period_in_blocks := 0 }

def setup : Setup := { setup_rules := setup_rules }

def congress_call (caller : TestAddress) (amount : Amount)
    (msg : @Msg TestBase) : TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call congress_addr amount (serialize msg) }

def initial_congress_header : @BlockHeader TestBase :=
  nextBlockHeader (lc_initial AddrSize) creator_addr 100

def deploy_congress_action : TestAction :=
  { act_origin := creator_addr,
    act_from := creator_addr,
    act_body := create_deployment 5 (contract (Base := TestBase)) setup }

def initial_congress_actions : List TestAction :=
  [ transferAction creator_addr member_addr 10,
    transferAction creator_addr candidate_addr 10,
    deploy_congress_action ]

def congress_deploy_result : Result TestLocalChainBuilder TestAddBlockError :=
  add_block AddrSize DepthFirst (lcb_initial AddrSize)
    initial_congress_header initial_congress_actions

def add_initial_members_result :
    Result TestLocalChainBuilder TestAddBlockError :=
  match congress_deploy_result with
  | .Err err => .Err err
  | .Ok cb =>
      let header := nextBlockHeader cb.lcb_lc creator_addr 0
      add_block AddrSize DepthFirst cb header
        [ congress_call creator_addr 0 (.add_member creator_addr),
          congress_call creator_addr 0 (.add_member member_addr) ]

def get_congress_state (cb : TestLocalChainBuilder) :
    Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) congress_addr

def get_congress_state_from_env (env : @Environment TestBase) :
    Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase) env congress_addr

def account_balance (env : @Environment TestBase) (addr : TestAddress) :
    Amount :=
  env.env_account_balances addr

def members (state : @State TestBase) : List TestAddress :=
  (FMap.elements state.members).map Prod.fst

def congressContractsMembers_nonowners (state : @State TestBase) :
    List TestAddress :=
  (members state).filter (fun member => !(TestBase.address_eqb member state.owner))

def gCongressMember_without_caller (state : @State TestBase)
    (calling_addr : TestAddress) : GOpt TestAddress :=
  elems_opt ((members state).filter
    (fun member => !(TestBase.address_eqb member calling_addr)))

def try_newCongressMember_fix (members : List TestAddress) :
    List TestAddress :=
  account_candidates.filter
    (fun addr => !(members.any (fun member => TestBase.address_eqb member addr)))

def try_newCongressMember (state : @State TestBase) : GOpt TestAddress :=
  elems_opt (try_newCongressMember_fix (members state))

def bindCallerIsOwnerOpt {A : Type} (state : @State TestBase)
    (calling_addr : TestAddress) (g : GOpt A) : GOpt A :=
  if TestBase.address_eqb calling_addr congress_addr then
    g
  else if TestBase.address_eqb state.owner calling_addr then
    g
  else
    returnGen none

def try_gNewOwner (state : @State TestBase) (calling_addr : TestAddress) :
    GOpt TestAddress :=
  bindCallerIsOwnerOpt state calling_addr
    (gCongressMember_without_caller state calling_addr)

def finishable_proposals (state : @State TestBase)
    (current_slot : Nat) : List (ProposalId × @Proposal TestBase) :=
  (FMap.elements state.proposals).filter
    (fun p =>
      p.2.proposed_in + state.state_rules.debating_period_in_blocks ≤
        current_slot)

def proposal_ids_not_voted (state : @State TestBase)
    (voter : TestAddress) : List ProposalId :=
  ((FMap.elements state.proposals).filter
    (fun p => (FMap.find voter p.2.votes).isNone)).map Prod.fst

def proposal_ids_with_votes (state : @State TestBase)
    (voter : TestAddress) : List ProposalId :=
  ((FMap.elements state.proposals).filter
    (fun p => (FMap.find voter p.2.votes).isSome)).map Prod.fst

def generated_call (env : @Environment TestBase) (caller : TestAddress)
    (msg : @Msg TestBase) : GOpt TestAction := (do
  let upper := (account_balance env caller).toNat
  let amount ← chooseNatBetween 0 upper (Nat.zero_le upper)
  return some (congress_call caller (Int.ofNat amount) msg) :
    G (Option TestAction))

def vote_proposal (env : @Environment TestBase)
    (state : @State TestBase) (vote : ProposalId → @Msg TestBase) :
    GOpt TestAction := (do
  match ← elems_opt (members state) with
  | none => return none
  | some member =>
      match ← elems_opt (proposal_ids_not_voted state member) with
      | none => return none
      | some pid => generated_call env member (vote pid) :
    G (Option TestAction))

def retract_vote (env : @Environment TestBase)
    (state : @State TestBase) : GOpt TestAction := (do
  match ← elems_opt (members state) with
  | none => return none
  | some member =>
      match ← elems_opt (proposal_ids_with_votes state member) with
      | none => return none
      | some pid => generated_call env member (.retract_vote pid) :
    G (Option TestAction))

def gBaseCongressAction (env : @Environment TestBase)
    (state : @State TestBase) : GOpt TestAction := (do
  let choice ← chooseNatBetween 0 8 (by decide)
  match choice with
  | 0 =>
      match ← elems_opt (congressContractsMembers_nonowners state) with
      | none => return none
      | some _ =>
          match ← try_gNewOwner state state.owner with
          | none => return none
          | some new_owner =>
              generated_call env state.owner (.transfer_ownership new_owner)
  | 1 =>
      let rules ← gRules
      generated_call env state.owner (.change_rules rules)
  | 2 =>
      match ← try_newCongressMember state with
      | none => return none
      | some new_member =>
          generated_call env state.owner (.add_member new_member)
  | 3 =>
      match ← elems_opt (members state) with
      | none => return none
      | some member =>
          generated_call env state.owner (.remove_member member)
  | 4 =>
      vote_proposal env state Msg.vote_for_proposal
  | 5 =>
      vote_proposal env state Msg.vote_against_proposal
  | 6 =>
      retract_vote env state
  | 7 =>
      match ← elems_opt (finishable_proposals state env.current_slot) with
      | none => return none
      | some (pid, _) =>
          generated_call env state.owner (.finish_proposal pid)
  | _ =>
      let action : @CongressAction TestBase :=
        .cact_transfer recipient_addr 3
      match ← elems_opt (members state) with
      | none => return none
      | some member =>
          generated_call env member (.create_proposal [action]) :
    G (Option TestAction))

partial def GCongressAction (env : @Environment TestBase)
    (fuel : Nat) (caddr : TestAddress := congress_addr) : GOpt TestAction := (do
  match get_congress_state_from_env env with
  | none => return none
  | some state =>
      if !(TestBase.address_eqb caddr congress_addr) then
        return none
      else
        match fuel with
        | 0 => gBaseCongressAction env state
        | fuel' + 1 =>
            let choice ← chooseNatBetween 0 3 (by decide)
            if choice == 0 then
              match ← GCongressAction env fuel' caddr with
              | none => return none
              | some act =>
                  match act.act_body with
                  | .act_call to_ amount msg =>
                      match ← elems_opt (members state) with
                      | none => return some act
                      | some member =>
                          let ca : @CongressAction TestBase :=
                            .cact_call to_ amount msg
                          generated_call env member (.create_proposal [ca])
                  | _ => return some act
            else
              gBaseCongressAction env state :
    G (Option TestAction))

def addCongressActionBlockResult (cb : TestLocalChainBuilder)
    (act : TestAction) : Result TestLocalChainBuilder TestAddBlockError :=
  let header := nextBlockHeader cb.lcb_lc creator_addr 0
  add_block AddrSize DepthFirst cb header [act]

def tryAddCongressActionBlock (cb : TestLocalChainBuilder)
    (act : TestAction) : Option TestLocalChainBuilder :=
  match addCongressActionBlockResult cb act with
  | .Ok cb' => some cb'
  | .Err _ => none

def gCongressTrace (cb : TestLocalChainBuilder) (fuel : Nat) :
    Nat → G TestLocalChainBuilder
  | 0 => return cb
  | n + 1 => do
      match ← GCongressAction (lc_to_env AddrSize cb.lcb_lc) fuel with
      | none => return cb
      | some act =>
          match tryAddCongressActionBlock cb act with
          | some cb' => gCongressTrace cb' fuel n
          | none => gCongressTrace cb fuel n

def gCongressChainBuilder (length : Nat) (fuel : Nat := 2) :
    G TestLocalChainBuilder := do
  match add_initial_members_result with
  | .Ok cb => gCongressTrace cb fuel length
  | .Err _ => genFailure "initial Congress chain deployment failed"

end ConCert.Examples.Congress.Gens
