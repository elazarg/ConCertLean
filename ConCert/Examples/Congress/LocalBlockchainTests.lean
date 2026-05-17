/- Port of examples/congress/LocalBlockchainTests.v. -/

import ConCert.Examples.Congress.CongressCorrect
import ConCert.Examples.Congress.CongressGens

namespace ConCert.Examples.Congress.LocalBlockchainTests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainBuilder
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
noncomputable local instance : @ChainBuilderType TestBase :=
  LocalChainBuilderImpl AddrSize DepthFirst

def creator : TestAddress := fixedUser10
def person_1 : TestAddress := fixedUser11
def person_2 : TestAddress := fixedLocalAddress 12 (by decide)
def person_3 : TestAddress := fixedLocalAddress 13 (by decide)

def chain1 : TestLocalChainBuilder := lcb_initial AddrSize

def add_block (chain : TestLocalChainBuilder) (acts : List TestAction) :
    Result TestLocalChainBuilder TestAddBlockError :=
  let header := nextBlockHeader chain.lcb_lc creator 50
  ConCert.Execution.Test.LocalBlockchain.add_block
    AddrSize DepthFirst chain header acts

def chain2 : TestLocalChainBuilder :=
  unpack_result (add_block chain1 [])

#guard (lc_to_env AddrSize chain2.lcb_lc).env_account_balances person_1 == 0
#guard (lc_to_env AddrSize chain2.lcb_lc).env_account_balances creator == 50

def chain3 : TestLocalChainBuilder :=
  unpack_result (add_block chain2 [transferAction creator person_1 10])

#guard (lc_to_env AddrSize chain3.lcb_lc).env_account_balances person_1 == 10
#guard (lc_to_env AddrSize chain3.lcb_lc).env_account_balances creator == 90

def setup_rules : Rules :=
  { min_vote_count_permille := 200,
    margin_needed_permille := 501,
    debating_period_in_blocks := 0 }

def setup : Setup := { setup_rules := setup_rules }

def deploy_congress : @ActionBody TestBase :=
  create_deployment 5 (contract (Base := TestBase)) setup

def chain4 : TestLocalChainBuilder :=
  unpack_result (add_block chain3
    [{ act_origin := person_1, act_from := person_1,
       act_body := deploy_congress }])

def congress_1 : TestAddress := fixedContractBase

#guard (lc_to_env AddrSize chain4.lcb_lc).env_account_balances person_1 == 5
#guard (lc_to_env AddrSize chain4.lcb_lc).env_account_balances creator == 140
#guard (lc_to_env AddrSize chain4.lcb_lc).env_account_balances congress_1 == 5

def congress_state (chain : TestLocalChainBuilder) : @State TestBase :=
  match ConCert.Execution.Test.TestUtils.get_contract_state
      (Base := TestBase) (S := @State TestBase)
      (lc_to_env AddrSize chain.lcb_lc) congress_1 with
  | some state => state
  | none =>
      { owner := creator,
        state_rules := setup_rules,
        proposals := FMap.empty,
        next_proposal_id := 0,
        members := FMap.empty }

#guard (congress_state chain4).next_proposal_id == 1
#guard (FMap.elements (congress_state chain4).members).isEmpty

def add_person (p : TestAddress) : TestAction :=
  { act_origin := person_1,
    act_from := person_1,
    act_body := .act_call congress_1 0 (serialize (Msg.add_member p)) }

def chain5 : TestLocalChainBuilder :=
  unpack_result (add_block chain4 [add_person person_1, add_person person_2])

#guard (FMap.size (congress_state chain5).members) == 2
#guard (lc_to_env AddrSize chain5.lcb_lc).env_account_balances congress_1 == 5

def create_proposal_call : TestAction :=
  { act_origin := person_1,
    act_from := person_1,
    act_body := .act_call congress_1 0
      (serialize (Msg.create_proposal [.cact_transfer person_3 3])) }

def chain6 : TestLocalChainBuilder :=
  unpack_result (add_block chain5 [create_proposal_call])

#guard (FMap.size (congress_state chain6).proposals) == 1

def vote_proposal (voter : TestAddress) : TestAction :=
  { act_origin := voter,
    act_from := voter,
    act_body := .act_call congress_1 0 (serialize (Msg.vote_for_proposal 1)) }

def chain7 : TestLocalChainBuilder :=
  unpack_result (add_block chain6 [vote_proposal person_1, vote_proposal person_2])

#guard
  match FMap.find 1 (congress_state chain7).proposals with
  | some proposal => proposal.vote_result == 2
  | none => false

def finish_proposal : TestAction :=
  { act_origin := person_3,
    act_from := person_3,
    act_body := .act_call congress_1 0 (serialize (Msg.finish_proposal 1)) }

def chain8 : TestLocalChainBuilder :=
  unpack_result (add_block chain7 [finish_proposal])

#guard (FMap.elements (congress_state chain8).proposals).isEmpty
#guard (lc_to_env AddrSize chain7.lcb_lc).env_account_balances congress_1 == 5
#guard (lc_to_env AddrSize chain7.lcb_lc).env_account_balances person_3 == 0
#guard (lc_to_env AddrSize chain8.lcb_lc).env_account_balances congress_1 == 2
#guard (lc_to_env AddrSize chain8.lcb_lc).env_account_balances person_3 == 3

theorem congress_txs_after_local_chain_block
    (prev new : TestLocalChainBuilder) (header : @BlockHeader TestBase)
    (acts : List TestAction) :
    ConCert.Execution.Test.LocalBlockchain.add_block
      AddrSize DepthFirst prev header acts = .Ok new →
    ∀ caddr : TestAddress,
      (lc_to_env AddrSize new.lcb_lc).env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract TestBase _ _ _ _ _ _ _ _)) →
      ∃ inc_calls : List (@ContractCallInfo TestBase (@Msg TestBase)),
        incoming_calls (@Msg TestBase) new.lcb_trace caddr = some inc_calls ∧
        (outgoing_txs new.lcb_trace caddr).length ≤
          num_acts_created_in_proposals inc_calls := by
  intro h caddr hcontract
  exact congress_correct_after_block
    (Base := TestBase) (Cb := (inferInstance : @ChainBuilderType TestBase))
    prev new header acts h caddr hcontract

end ConCert.Examples.Congress.LocalBlockchainTests
