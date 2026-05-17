/- Executable checks ported from examples/congress/tests. -/

import ConCert.Examples.Congress.Congress
import ConCert.Execution.Test.TestUtils
import ConCert.Execution.Test.TraceGens

namespace ConCert.Examples.Congress.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.Congress

local instance : ChainBase := TestBase

private def addrEq (a b : TestAddress) : Bool := TestBase.address_eqb a b

private def baseChain : Chain :=
  { chain_height := 0, current_slot := 0, finalized_height := 0 }

private def ctx
    (sender contract : TestAddress) (amount balance : Amount) :
    @ContractCallContext TestBase :=
  { ctx_origin := sender,
    ctx_from := sender,
    ctx_contract_address := contract,
    ctx_contract_balance := balance,
    ctx_amount := amount }

private def rules : Rules :=
  { min_vote_count_permille := 200,
    margin_needed_permille := 501,
    debating_period_in_blocks := 0 }

private def setup : Setup := { setup_rules := rules }

private def actionEq
    (a b : @CongressAction TestBase) : Bool :=
  match a, b with
  | .cact_transfer toA amountA, .cact_transfer toB amountB =>
      addrEq toA toB && amountA == amountB
  | _, _ => false

private def actionListEq :
    List (@CongressAction TestBase) → List (@CongressAction TestBase) → Bool
  | [], [] => true
  | a :: as, b :: bs => actionEq a b && actionListEq as bs
  | _, _ => false

private def rulesEq (a b : Rules) : Bool :=
  a.min_vote_count_permille == b.min_vote_count_permille &&
    a.margin_needed_permille == b.margin_needed_permille &&
    a.debating_period_in_blocks == b.debating_period_in_blocks

private def proposalEq
    (a b : @Proposal TestBase) : Bool :=
  actionListEq a.actions b.actions &&
    decide (FMap.elements a.votes = FMap.elements b.votes) &&
    a.vote_result == b.vote_result &&
    a.proposed_in == b.proposed_in

private def proposalEntriesEq :
    List (Nat × @Proposal TestBase) → List (Nat × @Proposal TestBase) → Bool
  | [], [] => true
  | a :: as, b :: bs =>
      a.1 == b.1 && proposalEq a.2 b.2 && proposalEntriesEq as bs
  | _, _ => false

private def stateEq (a b : @State TestBase) : Bool :=
  addrEq a.owner b.owner &&
    rulesEq a.state_rules b.state_rules &&
    proposalEntriesEq (FMap.elements a.proposals) (FMap.elements b.proposals) &&
    a.next_proposal_id == b.next_proposal_id &&
    decide (FMap.elements a.members = FMap.elements b.members)

private def msgEq
    (a b : @Msg TestBase) : Bool :=
  match a, b with
  | .transfer_ownership a, .transfer_ownership b => addrEq a b
  | .change_rules a, .change_rules b => rulesEq a b
  | .add_member a, .add_member b => addrEq a b
  | .remove_member a, .remove_member b => addrEq a b
  | .create_proposal a, .create_proposal b => actionListEq a b
  | .vote_for_proposal a, .vote_for_proposal b => a == b
  | .vote_against_proposal a, .vote_against_proposal b => a == b
  | .retract_vote a, .retract_vote b => a == b
  | .finish_proposal a, .finish_proposal b => a == b
  | _, _ => false

private def buggyMsgEq
    (a b : @Buggy.Msg TestBase) : Bool :=
  match a, b with
  | .transfer_ownership a, .transfer_ownership b => addrEq a b
  | .change_rules a, .change_rules b => rulesEq a b
  | .add_member a, .add_member b => addrEq a b
  | .remove_member a, .remove_member b => addrEq a b
  | .create_proposal a, .create_proposal b => actionListEq a b
  | .vote_for_proposal a, .vote_for_proposal b => a == b
  | .vote_against_proposal a, .vote_against_proposal b => a == b
  | .retract_vote a, .retract_vote b => a == b
  | .finish_proposal a, .finish_proposal b => a == b
  | .finish_proposal_remove a, .finish_proposal_remove b => a == b
  | _, _ => false

private def roundTripWith {A : Type} [Serializable A]
    (eqA : A → A → Bool) (a : A) : Bool :=
  match (deserialize (serialize a) : Option A) with
  | some b => eqA a b
  | none => false

private def gRules : G Rules := do
  let min_vote_count_permille ← chooseIntBetween 0 1000 (by decide)
  let margin_needed_permille ← chooseIntBetween 0 1000 (by decide)
  let debating_period_in_blocks ← chooseNatBetween 0 10 (by decide)
  return {
    min_vote_count_permille,
    margin_needed_permille,
    debating_period_in_blocks }

private def gAction : G (@CongressAction TestBase) := do
  let to_ ← gLocalAccountAddress
  let amount ← chooseIntBetween 0 50 (by decide)
  return .cact_transfer to_ amount

private def gActionList : G (List (@CongressAction TestBase)) := do
  let len ← chooseNatBetween 0 3 (by decide)
  let rec loop : Nat → G (List (@CongressAction TestBase))
    | 0 => return []
    | n + 1 => do
        let act ← gAction
        let acts ← loop n
        return act :: acts
  loop len

private def gMsg : G (@Msg TestBase) := do
  let tag ← chooseNatBetween 0 8 (by decide)
  match tag with
  | 0 => return .transfer_ownership (← gLocalAccountAddress)
  | 1 => return .change_rules (← gRules)
  | 2 => return .add_member (← gLocalAccountAddress)
  | 3 => return .remove_member (← gLocalAccountAddress)
  | 4 => return .create_proposal (← gActionList)
  | 5 => return .vote_for_proposal (← chooseNatBetween 0 8 (by decide))
  | 6 => return .vote_against_proposal (← chooseNatBetween 0 8 (by decide))
  | 7 => return .retract_vote (← chooseNatBetween 0 8 (by decide))
  | _ => return .finish_proposal (← chooseNatBetween 0 8 (by decide))

private def gBuggyMsg : G (@Buggy.Msg TestBase) := do
  let tag ← chooseNatBetween 0 9 (by decide)
  match tag with
  | 0 => return .transfer_ownership (← gLocalAccountAddress)
  | 1 => return .change_rules (← gRules)
  | 2 => return .add_member (← gLocalAccountAddress)
  | 3 => return .remove_member (← gLocalAccountAddress)
  | 4 => return .create_proposal (← gActionList)
  | 5 => return .vote_for_proposal (← chooseNatBetween 0 8 (by decide))
  | 6 => return .vote_against_proposal (← chooseNatBetween 0 8 (by decide))
  | 7 => return .retract_vote (← chooseNatBetween 0 8 (by decide))
  | 8 => return .finish_proposal (← chooseNatBetween 0 8 (by decide))
  | _ => return .finish_proposal_remove (← chooseNatBetween 0 8 (by decide))

private def gProposal : G (@Proposal TestBase) := do
  let action ← gAction
  let voter ← gLocalAccountAddress
  let vote ← chooseIntBetween (-1) 1 (by decide)
  let proposed_in ← chooseNatBetween 0 20 (by decide)
  return {
    actions := [action],
    votes := FMap.add voter vote FMap.empty,
    vote_result := vote,
    proposed_in }

private def gState : G (@State TestBase) := do
  let owner ← gLocalAccountAddress
  let state_rules ← gRules
  let proposal ← gProposal
  let member ← gLocalAccountAddress
  return {
    owner,
    state_rules,
    proposals := FMap.add 1 proposal FMap.empty,
    next_proposal_id := 2,
    members := FMap.add member () FMap.empty }

def serializationCheckers : List (String × Checker) :=
  [ ("Congress rules serialization round-trip",
      forAllGen gRules (roundTripWith rulesEq))
  , ("Congress message serialization round-trip",
      forAllGen gMsg (roundTripWith msgEq))
  , ("Congress buggy message serialization round-trip",
      forAllGen gBuggyMsg (roundTripWith buggyMsgEq))
  , ("Congress state serialization round-trip",
      forAllGen gState (roundTripWith stateEq)) ]

def congressBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let member := fixedUser11
    let recipient : TestAddress := fixedLocalAddress 12 (by decide)
    let congressAddr : TestAddress := fixedLocalAddress 18 (by decide)
    let ownerCtx := ctx owner congressAddr 0 50
    let memberCtx := ctx member congressAddr 0 50
    match init baseChain ownerCtx setup with
    | .Err _ => false
    | .Ok st0 =>
        let ownerCanAdd :=
          match receive baseChain ownerCtx st0 (some (.add_member member)) with
          | .Ok (st1, acts) =>
              acts.isEmpty && FMap.mem member st1.members
          | .Err _ => false
        let nonOwnerCannotAdd :=
          isErr (receive baseChain memberCtx st0 (some (.add_member recipient)))
        let voteFlow :=
          match receive baseChain ownerCtx st0 (some (.add_member member)) with
          | .Err _ => false
          | .Ok (stMember, _) =>
              let action : @CongressAction TestBase :=
                .cact_transfer recipient 3
              match receive baseChain memberCtx stMember
                  (some (.create_proposal [action])) with
              | .Err _ => false
              | .Ok (stProposal, acts1) =>
                  let createdOk :=
                    acts1.isEmpty &&
                      stProposal.next_proposal_id == 2 &&
                      match FMap.find 1 stProposal.proposals with
                      | some p =>
                          p.actions.length == 1 &&
                            p.proposed_in == baseChain.current_slot
                      | none => false
                  match receive baseChain memberCtx stProposal
                      (some (.vote_for_proposal 1)) with
                  | .Err _ => false
                  | .Ok (stVoted, acts2) =>
                      let votedOk :=
                        acts2.isEmpty &&
                          match FMap.find 1 stVoted.proposals with
                          | some p =>
                              p.vote_result == 1 &&
                                FMap.find member p.votes == some 1
                          | none => false
                      match receive baseChain memberCtx stVoted
                          (some (.finish_proposal 1)) with
                      | .Ok (stFinished, [.act_transfer to_ amount]) =>
                          createdOk && votedOk &&
                            addrEq to_ recipient && amount == 3 &&
                            (FMap.find 1 stFinished.proposals).isNone
                      | _ => false
        let noneIsDonation :=
          match receive baseChain memberCtx st0 none with
          | .Ok (stSame, acts) => stateEq stSame st0 && acts.isEmpty
          | .Err _ => false
        ownerCanAdd && nonOwnerCannotAdd && voteFlow && noneIsDonation

private def buggyWitnessState :
    @State TestBase :=
  let member := fixedUser11
  let recipient : TestAddress := fixedLocalAddress 12 (by decide)
  let proposal : @Proposal TestBase :=
    { actions := [.cact_transfer recipient 3],
      votes := FMap.add member 1 FMap.empty,
      vote_result := 1,
      proposed_in := 0 }
  { owner := fixedUser10,
    state_rules := rules,
    proposals := FMap.add 1 proposal FMap.empty,
    next_proposal_id := 2,
    members := FMap.add member () FMap.empty }

def buggyFinishWitnessChecker : Checker :=
  checker <|
    let member := fixedUser11
    let recipient : TestAddress := fixedLocalAddress 12 (by decide)
    let congressAddr : TestAddress := fixedLocalAddress 18 (by decide)
    let memberCtx := ctx member congressAddr 0 50
    let msg : @Buggy.Msg TestBase := .finish_proposal 1
    match Buggy.receive baseChain memberCtx buggyWitnessState (some msg) with
    | .Ok (stNew, [.act_transfer to_ amount, .act_call self amount2 selfMsg]) =>
        addrEq to_ recipient &&
          amount == 3 &&
          addrEq self congressAddr &&
          amount2 == 0 &&
          (FMap.find 1 stNew.proposals).isSome &&
          !(Buggy.receive_state_well_behaved buggyWitnessState (some msg)
            stNew [.act_transfer to_ amount, .act_call self amount2 selfMsg]) &&
          match (deserialize selfMsg : Option (@Buggy.Msg TestBase)) with
          | some (.finish_proposal_remove 1) => true
          | _ => false
    | _ => false

def buggyActionConservationChecker : Checker :=
  checker <|
    let member := fixedUser11
    let congressAddr : TestAddress := fixedLocalAddress 18 (by decide)
    let memberCtx := ctx member congressAddr 0 50
    let msg : @Buggy.Msg TestBase := .finish_proposal 1
    match Buggy.receive baseChain memberCtx buggyWitnessState (some msg) with
    | .Ok (stNew, acts) =>
        Buggy.receive_state_well_behaved buggyWitnessState (some msg) stNew acts
    | .Err _ => false

end ConCert.Examples.Congress.Tests
