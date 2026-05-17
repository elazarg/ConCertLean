/- Executable checks for the BoardroomVotingZ port. -/

import ConCert.Examples.BoardroomVoting.BoardroomVoting
import ConCert.Execution.Test.TestUtils
import ConCert.Execution.Test.TraceGens

namespace ConCert.Examples.BoardroomVoting.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.SerializableInstances
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.BoardroomVoting

local instance : ChainBase := TestBase

private def addrEq (a b : TestAddress) : Bool := TestBase.address_eqb a b

private def chainAt (slot : Nat) : Chain :=
  { chain_height := slot, current_slot := slot, finalized_height := 0 }

private def ctx
    (sender contract : TestAddress) (amount balance : Amount) :
    @ContractCallContext TestBase :=
  { ctx_origin := sender,
    ctx_from := sender,
    ctx_contract_address := contract,
    ctx_contract_balance := balance,
    ctx_amount := amount }

private def hashFunc (xs : List Positive) : Positive :=
  encode_N (xs.foldl (fun acc p => acc + p.val) 0)

private def params : Params :=
  { hash := hashFunc, prime := 13, generator := 2 }

private def setup : @Setup TestBase :=
  { eligible_voters :=
      FMap.add fixedUser10 ()
        (FMap.add fixedUser11 () FMap.empty),
    finish_registration_by := 2,
    finish_commit_by := none,
    finish_vote_by := 5,
    registration_deposit := 0 }

private def voterInfoEq (a b : VoterInfo) : Bool :=
  a.voter_index == b.voter_index &&
    a.vote_hash.val == b.vote_hash.val &&
    a.public_vote == b.public_vote

private def voterEntriesEq :
    List (TestAddress × VoterInfo) → List (TestAddress × VoterInfo) → Bool
  | [], [] => true
  | a :: as, b :: bs =>
      addrEq a.1 b.1 && voterInfoEq a.2 b.2 && voterEntriesEq as bs
  | _, _ => false

private def setupEq (a b : @Setup TestBase) : Bool :=
  decide (FMap.elements a.eligible_voters = FMap.elements b.eligible_voters) &&
    a.finish_registration_by == b.finish_registration_by &&
    a.finish_commit_by == b.finish_commit_by &&
    a.finish_vote_by == b.finish_vote_by &&
    a.registration_deposit == b.registration_deposit

private def stateEq (a b : @State TestBase) : Bool :=
  addrEq a.owner b.owner &&
    voterEntriesEq (FMap.elements a.registered_voters)
      (FMap.elements b.registered_voters) &&
    a.public_keys == b.public_keys &&
    setupEq a.setup b.setup &&
    a.tally == b.tally

private def roundTripWith {A : Type} [Serializable A]
    (eqA : A → A → Bool) (a : A) : Bool :=
  match (deserialize (serialize a) : Option A) with
  | some b => eqA a b
  | none => false

private def boardroomCall (sender : TestAddress) (msg : Msg) : TestAction :=
  { act_origin := sender,
    act_from := sender,
    act_body := .act_call fixedContractBase 0 (serialize msg) }

private def boardroomDeployAction : TestAction :=
  { act_origin := fixedUser10,
    act_from := fixedUser10,
    act_body :=
      create_deployment 0
        (contract (Base := TestBase) params)
        { setup with finish_vote_by := 3 } }

private def boardroomPks : List A :=
  [compute_public_key params 1, compute_public_key params 2]

private def boardroomSignupActions : List TestAction :=
  [ boardroomCall fixedUser10 (make_signup_msg params 1 3 0),
    boardroomCall fixedUser11 (make_signup_msg params 2 4 1) ]

private def boardroomVoteActions : List TestAction :=
  [ boardroomCall fixedUser10 (make_vote_msg params boardroomPks 0 1 true 3 4 5),
    boardroomCall fixedUser11 (make_vote_msg params boardroomPks 1 2 false 4 5 6) ]

private def addBoardroomBlock
    (cb : TestLocalChainBuilder) (actions : List TestAction) :
    Result TestLocalChainBuilder TestAddBlockError :=
  add_block AddrSize DepthFirst cb
    (nextBlockHeader cb.lcb_lc fixedUser10 BlockReward) actions

private def boardroomChainResult :
    Result TestLocalChainBuilder TestAddBlockError :=
  match addBoardroomBlock (lcb_initial AddrSize) [boardroomDeployAction] with
  | .Err e => .Err e
  | .Ok cb1 =>
      match addBoardroomBlock cb1 boardroomSignupActions with
      | .Err e => .Err e
      | .Ok cb2 =>
          match addBoardroomBlock cb2 boardroomVoteActions with
          | .Err e => .Err e
          | .Ok cb3 =>
              addBoardroomBlock cb3
                [boardroomCall fixedUser10 .tally_votes]

private def getBoardroomState
    (cb : TestLocalChainBuilder) : Option (@State TestBase) :=
  get_contract_state
    (Base := TestBase) (S := @State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) fixedContractBase

def serializationChecker : Checker :=
  checker <|
    let info : VoterInfo :=
      { voter_index := 0, vote_hash := encode_N 4, public_vote := 2 }
    let state : @State TestBase :=
      { owner := fixedUser10,
        registered_voters := FMap.add fixedUser10 info FMap.empty,
        public_keys := [2],
        setup := setup,
        tally := none }
    let msg := make_signup_msg params 1 3 0
    roundTripWith stateEq state &&
      (match (deserialize (serialize msg) : Option Msg) with
       | some (.signup pk _) => pk == compute_public_key params 1
       | _ => false)

def boardroomBehaviorChecker : Checker :=
  checker <|
    let caddr : TestAddress := fixedLocalAddress 135 (by decide)
    let voter := fixedUser10
    let voter2 := fixedUser11
    let ownerCtx := ctx voter caddr 0 0
    match init params (chainAt 0) ownerCtx setup with
    | .Err _ => false
    | .Ok st0 =>
        let signupMsg := make_signup_msg params 1 3 0
        let signupOk :=
          match receive params (chainAt 1) ownerCtx st0 (some signupMsg) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
                st1.public_keys.length == 1 &&
                match FMap.find voter st1.registered_voters with
                | some info =>
                    info.voter_index == 0 &&
                      info.public_vote == 0 &&
                      verify_secret_key_proof params
                        (compute_public_key params 1) 0
                        (secret_key_proof params 1 3 0)
                | none => false
          | .Err _ => false
        let duplicateRejected :=
          match receive params (chainAt 1) ownerCtx st0 (some signupMsg) with
          | .Ok (st1, _) =>
              isErr (receive params (chainAt 1) ownerCtx st1 (some signupMsg))
          | .Err _ => false
        let commitOk :=
          let setupCommit := { setup with finish_commit_by := some 3 }
          let info : VoterInfo :=
            { voter_index := 0, vote_hash := encode_N 0, public_vote := 0 }
          let stCommit : @State TestBase :=
            { owner := voter,
              registered_voters := FMap.add voter info FMap.empty,
              public_keys := [compute_public_key params 1],
              setup := setupCommit,
              tally := none }
          let hash := hashFunc [encodeA 2]
          match receive params (chainAt 2) ownerCtx stCommit
              (some (.commit_to_vote hash)) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
                match FMap.find voter st1.registered_voters with
                | some info => info.vote_hash.val == hash.val
                | none => false
          | .Err _ => false
        let submitOk :=
          match receive params (chainAt 1) ownerCtx st0 (some signupMsg) with
          | .Err _ => false
          | .Ok (st1, _) =>
              let voteMsg := make_vote_msg params st1.public_keys 0 1 true 3 4 5
              match receive params (chainAt 3) ownerCtx st1 (some voteMsg) with
              | .Ok (st2, acts) =>
                  acts.isEmpty &&
                    match FMap.find voter st2.registered_voters with
                    | some info => !elmeqb params info.public_vote 0
                    | none => false
              | .Err _ => false
        let tallyOk :=
          let info1 : VoterInfo :=
            { voter_index := 0, vote_hash := encode_N 0,
              public_vote := params.generator }
          let info2 : VoterInfo :=
            { voter_index := 1, vote_hash := encode_N 0,
              public_vote := params.generator }
          let info3 : VoterInfo :=
            { voter_index := 2, vote_hash := encode_N 0, public_vote := 1 }
          let stTally : @State TestBase :=
            { owner := voter,
              registered_voters :=
                FMap.add voter info1
                  (FMap.add voter2 info2
                    (FMap.add (fixedLocalAddress 12 (by decide)) info3 FMap.empty)),
              public_keys := [2, 2, 2],
              setup := setup,
              tally := none }
          match receive params (chainAt 6) ownerCtx stTally (some .tally_votes) with
          | .Ok (stDone, acts) => acts.isEmpty && stDone.tally == some 2
          | .Err _ => false
        signupOk && duplicateRejected && commitOk && submitOk && tallyOk

def localChainExampleChecker : Checker :=
  checker <|
    match boardroomChainResult with
    | .Err _ => false
    | .Ok cb =>
        match getBoardroomState cb with
        | none => false
        | some st =>
            st.tally == some 1 &&
              st.public_keys == boardroomPks &&
              (FMap.values st.registered_voters).all
                (fun info => !elmeqb params info.public_vote 0)

end ConCert.Examples.BoardroomVoting.Tests
