/- Port of examples/congress/tests/Congress_BuggyPrinters.v as string renderers. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Examples.Congress.Congress
import ConCert.Examples.Congress.CongressPrinters

namespace ConCert.Examples.Congress.BuggyPrinters

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.ChainPrinters
open ConCert.Examples.Congress

variable [Base : ChainBase]

def string_of_rules (rules : Rules) : String :=
  Printers.string_of_rules rules

def string_of_setup (setup : Setup) : String :=
  Printers.string_of_setup setup

def string_of_congress_action
    (showAddr : Base.Address → String)
    (str_of_msg : @Buggy.Msg Base → String) :
    @CongressAction Base → String
  | .cact_transfer to_ amount =>
      "(transfer: " ++ showAddr to_ ++ sep ++ toString amount ++ ")"
  | .cact_call to_ amount msg =>
      "(call: " ++ showAddr to_ ++ sep ++ toString amount ++ sep ++
        (match (deserialize msg : Option (@Buggy.Msg Base)) with
        | some decoded => str_of_msg decoded
        | none => "<FAILED DESERIALIZATION OF CONGRESS MSG>") ++ ")"

def string_of_msg (showAddr : Base.Address → String) :
    Nat → @Buggy.Msg Base → String
  | 0, .create_proposal actions =>
      "create_proposal " ++
        String.intercalate "; " (actions.map (fun _ => "Msg{...}"))
  | fuel + 1, .create_proposal actions =>
      let showAct := string_of_congress_action showAddr (string_of_msg showAddr fuel)
      "create_proposal " ++ String.intercalate "; " (actions.map showAct)
  | _, .transfer_ownership addr =>
      "transfer_ownership " ++ showAddr addr
  | _, .change_rules rules =>
      "change_rules " ++ string_of_rules rules
  | _, .add_member addr =>
      "add_member " ++ showAddr addr
  | _, .remove_member addr =>
      "remove_member " ++ showAddr addr
  | _, .vote_for_proposal pid =>
      "vote_for_proposal " ++ toString pid
  | _, .vote_against_proposal pid =>
      "vote_against_proposal " ++ toString pid
  | _, .retract_vote pid =>
      "retract_vote " ++ toString pid
  | _, .finish_proposal pid =>
      "finish_proposal " ++ toString pid
  | _, .finish_proposal_remove pid =>
      "finish_proposal_remove " ++ toString pid

def string_of_proposal (showAddr : Base.Address → String)
    (proposal : @Proposal Base) : String :=
  let showAct := string_of_congress_action showAddr (string_of_msg showAddr 20)
  "Proposal{actions=[" ++ String.intercalate sep (proposal.actions.map showAct) ++
    "]" ++ sep ++ "votes=" ++
    ConCert.Execution.Test.TestUtils.string_of_FMap showAddr toString proposal.votes ++
    sep ++ "vote_result=" ++ toString proposal.vote_result ++
    sep ++ "proposed_in=" ++ toString proposal.proposed_in ++ "}"

def string_of_state (showAddr : Base.Address → String) (state : @State Base) :
    String :=
  "State{owner=" ++ showAddr state.owner ++ sep ++
    "rules=" ++ string_of_rules state.state_rules ++ sep ++
    "proposals=" ++
      ConCert.Execution.Test.TestUtils.string_of_FMap toString
        (string_of_proposal showAddr) state.proposals ++ sep ++
    "next_proposal_id=" ++ toString state.next_proposal_id ++ sep ++
    "members=" ++
      ConCert.Execution.Test.TestUtils.string_of_FMap showAddr (fun _ => "()")
        state.members ++ "}"

def string_of_serialized_msg (v : SerializedValue) : String :=
  string_of_serialized_value v

end ConCert.Examples.Congress.BuggyPrinters
