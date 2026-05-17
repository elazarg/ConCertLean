/- Executable checks for the CIS1 WCCD token port. -/

import ConCert.Examples.CIS1.CIS1
import ConCert.Execution.Test.TestUtils
import ConCert.Execution.Test.TraceGens

namespace ConCert.Examples.CIS1.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.CIS1

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

private def stateEq (a b : @WCCD.State TestBase) : Bool :=
  decide (FMap.elements a = FMap.elements b)

private def roundTripWith {A : Type} [Serializable A]
    (eqA : A → A → Bool) (a : A) : Bool :=
  match (deserialize (serialize a) : Option A) with
  | some b => eqA a b
  | none => false

def serializationChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let operator := fixedUser11
    let recipient : TestAddress := fixedLocalAddress 12 (by decide)
    let addrState : @WCCD.AddressState TestBase :=
      { wccd_balance := 25, wccd_operators := [operator] }
    let st : @WCCD.State TestBase := FMap.add owner addrState FMap.empty
    let msg : @WCCD.Msg TestBase :=
      .wccd_msg_transfer
        [{ token_id := (),
           amount := 7,
           from_ := owner,
           to_ := recipient }]
    roundTripWith stateEq st &&
      (match (deserialize (serialize msg) : Option (@WCCD.Msg TestBase)) with
       | some (.wccd_msg_transfer [p]) =>
           p.amount == 7 && addrEq p.from_ owner && addrEq p.to_ recipient
       | _ => false)

def wccdBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let operator := fixedUser11
    let recipient : TestAddress := fixedLocalAddress 12 (by decide)
    let hook : TestAddress := fixedLocalAddress 133 (by decide)
    let tokenAddr : TestAddress := fixedLocalAddress 134 (by decide)
    let ownerCtx0 := ctx owner tokenAddr 0 0
    let ownerCtxMint := ctx owner tokenAddr 40 40
    let stOwner : @WCCD.State TestBase :=
      FMap.add owner { wccd_balance := 100, wccd_operators := [] } FMap.empty
    let mintOk :=
      match WCCD.receive baseChain ownerCtxMint FMap.empty
          (some (.wccd_msg_mint recipient)) with
      | .Ok (stMinted, acts) =>
          acts.isEmpty && WCCD.balance_of recipient stMinted == 40
      | .Err _ => false
    let ownerTransferOk :=
      let transfer : @WCCD.TransferParam TestBase :=
        { token_id := (), amount := 30, from_ := owner, to_ := recipient }
      match WCCD.receive baseChain ownerCtx0 stOwner
          (some (.wccd_msg_transfer [transfer])) with
      | .Ok (stMoved, acts) =>
          acts.isEmpty &&
            WCCD.balance_of owner stMoved == 70 &&
            WCCD.balance_of recipient stMoved == 30
      | .Err _ => false
    let operatorUpdateOk :=
      match WCCD.receive baseChain ownerCtx0 stOwner
          (some (.wccd_msg_updateOperator [(.opAdd, operator)])) with
      | .Ok (stOp, acts1) =>
          acts1.isEmpty &&
            WCCD.is_operator operator owner stOp &&
            match WCCD.operators_of owner stOp with
            | op :: _ => addrEq op operator
            | _ => false
      | .Err _ => false
    let transferHookOk :=
      let transfer : @WCCD.TransferParam TestBase :=
        { token_id := (), amount := 10, from_ := owner, to_ := hook }
      match WCCD.receive baseChain ownerCtx0 stOwner
          (some (.wccd_msg_transfer [transfer])) with
      | .Ok (stMoved, [.act_call to_ amount msg]) =>
          WCCD.balance_of hook stMoved == 10 &&
            addrEq to_ hook &&
            amount == 0 &&
            match (deserialize msg :
                Option (WCCD.TokenID × TokenAmount × TestAddress)) with
            | some ((), 10, from_) => addrEq from_ owner
            | _ => false
      | _ => false
    let balanceOfOk :=
      match WCCD.receive baseChain ownerCtx0 stOwner
          (some (.wccd_msg_balanceOf [owner, recipient] hook)) with
      | .Ok (stSame, [.act_call to_ amount msg]) =>
          stateEq stSame stOwner &&
            addrEq to_ hook &&
            amount == 0 &&
            match (deserialize msg :
                Option (List (WCCD.TokenID × TestAddress × TokenAmount))) with
            | some [((), addr1, bal1), ((), addr2, bal2)] =>
                addrEq addr1 owner && bal1 == 100 &&
                  addrEq addr2 recipient && bal2 == 0
            | _ => false
      | _ => false
    let burnOk :=
      match WCCD.receive baseChain ownerCtx0 stOwner
          (some (.wccd_msg_burn 15)) with
      | .Ok (stBurned, [.act_transfer to_ amount]) =>
          WCCD.balance_of owner stBurned == 85 &&
            addrEq to_ owner &&
            amount == 15
      | _ => false
    let rejectsInsufficient :=
      let transfer : @WCCD.TransferParam TestBase :=
        { token_id := (), amount := 101, from_ := owner, to_ := recipient }
      isErr (WCCD.receive baseChain ownerCtx0 stOwner
        (some (.wccd_msg_transfer [transfer])))
    mintOk && ownerTransferOk && operatorUpdateOk && transferHookOk &&
      balanceOfOk && burnOk && rejectsInsufficient

end ConCert.Examples.CIS1.Tests
