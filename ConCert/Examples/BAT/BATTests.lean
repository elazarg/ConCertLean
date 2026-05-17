/- Executable checks ported from examples/bat/*Tests.v. -/

import ConCert.Examples.BAT.BAT
import ConCert.Execution.Test.TestUtils
import ConCert.Execution.Test.TraceGens

namespace ConCert.Examples.BAT.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Examples.BAT

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

private def tokenStateEq
    (a b : @ConCert.Examples.EIP20.EIP20Token.State TestBase) : Bool :=
  a.total_supply == b.total_supply &&
    decide (FMap.elements a.balances = FMap.elements b.balances) &&
    decide (FMap.elements a.allowances = FMap.elements b.allowances)

private def stateEq (a b : @State TestBase) : Bool :=
  tokenStateEq a.token_state b.token_state &&
    a.initSupply == b.initSupply &&
    addrEq a.fundDeposit b.fundDeposit &&
    addrEq a.batFundDeposit b.batFundDeposit &&
    a.isFinalized == b.isFinalized &&
    a.fundingStart == b.fundingStart &&
    a.fundingEnd == b.fundingEnd &&
    a.tokenExchangeRate == b.tokenExchangeRate &&
    a.tokenCreationCap == b.tokenCreationCap &&
    a.tokenCreationMin == b.tokenCreationMin

private def setupEq (a b : @Setup TestBase) : Bool :=
  a.batFund == b.batFund &&
    addrEq a.fundDeposit_ b.fundDeposit_ &&
    addrEq a.batFundDeposit_ b.batFundDeposit_ &&
    a.fundingStart_ == b.fundingStart_ &&
    a.fundingEnd_ == b.fundingEnd_ &&
    a.tokenExchangeRate_ == b.tokenExchangeRate_ &&
    a.tokenCreationCap_ == b.tokenCreationCap_ &&
    a.tokenCreationMin_ == b.tokenCreationMin_

private def roundTripWith {A : Type} [Serializable A]
    (eqA : A → A → Bool) (a : A) : Bool :=
  match (deserialize (serialize a) : Option A) with
  | some b => eqA a b
  | none => false

private def baseSetup : @Setup TestBase :=
  { batFund := 1000,
    fundDeposit_ := fixedUser10,
    batFundDeposit_ := fixedUser11,
    fundingStart_ := 0,
    fundingEnd_ := 10,
    tokenExchangeRate_ := 10,
    tokenCreationCap_ := 2000,
    tokenCreationMin_ := 100 }

def serializationChecker : Checker :=
  checker <|
    let tokenState : @ConCert.Examples.EIP20.EIP20Token.State TestBase :=
      { total_supply := 25,
        balances := FMap.add fixedUser10 25 FMap.empty,
        allowances :=
          FMap.add fixedUser10 (FMap.add fixedUser11 3 FMap.empty) FMap.empty }
    let state : @State TestBase :=
      { token_state := tokenState,
        initSupply := 1000,
        fundDeposit := fixedUser10,
        batFundDeposit := fixedUser11,
        isFinalized := false,
        fundingStart := 0,
        fundingEnd := 10,
        tokenExchangeRate := 10,
        tokenCreationCap := 2000,
        tokenCreationMin := 100 }
    let msg : Msg := .tokenMsg (.approve fixedUser11 5)
    roundTripWith setupEq baseSetup &&
      roundTripWith stateEq state &&
      (match (deserialize (serialize msg) : Option Msg) with
       | some (.tokenMsg (.approve delegate amount)) =>
           addrEq delegate fixedUser11 && amount == 5
       | _ => false)

private def failedRefundState
    (owner buyer batFund : TestAddress) : @State TestBase :=
  let tokenState : @ConCert.Examples.EIP20.EIP20Token.State TestBase :=
    { total_supply := 25,
      balances := FMap.add buyer 25 FMap.empty,
      allowances := FMap.empty }
  { token_state := tokenState,
    initSupply := 1000,
    fundDeposit := owner,
    batFundDeposit := batFund,
    isFinalized := false,
    fundingStart := 0,
    fundingEnd := 10,
    tokenExchangeRate := 10,
    tokenCreationCap := 2000,
    tokenCreationMin := 100 }

def originalBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let batFund := fixedUser11
    let buyer : TestAddress := fixedLocalAddress 12 (by decide)
    let tokenRecipient : TestAddress := fixedLocalAddress 13 (by decide)
    let batAddr : TestAddress := fixedLocalAddress 133 (by decide)
    let ownerCtx := ctx owner batAddr 0 55
    let buyerCtxPay := ctx buyer batAddr 10 10
    match Original.init (chainAt 0) ownerCtx baseSetup with
    | .Err _ => false
    | .Ok st0 =>
        let initOk :=
          total_supply st0 == 1000 && get_balance batFund st0 == 1000
        let createOk :=
          match Original.receive (chainAt 5) buyerCtxPay st0
              (some .create_tokens) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
                total_supply st1 == 1100 &&
                get_balance buyer st1 == 100
          | .Err _ => false
        let tokenTransferBeforeFinalized :=
          match Original.receive (chainAt 5) (ctx batFund batAddr 0 0) st0
              (some (.tokenMsg (.transfer tokenRecipient 7))) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
                get_balance batFund st1 == 993 &&
                get_balance tokenRecipient st1 == 7
          | .Err _ => false
        let finalizeOk :=
          match Original.receive (chainAt 11) ownerCtx st0 (some .finalize) with
          | .Ok (st1, [.act_transfer to_ amount]) =>
              st1.isFinalized && addrEq to_ owner && amount == 55
          | _ => false
        let refundOk :=
          let failed := failedRefundState owner buyer batFund
          match Original.receive (chainAt 11) (ctx buyer batAddr 0 25)
              failed (some .refund) with
          | .Ok (st1, [.act_transfer to_ amount]) =>
              addrEq to_ buyer &&
                amount == 2 &&
                total_supply st1 == 0 &&
                get_balance buyer st1 == 0
          | _ => false
        initOk && createOk && tokenTransferBeforeFinalized && finalizeOk && refundOk

def fixedBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let batFund := fixedUser11
    let buyer : TestAddress := fixedLocalAddress 12 (by decide)
    let recipient : TestAddress := fixedLocalAddress 13 (by decide)
    let batAddr : TestAddress := fixedLocalAddress 133 (by decide)
    let ownerCtx := ctx owner batAddr 0 55
    let invalidSetup := { baseSetup with fundingEnd_ := 0 }
    match Fixed.init (chainAt 0) ownerCtx baseSetup with
    | .Err _ => false
    | .Ok st0 =>
        let invalidRejected :=
          isErr (Fixed.init (chainAt 0) ownerCtx invalidSetup)
        let batFundCannotBuy :=
          isErr (Fixed.receive (chainAt 5) (ctx batFund batAddr 10 10)
            st0 (some .create_tokens))
        let tokenTransferBeforeFinalizedRejected :=
          isErr (Fixed.receive (chainAt 5) (ctx batFund batAddr 0 0)
            st0 (some (.tokenMsg (.transfer recipient 7))))
        let finalizedState := { st0 with isFinalized := true }
        let tokenTransferAfterFinalized :=
          match Fixed.receive (chainAt 11) (ctx batFund batAddr 0 0)
              finalizedState (some (.tokenMsg (.transfer buyer 7))) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
                get_balance batFund st1 == 993 &&
                get_balance buyer st1 == 7
          | .Err _ => false
        invalidRejected && batFundCannotBuy &&
          tokenTransferBeforeFinalizedRejected && tokenTransferAfterFinalized

def altFixBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let batFund := fixedUser11
    let buyer : TestAddress := fixedLocalAddress 12 (by decide)
    let batAddr : TestAddress := fixedLocalAddress 133 (by decide)
    let ownerCtx := ctx owner batAddr 0 55
    match AltFix.init (chainAt 0) ownerCtx baseSetup with
    | .Err _ => false
    | .Ok st0 =>
        let initOk := total_supply st0 == 0 && get_balance batFund st0 == 0
        let finalizeMintsInitial :=
          match AltFix.receive (chainAt 5) (ctx buyer batAddr 10 10)
              st0 (some .create_tokens) with
          | .Err _ => false
          | .Ok (stBought, _) =>
              match AltFix.receive (chainAt 11) ownerCtx stBought
                  (some .finalize) with
              | .Ok (stFinal, [.act_transfer to_ amount]) =>
                  stFinal.isFinalized &&
                    total_supply stFinal == 1100 &&
                    get_balance batFund stFinal == 1000 &&
                    addrEq to_ owner &&
                    amount == 55
              | _ => false
        let refundKeepsRemainder :=
          let failed := failedRefundState owner buyer batFund
          match AltFix.receive (chainAt 11) (ctx buyer batAddr 0 25)
              failed (some .refund) with
          | .Ok (st1, [.act_transfer to_ amount]) =>
              addrEq to_ buyer &&
                amount == 2 &&
                total_supply st1 == 5 &&
                get_balance buyer st1 == 5
          | _ => false
        initOk && finalizeMintsInitial && refundKeepsRemainder

end ConCert.Examples.BAT.Tests
