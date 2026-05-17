/- Executable checks ported from examples/dexter2/Dexter2Tests.v. -/

import ConCert.Examples.Dexter2.Dexter2CPMM
import ConCert.Execution.Test.TestUtils
import ConCert.Execution.Test.TraceGens

namespace ConCert.Examples.Dexter2.Tests

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens

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

private def lqtStateEq
    (a b : @FA12.State TestBase) : Bool :=
  decide (FMap.elements a.tokens = FMap.elements b.tokens) &&
    decide (FMap.elements a.allowances = FMap.elements b.allowances) &&
    addrEq a.admin b.admin &&
    a.total_supply == b.total_supply

private def cpmmStateEq
    (a b : @CPMM.State TestBase) : Bool :=
  a.tokenPool == b.tokenPool &&
    a.xtzPool == b.xtzPool &&
    a.lqtTotal == b.lqtTotal &&
    a.selfIsUpdatingTokenPool == b.selfIsUpdatingTokenPool &&
    a.freezeBaker == b.freezeBaker &&
    addrEq a.manager b.manager &&
    addrEq a.tokenAddress b.tokenAddress &&
    a.tokenId == b.tokenId &&
    addrEq a.lqtAddress b.lqtAddress

private def roundTripWith {A : Type} [Serializable A]
    (eqA : A → A → Bool) (a : A) : Bool :=
  match (deserialize (serialize a) : Option A) with
  | some b => eqA a b
  | none => false

def serializationChecker : Checker :=
  checker <|
    let admin := fixedUser10
    let provider := fixedUser11
    let tokenAddr : TestAddress := fixedLocalAddress 129 (by decide)
    let lqtAddr : TestAddress := fixedLocalAddress 130 (by decide)
    let lqtState : @FA12.State TestBase :=
      { tokens := FMap.add provider 100 FMap.empty,
        allowances := FMap.add (provider, admin) 5 FMap.empty,
        admin := admin,
        total_supply := 100 }
    let cpmmState : @CPMM.State TestBase :=
      { tokenPool := 1000,
        xtzPool := 1000,
        lqtTotal := 100,
        selfIsUpdatingTokenPool := false,
        freezeBaker := false,
        manager := admin,
        tokenAddress := tokenAddr,
        tokenId := 0,
        lqtAddress := lqtAddr }
    let lqtMsg : @FA12.Msg TestBase :=
      .msg_mint_or_burn { quantity := 25, target := provider }
    let cpmmMsg : @CPMM.Msg TestBase :=
      .other_msg (.AddLiquidity
        { owner := provider,
          minLqtMinted := 1,
          maxTokensDeposited := 100,
          add_deadline := 10 })
    roundTripWith lqtStateEq lqtState &&
      roundTripWith cpmmStateEq cpmmState &&
      (match (deserialize (serialize lqtMsg) : Option (@FA12.Msg TestBase)) with
       | some (.msg_mint_or_burn p) => p.quantity == 25 && addrEq p.target provider
       | _ => false) &&
      (match (deserialize (serialize cpmmMsg) : Option (@CPMM.Msg TestBase)) with
       | some (.other_msg (.AddLiquidity p)) =>
           addrEq p.owner provider && p.minLqtMinted == 1 &&
             p.maxTokensDeposited == 100 && p.add_deadline == 10
       | _ => false)

def lqtBehaviorChecker : Checker :=
  checker <|
    let admin := fixedUser10
    let provider := fixedUser11
    let receiver : TestAddress := fixedLocalAddress 12 (by decide)
    let spender : TestAddress := fixedLocalAddress 13 (by decide)
    let lqtAddr : TestAddress := fixedLocalAddress 130 (by decide)
    let setup : @FA12.Setup TestBase :=
      { admin_ := admin, lqt_provider := provider, initial_pool := 100 }
    let ctxAdmin := ctx admin lqtAddr 0 0
    let ctxProvider := ctx provider lqtAddr 0 0
    let ctxSpender := ctx spender lqtAddr 0 0
    let ctxPayable := ctx provider lqtAddr 1 0
    match FA12.init baseChain ctxAdmin setup with
    | .Err _ => false
    | .Ok st0 =>
        let transferOk :=
          let transfer : @FA12.TransferParam TestBase :=
            { from_ := provider, to_ := receiver, value := 25 }
          match FA12.receive baseChain ctxProvider st0
              (some (.msg_transfer transfer)) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
                FA12.get_balance provider st1 == 75 &&
                FA12.get_balance receiver st1 == 25
          | .Err _ => false
        let delegatedTransferOk :=
          let approve : @FA12.ApproveParam TestBase :=
            { spender := spender, value_ := 10 }
          match FA12.receive baseChain ctxProvider st0
              (some (.msg_approve approve)) with
          | .Err _ => false
          | .Ok (stApproved, acts1) =>
              let transfer : @FA12.TransferParam TestBase :=
                { from_ := provider, to_ := receiver, value := 5 }
              match FA12.receive baseChain ctxSpender stApproved
                  (some (.msg_transfer transfer)) with
              | .Ok (st2, acts2) =>
                  acts1.isEmpty && acts2.isEmpty &&
                    FA12.get_allowance provider spender st2 == 5 &&
                    FA12.get_balance provider st2 == 95 &&
                    FA12.get_balance receiver st2 == 5
              | .Err _ => false
        let mintBurnOk :=
          let mint : @FA12.MintOrBurnParam TestBase :=
            { quantity := 40, target := receiver }
          let burn : @FA12.MintOrBurnParam TestBase :=
            { quantity := -20, target := provider }
          match FA12.receive baseChain ctxAdmin st0 (some (.msg_mint_or_burn mint)) with
          | .Err _ => false
          | .Ok (stMinted, acts1) =>
              match FA12.receive baseChain ctxAdmin st0
                  (some (.msg_mint_or_burn burn)) with
              | .Ok (stBurned, acts2) =>
                  acts1.isEmpty && acts2.isEmpty &&
                    FA12.get_balance receiver stMinted == 40 &&
                    stMinted.total_supply == 140 &&
                    FA12.get_balance provider stBurned == 80 &&
                    stBurned.total_supply == 80
              | .Err _ => false
        let callbackOk :=
          let callback : @FA12.Callback TestBase := { return_addr := receiver }
          let param : @FA12.GetBalanceParam TestBase :=
            { owner_ := provider, balance_callback := callback }
          match FA12.receive baseChain ctxProvider st0
              (some (.msg_get_balance param)) with
          | .Ok (stSame, [.act_call to_ amount msg]) =>
              lqtStateEq stSame st0 &&
                addrEq to_ receiver &&
                amount == 0 &&
                match (deserialize msg :
                    Option (FA12.FA12ReceiverMsg Unit)) with
                | some (.receive_balance_of 100) => true
                | _ => false
          | _ => false
        let rejectsPayable :=
          isErr (FA12.receive baseChain ctxPayable st0
            (some (.msg_get_total_supply
              { request_ := (),
                supply_callback := { return_addr := receiver } })))
        transferOk && delegatedTransferOk && mintBurnOk && callbackOk && rejectsPayable

private def nullAddr : TestAddress := fixedLocalAddress 0 (by decide)
private def tokenAddr : TestAddress := fixedLocalAddress 129 (by decide)
private def lqtAddr : TestAddress := fixedLocalAddress 130 (by decide)
private def cpmmAddr : TestAddress := fixedLocalAddress 131 (by decide)

private def setDelegateNone (_baker : CPMM.BakerAddress (Base := TestBase)) :
    List (@ActionBody TestBase) := []

private def cpmmSetup : @CPMM.Setup TestBase :=
  { lqtTotal_ := 100,
    manager_ := fixedUser10,
    tokenAddress_ := tokenAddr,
    tokenId_ := 0 }

private def pooledState : @CPMM.State TestBase :=
  { tokenPool := 1000,
    xtzPool := 1000,
    lqtTotal := 100,
    selfIsUpdatingTokenPool := false,
    freezeBaker := false,
    manager := fixedUser10,
    tokenAddress := tokenAddr,
    tokenId := 0,
    lqtAddress := lqtAddr }

def cpmmBehaviorChecker : Checker :=
  checker <|
    let manager := fixedUser10
    let trader := fixedUser11
    let otherDexter : TestAddress := fixedLocalAddress 132 (by decide)
    let managerCtx := ctx manager cpmmAddr 0 1000
    let traderCtx0 := ctx trader cpmmAddr 0 1000
    let traderCtx100 := ctx trader cpmmAddr 100 1100
    match CPMM.init nullAddr baseChain managerCtx cpmmSetup with
    | .Err _ => false
    | .Ok st0 =>
        let defaultOk :=
          match CPMM.receive nullAddr setDelegateNone baseChain
              (ctx trader cpmmAddr 25 1025) st0 none with
          | .Ok (st1, acts) => st1.xtzPool == 25 && acts.isEmpty
          | .Err _ => false
        let setLqtOk :=
          match CPMM.receive nullAddr setDelegateNone baseChain managerCtx st0
              (some (.other_msg (.SetLqtAddress lqtAddr))) with
          | .Ok (st1, acts) => addrEq st1.lqtAddress lqtAddr && acts.isEmpty
          | .Err _ => false
        let addLiquidityOk :=
          let param : @CPMM.AddLiquidityParam TestBase :=
            { owner := trader,
              minLqtMinted := 1,
              maxTokensDeposited := 100,
              add_deadline := 10 }
          match CPMM.receive nullAddr setDelegateNone baseChain traderCtx100
              pooledState (some (.other_msg (.AddLiquidity param))) with
          | .Ok (st1, [opToken, opLqt]) =>
              let opTokenOk :=
                match opToken with
                | .act_call to_ amount msg =>
                    addrEq to_ tokenAddr && amount == 0 &&
                      match (deserialize msg :
                          Option (@ConCert.Examples.FA2.Msg TestBase)) with
                      | some (.msg_transfer [transfer]) =>
                          transfer.txs.length == 1 &&
                            addrEq transfer.from_ trader &&
                            match transfer.txs.head? with
                            | some dst =>
                                addrEq dst.to_ cpmmAddr && dst.amount == 100
                            | none => false
                      | _ => false
                | _ => false
              let opLqtOk :=
                match opLqt with
                | .act_call to_ amount msg =>
                    addrEq to_ lqtAddr && amount == 0 &&
                      match (deserialize msg : Option (@FA12.Msg TestBase)) with
                      | some (.msg_mint_or_burn p) =>
                          p.quantity == 10 && addrEq p.target trader
                      | _ => false
                | _ => false
              st1.lqtTotal == 110 &&
                st1.tokenPool == 1100 &&
                st1.xtzPool == 1100 &&
                opTokenOk && opLqtOk
          | _ => false
        let xtzToTokenOk :=
          let param : @CPMM.XtzToTokenParam TestBase :=
            { tokens_to := trader, minTokensBought := 1, xtt_deadline := 10 }
          match CPMM.receive nullAddr setDelegateNone baseChain traderCtx100
              pooledState (some (.other_msg (.XtzToToken param))) with
          | .Ok (st1, [_]) =>
              st1.xtzPool == 1100 && st1.tokenPool == 910
          | _ => false
        let tokenToXtzOk :=
          let param : @CPMM.TokenToXtzParam TestBase :=
            { xtz_to := trader,
              tokensSold := 100,
              minXtzBought := 1,
              ttx_deadline := 10 }
          match CPMM.receive nullAddr setDelegateNone baseChain traderCtx0
              pooledState (some (.other_msg (.TokenToXtz param))) with
          | .Ok (st1, [_, .act_transfer to_ amount]) =>
              st1.tokenPool == 1100 &&
                st1.xtzPool == 910 &&
                addrEq to_ trader &&
                amount == 90
          | _ => false
        let updatePoolOk :=
          match CPMM.receive nullAddr setDelegateNone baseChain traderCtx0
              pooledState (some (.other_msg .UpdateTokenPool)) with
          | .Err _ => false
          | .Ok (stUpdating, [_]) =>
              let response : ConCert.Examples.FA2.BalanceOfResponse :=
                { request := { owner := cpmmAddr, bal_req_token_id := 0 },
                  balance := 777 }
              let tokenCtx := ctx tokenAddr cpmmAddr 0 1000
              match CPMM.receive nullAddr setDelegateNone baseChain tokenCtx
                  stUpdating (some (.receive_balance_of_param [response])) with
              | .Ok (stUpdated, acts) =>
                  stUpdated.tokenPool == 777 &&
                    !stUpdated.selfIsUpdatingTokenPool &&
                    acts.isEmpty
              | .Err _ => false
          | .Ok _ => false
        let tokenToTokenOk :=
          let param : @CPMM.TokenToTokenParam TestBase :=
            { outputDexterContract := otherDexter,
              to_ := trader,
              minTokensBought_ := 1,
              tokensSold_ := 100,
              ttt_deadline := 10 }
          match CPMM.receive nullAddr setDelegateNone baseChain traderCtx0
              pooledState (some (.other_msg (.TokenToToken param))) with
          | .Ok (st1, [_, .act_call to_ amount msg]) =>
              st1.tokenPool == 1100 &&
                st1.xtzPool == 910 &&
                addrEq to_ otherDexter &&
                amount == 90 &&
                match (deserialize msg : Option (@CPMM.Msg TestBase)) with
                | some (.other_msg (.XtzToToken p)) =>
                    addrEq p.tokens_to trader && p.minTokensBought == 1
                | _ => false
          | _ => false
        defaultOk && setLqtOk && addLiquidityOk && xtzToTokenOk &&
          tokenToXtzOk && updatePoolOk && tokenToTokenOk

end ConCert.Examples.Dexter2.Tests
