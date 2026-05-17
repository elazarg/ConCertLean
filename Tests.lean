import ConCert

open ConCert.Execution.SerializableBase
open ConCert.Execution.SerializableInstances
open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainBuilder
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TraceGens
open ConCert.Utils.Env

#guard ConCert.Utils.StringExtra.to_upper "abZ9" == "ABZ9"
#guard ConCert.Utils.StringExtra.str_rev "abc" == "cba"
#guard ConCert.Utils.Extras.with_default 7 (none : Option Nat) == 7
#guard (deserialize (serialize (42 : Nat)) : Option Nat) == some 42
#guard (deserialize (serialize (true : Bool)) : Option Bool) == some true
#guard (LocalChain.lc_height (lc_initial 8)) == 0
#guard ((([] : Env Nat) # ["x" ~> 3]) # ("x")) == some 3
#guard
  (ConCert.Execution.Test.TestUtils.contract_base_addr
    (Base := LocalChainBase ConCert.Execution.Test.TestUtils.AddrSize)).val == 128
#guard
  ConCert.Execution.Test.TestUtils.split_at_first_satisfying
    (fun n : Nat => n == 3) [1, 2, 3, 4] == some ([1, 2, 3], [4])

namespace PiggyBankSmoke

local instance : ChainBase := LocalChainBase 8

private def addr0 : ConCert.Execution.BoundedN 8 := ⟨0, by decide⟩
private def addr1 : ConCert.Execution.BoundedN 8 := ⟨1, by decide⟩
private def contractAddr : ConCert.Execution.BoundedN 8 := ⟨4, by decide⟩

private def chain : Chain :=
  { chain_height := 0, current_slot := 0, finalized_height := 0 }

private def ctx (sender : ConCert.Execution.BoundedN 8) (amount : Amount) :
    @ContractCallContext (LocalChainBase 8) :=
  { ctx_origin := sender,
    ctx_from := sender,
    ctx_contract_address := contractAddr,
    ctx_contract_balance := amount,
    ctx_amount := amount }

private def intactState : @ConCert.Examples.PiggyBank.State (LocalChainBase 8) :=
  { balance := 5,
    owner := addr0,
    piggyState := ConCert.Examples.PiggyBank.PiggyState.Intact }

private def initSmoke :=
  ConCert.Examples.PiggyBank.init chain (ctx addr0 5) ()

#guard
  match initSmoke with
  | .Ok st =>
      st.balance == 5 &&
      (match st.piggyState with
       | ConCert.Examples.PiggyBank.PiggyState.Intact => true
       | _ => false)
  | _ => false

private def insertSmoke :=
  ConCert.Examples.PiggyBank.receive chain (ctx addr1 7) intactState
    (some ConCert.Examples.PiggyBank.Msg.Insert)

#guard
  match insertSmoke with
  | .Ok (st, acts) =>
      st.balance == 12 &&
      acts.isEmpty &&
      (match st.piggyState with
       | ConCert.Examples.PiggyBank.PiggyState.Intact => true
       | _ => false)
  | _ => false

private def smashSmoke :=
  ConCert.Examples.PiggyBank.receive chain (ctx addr0 2) intactState
    (some ConCert.Examples.PiggyBank.Msg.Smash)

#guard
  match smashSmoke with
  | .Ok (st, acts) =>
      st.balance == 0 &&
      (match st.piggyState with
       | ConCert.Examples.PiggyBank.PiggyState.Smashed => true
       | _ => false) &&
      (match acts with
       | [.act_transfer to_ amount] =>
           (LocalChainBase 8).address_eqb to_ addr0 && amount == 7
       | _ => false)
  | _ => false

end PiggyBankSmoke

def counterSafeSmoke [BaseTypes : ChainBase] :=
  ConCert.Examples.Counter.counter_safe (BaseTypes := BaseTypes)

def escrowCorrectSmoke [Base : ChainBase] {Cb : @ChainBuilderType Base} :=
  @ConCert.Examples.Escrow.EscrowCorrectness.escrow_correct Base Cb

namespace GeneratedProperties

open ConCert.Execution.Test.TestUtils

local instance : ChainBase := TestBase

private def cfg : CheckerConfig := strictCheckerConfig

private def addrEq (a b : TestAddress) : Bool :=
  TestBase.address_eqb a b

private def roundTripWith {A : Type} [Serializable A]
    (eq : A → A → Bool) (a : A) : Bool :=
  match (deserialize (serialize a) : Option A) with
  | some a' => eq a a'
  | none => false

private def listEq {A : Type} (eq : A → A → Bool) : List A → List A → Bool
  | [], [] => true
  | a :: as, b :: bs => eq a b && listEq eq as bs
  | _, _ => false

private def optionEq {A : Type} (eq : A → A → Bool) : Option A → Option A → Bool
  | none, none => true
  | some a, some b => eq a b
  | _, _ => false

private def gSmallNat : G Nat :=
  chooseNatBetween 0 1000 (by decide)

private def gSmallInt : G Int :=
  chooseIntBetween (-1000) 1000 (by decide)

private def gSmallAmount : G Amount :=
  chooseAmountBetween (-50) 150 (by decide)

private def gListOf {A : Type} (maxLen : Nat) (gA : G A) : G (List A) := do
  let len ← chooseNatBetween 0 maxLen (Nat.zero_le maxLen)
  let rec loop : Nat → G (List A)
    | 0 => return []
    | n + 1 => do
        let x ← gA
        let xs ← loop n
        return x :: xs
  loop len

private def gNatList : G (List Nat) := do
  let len ← chooseNatBetween 0 10 (by decide)
  let rec loop : Nat → G (List Nat)
    | 0 => return []
    | n + 1 => do
        let x ← gSmallNat
        let xs ← loop n
        return x :: xs
  loop len

private def gCounterMsg : G ConCert.Examples.Counter.Msg := do
  let n ← chooseIntBetween (-20) 20 (by decide)
  let inc ← chooseBool
  return if inc then .Inc n else .Dec n

private def gCounterState : G ConCert.Examples.Counter.State := do
  let count ← gSmallInt
  let owner ← gLocalAccountAddress
  return { count, owner }

private def counterMsgEq :
    ConCert.Examples.Counter.Msg → ConCert.Examples.Counter.Msg → Bool
  | .Inc a, .Inc b => a == b
  | .Dec a, .Dec b => a == b
  | _, _ => false

private def counterStateEq
    (a b : ConCert.Examples.Counter.State) : Bool :=
  a.count == b.count && addrEq a.owner b.owner

private def gPiggyStateTag : G ConCert.Examples.PiggyBank.PiggyState := do
  let intact ← chooseBool
  return if intact then .Intact else .Smashed

private def gPiggyMsg : G ConCert.Examples.PiggyBank.Msg := do
  let insert ← chooseBool
  return if insert then .Insert else .Smash

private def gPiggyState : G ConCert.Examples.PiggyBank.State := do
  let balance ← gSmallAmount
  let owner ← gLocalAccountAddress
  let piggyState ← gPiggyStateTag
  return { balance, owner, piggyState }

private def piggyStateTagEq
    (a b : ConCert.Examples.PiggyBank.PiggyState) : Bool :=
  decide (a = b)

private def piggyMsgEq
    (a b : ConCert.Examples.PiggyBank.Msg) : Bool :=
  decide (a = b)

private def piggyStateEq
    (a b : ConCert.Examples.PiggyBank.State) : Bool :=
  a.balance == b.balance && addrEq a.owner b.owner &&
    piggyStateTagEq a.piggyState b.piggyState

private def gEscrowNextStep : G ConCert.Examples.Escrow.NextStep := do
  let n ← chooseNatBetween 0 3 (by decide)
  return match n with
    | 0 => .buyer_commit
    | 1 => .buyer_confirm
    | 2 => .withdrawals
    | _ => .no_next_step

private def gEscrowMsg : G ConCert.Examples.Escrow.Msg := do
  let n ← chooseNatBetween 0 2 (by decide)
  return match n with
    | 0 => .commit_money
    | 1 => .confirm_item_received
    | _ => .withdraw

private def gEscrowSetup : G ConCert.Examples.Escrow.Setup := do
  return { setup_buyer := (← gLocalAccountAddress) }

private def gEscrowState : G ConCert.Examples.Escrow.State := do
  let last_action ← chooseNatBetween 0 100 (by decide)
  let next_step ← gEscrowNextStep
  let seller ← gLocalAccountAddress
  let buyer ← gLocalAccountAddress
  let seller_withdrawable ← gSmallAmount
  let buyer_withdrawable ← gSmallAmount
  return { last_action := last_action,
           next_step := next_step,
           seller := seller,
           buyer := buyer,
           seller_withdrawable := seller_withdrawable,
           buyer_withdrawable := buyer_withdrawable }

private def escrowNextStepEq
    (a b : ConCert.Examples.Escrow.NextStep) : Bool :=
  decide (a = b)

private def escrowMsgEq
    (a b : ConCert.Examples.Escrow.Msg) : Bool :=
  match a, b with
  | .commit_money, .commit_money => true
  | .confirm_item_received, .confirm_item_received => true
  | .withdraw, .withdraw => true
  | _, _ => false

private def escrowSetupEq
    (a b : ConCert.Examples.Escrow.Setup) : Bool :=
  addrEq a.setup_buyer b.setup_buyer

private def escrowStateEq
    (a b : ConCert.Examples.Escrow.State) : Bool :=
  a.last_action == b.last_action &&
    escrowNextStepEq a.next_step b.next_step &&
    addrEq a.seller b.seller &&
    addrEq a.buyer b.buyer &&
    a.seller_withdrawable == b.seller_withdrawable &&
    a.buyer_withdrawable == b.buyer_withdrawable

private def gStackOp : G ConCert.Examples.StackInterpreter.Op := do
  let n ← chooseNatBetween 0 5 (by decide)
  return match n with
    | 0 => .Add
    | 1 => .Sub
    | 2 => .Mult
    | 3 => .Lt
    | 4 => .Le
    | _ => .Equal

private def gStackKey : G ConCert.Examples.StackInterpreter.MapKey := do
  let n ← chooseNatBetween 0 2 (by decide)
  let i ← chooseIntBetween (-5) 5 (by decide)
  let key :=
    match n with
    | 0 => "x"
    | 1 => "y"
    | _ => "z"
  return (key, i)

private def gStackValue : G ConCert.Examples.StackInterpreter.Value := do
  let useBool ← chooseBool
  if useBool then
    return .BVal (← chooseBool)
  else
    return .ZVal (← chooseIntBetween (-20) 20 (by decide))

private def gStackInstruction : G ConCert.Examples.StackInterpreter.Instruction := do
  let n ← chooseNatBetween 0 6 (by decide)
  match n with
  | 0 => return .IPushZ (← chooseIntBetween (-20) 20 (by decide))
  | 1 => return .IPushB (← chooseBool)
  | 2 => return .IObs (← gStackKey)
  | 3 => return .IIf
  | 4 => return .IElse
  | 5 => return .IEndIf
  | _ => return .IOp (← gStackOp)

private def gStackProgram : G (List ConCert.Examples.StackInterpreter.Instruction) := do
  let len ← chooseNatBetween 0 8 (by decide)
  let rec loop : Nat → G (List ConCert.Examples.StackInterpreter.Instruction)
    | 0 => return []
    | n + 1 => do
        let i ← gStackInstruction
        let is ← loop n
        return i :: is
  loop len

private def gStackExtMap : G ConCert.Examples.StackInterpreter.ExtMap := do
  let len ← chooseNatBetween 0 4 (by decide)
  let rec loop : Nat → G (List (ConCert.Examples.StackInterpreter.MapKey ×
      ConCert.Examples.StackInterpreter.Value))
    | 0 => return []
    | n + 1 => do
        let k ← gStackKey
        let v ← gStackValue
        let rest ← loop n
        return (k, v) :: rest
  return FMap.of_list (← loop len)

private def gStackMsg : G ConCert.Examples.StackInterpreter.Msg := do
  let program ← gStackProgram
  let ext ← gStackExtMap
  return (program, ext)

private def stackOpEq (a b : ConCert.Examples.StackInterpreter.Op) : Bool :=
  decide (a = b)

private def stackInstructionEq
    (a b : ConCert.Examples.StackInterpreter.Instruction) : Bool :=
  decide (a = b)

private def stackValueEq (a b : ConCert.Examples.StackInterpreter.Value) : Bool :=
  decide (a = b)

private def stackMapEq
    (a b : ConCert.Examples.StackInterpreter.ExtMap) : Bool :=
  decide (FMap.elements a = FMap.elements b)

private def stackMsgEq
    (a b : ConCert.Examples.StackInterpreter.Msg) : Bool :=
  decide (a.1 = b.1) && stackMapEq a.2 b.2

private def gEIP20Msg : G ConCert.Examples.EIP20.EIP20Token.Msg := do
  let n ← chooseNatBetween 0 2 (by decide)
  let a ← gLocalAccountAddress
  let b ← gLocalAccountAddress
  let amount ← chooseNatBetween 0 100 (by decide)
  return match n with
    | 0 => .transfer a amount
    | 1 => .transfer_from a b amount
    | _ => .approve a amount

private def gEIP20Setup : G ConCert.Examples.EIP20.EIP20Token.Setup := do
  let owner ← gLocalAccountAddress
  let init_amount ← chooseNatBetween 0 1000 (by decide)
  return { owner, init_amount }

private def gEIP20State : G ConCert.Examples.EIP20.EIP20Token.State := do
  let owner ← gLocalAccountAddress
  let spender ← gLocalAccountAddress
  let total_supply ← chooseNatBetween 0 1000 (by decide)
  let owner_balance ← chooseNatBetween 0 total_supply (Nat.zero_le total_supply)
  let allowance ← chooseNatBetween 0 total_supply (Nat.zero_le total_supply)
  let balances := FMap.add owner owner_balance FMap.empty
  let allowances :=
    FMap.add owner (FMap.add spender allowance FMap.empty) FMap.empty
  return { total_supply, balances, allowances }

private def eip20MsgEq
    (a b : ConCert.Examples.EIP20.EIP20Token.Msg) : Bool :=
  match a, b with
  | .transfer toA amountA, .transfer toB amountB =>
      addrEq toA toB && amountA == amountB
  | .transfer_from fromA toA amountA, .transfer_from fromB toB amountB =>
      addrEq fromA fromB && addrEq toA toB && amountA == amountB
  | .approve delegateA amountA, .approve delegateB amountB =>
      addrEq delegateA delegateB && amountA == amountB
  | _, _ => false

private def eip20SetupEq
    (a b : ConCert.Examples.EIP20.EIP20Token.Setup) : Bool :=
  addrEq a.owner b.owner && a.init_amount == b.init_amount

private def eip20MapNatEq
    (a b : FMap TestAddress Nat) : Bool :=
  decide (FMap.elements a = FMap.elements b)

private def eip20AllowanceMapEq
    (a b : FMap TestAddress (FMap TestAddress Nat)) : Bool :=
  decide (FMap.elements a = FMap.elements b)

private def eip20StateEq
    (a b : ConCert.Examples.EIP20.EIP20Token.State) : Bool :=
  a.total_supply == b.total_supply &&
    eip20MapNatEq a.balances b.balances &&
    eip20AllowanceMapEq a.allowances b.allowances

private def gITokenMsg : G ConCert.Examples.ITokenBuggy.Msg := do
  let n ← chooseNatBetween 0 3 (by decide)
  let a ← gLocalAccountAddress
  let b ← gLocalAccountAddress
  let amount ← chooseNatBetween 0 100 (by decide)
  return match n with
    | 0 => .transfer_from a b amount
    | 1 => .approve a amount
    | 2 => .mint amount
    | _ => .burn amount

private def gITokenSetup : G ConCert.Examples.ITokenBuggy.Setup := do
  let owner ← gLocalAccountAddress
  let init_amount ← chooseNatBetween 0 1000 (by decide)
  return { owner, init_amount }

private def gITokenState : G ConCert.Examples.ITokenBuggy.State := do
  let owner ← gLocalAccountAddress
  let spender ← gLocalAccountAddress
  let total_supply ← chooseNatBetween 0 1000 (by decide)
  let owner_balance ← chooseNatBetween 0 total_supply (Nat.zero_le total_supply)
  let allowance ← chooseNatBetween 0 total_supply (Nat.zero_le total_supply)
  let balances := FMap.add owner owner_balance FMap.empty
  let allowances :=
    FMap.add owner (FMap.add spender allowance FMap.empty) FMap.empty
  return { total_supply, balances, allowances }

private def iTokenMsgEq
    (a b : ConCert.Examples.ITokenBuggy.Msg) : Bool :=
  match a, b with
  | .transfer_from fromA toA amountA, .transfer_from fromB toB amountB =>
      addrEq fromA fromB && addrEq toA toB && amountA == amountB
  | .approve delegateA amountA, .approve delegateB amountB =>
      addrEq delegateA delegateB && amountA == amountB
  | .mint amountA, .mint amountB => amountA == amountB
  | .burn amountA, .burn amountB => amountA == amountB
  | _, _ => false

private def iTokenSetupEq
    (a b : ConCert.Examples.ITokenBuggy.Setup) : Bool :=
  addrEq a.owner b.owner && a.init_amount == b.init_amount

private def iTokenStateEq
    (a b : ConCert.Examples.ITokenBuggy.State) : Bool :=
  a.total_supply == b.total_supply &&
    eip20MapNatEq a.balances b.balances &&
    eip20AllowanceMapEq a.allowances b.allowances

private def gFA12Callback : G ConCert.Examples.FA1_2.Callback := do
  return { return_addr := (← gLocalAccountAddress) }

private def gFA12TransferParam : G ConCert.Examples.FA1_2.TransferParam := do
  let from_ ← gLocalAccountAddress
  let to_ ← gLocalAccountAddress
  let value ← chooseNatBetween 0 100 (by decide)
  return { from_, to_, value }

private def gFA12ApproveParam : G ConCert.Examples.FA1_2.ApproveParam := do
  let spender ← gLocalAccountAddress
  let value_ ← chooseNatBetween 0 100 (by decide)
  return { spender, value_ }

private def gFA12GetAllowanceParam : G ConCert.Examples.FA1_2.GetAllowanceParam := do
  let owner ← gLocalAccountAddress
  let spender ← gLocalAccountAddress
  let allowance_callback ← gFA12Callback
  return { request := (owner, spender), allowance_callback }

private def gFA12GetBalanceParam : G ConCert.Examples.FA1_2.GetBalanceParam := do
  let owner_ ← gLocalAccountAddress
  let balance_callback ← gFA12Callback
  return { owner_, balance_callback }

private def gFA12GetTotalSupplyParam :
    G ConCert.Examples.FA1_2.GetTotalSupplyParam := do
  let supply_callback ← gFA12Callback
  return { request_ := (), supply_callback }

private def gFA12ReceiverMsgUnit :
    G (ConCert.Examples.FA1_2.FA12ReceiverMsg Unit) := do
  let n ← chooseNatBetween 0 3 (by decide)
  let amount ← chooseNatBetween 0 1000 (by decide)
  return match n with
    | 0 => .receive_allowance amount
    | 1 => .receive_balance_of amount
    | 2 => .receive_total_supply amount
    | _ => .other_msg ()

private def gFA12Msg : G ConCert.Examples.FA1_2.Msg := do
  let n ← chooseNatBetween 0 4 (by decide)
  match n with
  | 0 => return .transfer (← gFA12TransferParam)
  | 1 => return .approve (← gFA12ApproveParam)
  | 2 => return .getAllowance (← gFA12GetAllowanceParam)
  | 3 => return .getBalance (← gFA12GetBalanceParam)
  | _ => return .getTotalSupply (← gFA12GetTotalSupplyParam)

private def gFA12Setup : G ConCert.Examples.FA1_2.Setup := do
  let lqt_provider ← gLocalAccountAddress
  let initial_pool ← chooseNatBetween 0 1000 (by decide)
  return { lqt_provider, initial_pool }

private def gFA12State : G ConCert.Examples.FA1_2.State := do
  let owner ← gLocalAccountAddress
  let recipient ← gLocalAccountAddress
  let spender ← gLocalAccountAddress
  let total_supply ← chooseNatBetween 0 1000 (by decide)
  let owner_balance ← chooseNatBetween 0 total_supply (Nat.zero_le total_supply)
  let recipient_balance ← chooseNatBetween 0 total_supply (Nat.zero_le total_supply)
  let allowance ← chooseNatBetween 0 total_supply (Nat.zero_le total_supply)
  let tokens :=
    FMap.add owner owner_balance
      (FMap.add recipient recipient_balance FMap.empty)
  let allowances := FMap.add (owner, spender) allowance FMap.empty
  return { tokens, allowances, total_supply }

private def fa12CallbackEq
    (a b : ConCert.Examples.FA1_2.Callback) : Bool :=
  addrEq a.return_addr b.return_addr

private def fa12TransferParamEq
    (a b : ConCert.Examples.FA1_2.TransferParam) : Bool :=
  addrEq a.from_ b.from_ && addrEq a.to_ b.to_ && a.value == b.value

private def fa12ApproveParamEq
    (a b : ConCert.Examples.FA1_2.ApproveParam) : Bool :=
  addrEq a.spender b.spender && a.value_ == b.value_

private def fa12GetAllowanceParamEq
    (a b : ConCert.Examples.FA1_2.GetAllowanceParam) : Bool :=
  addrEq a.request.1 b.request.1 &&
    addrEq a.request.2 b.request.2 &&
    fa12CallbackEq a.allowance_callback b.allowance_callback

private def fa12GetBalanceParamEq
    (a b : ConCert.Examples.FA1_2.GetBalanceParam) : Bool :=
  addrEq a.owner_ b.owner_ &&
    fa12CallbackEq a.balance_callback b.balance_callback

private def fa12GetTotalSupplyParamEq
    (a b : ConCert.Examples.FA1_2.GetTotalSupplyParam) : Bool :=
  fa12CallbackEq a.supply_callback b.supply_callback

private def fa12ReceiverMsgEq
    (a b : ConCert.Examples.FA1_2.FA12ReceiverMsg Unit) : Bool :=
  match a, b with
  | .receive_allowance a, .receive_allowance b => a == b
  | .receive_balance_of a, .receive_balance_of b => a == b
  | .receive_total_supply a, .receive_total_supply b => a == b
  | .other_msg (), .other_msg () => true
  | _, _ => false

private def fa12MsgEq
    (a b : ConCert.Examples.FA1_2.Msg) : Bool :=
  match a, b with
  | .transfer a, .transfer b => fa12TransferParamEq a b
  | .approve a, .approve b => fa12ApproveParamEq a b
  | .getAllowance a, .getAllowance b => fa12GetAllowanceParamEq a b
  | .getBalance a, .getBalance b => fa12GetBalanceParamEq a b
  | .getTotalSupply a, .getTotalSupply b => fa12GetTotalSupplyParamEq a b
  | _, _ => false

private def fa12AllowanceEq
    (a b : FMap (TestAddress × TestAddress) Nat) : Bool :=
  decide (FMap.elements a = FMap.elements b)

private def fa12StateEq
    (a b : ConCert.Examples.FA1_2.State) : Bool :=
  eip20MapNatEq a.tokens b.tokens &&
    fa12AllowanceEq a.allowances b.allowances &&
    a.total_supply == b.total_supply

private def fa12SetupEq
    (a b : ConCert.Examples.FA1_2.Setup) : Bool :=
  addrEq a.lqt_provider b.lqt_provider && a.initial_pool == b.initial_pool

private def gFA2SmallTokenId : G ConCert.Examples.FA2.TokenId :=
  chooseNatBetween 0 3 (by decide)

private def gFA2Callback {A : Type}
    (gA : G A) : G (ConCert.Examples.FA2.Callback A) := do
  let includeBlob ← chooseBool
  let blob ←
    (if includeBlob then
      (do
        let a ← gA
        pure (some a))
    else
      pure none)
  let return_addr ← gLocalAccountAddress
  return { blob, return_addr }

private def gFA2TransferDestination :
    G ConCert.Examples.FA2.TransferDestination := do
  let to_ ← gLocalAccountAddress
  let dst_token_id ← gFA2SmallTokenId
  let amount ← chooseNatBetween 0 100 (by decide)
  return { to_, dst_token_id, amount }

private def gFA2Transfer : G ConCert.Examples.FA2.Transfer := do
  let from_ ← gLocalAccountAddress
  let tx ← gFA2TransferDestination
  let includeCallback ← chooseBool
  let callback ← gLocalAccountAddress
  return { from_ := from_,
           txs := [tx],
           sender_callback_addr := if includeCallback then some callback else none }

private def gFA2BalanceOfRequest :
    G ConCert.Examples.FA2.BalanceOfRequest := do
  let owner ← gLocalAccountAddress
  let bal_req_token_id ← gFA2SmallTokenId
  return { owner, bal_req_token_id }

private def gFA2BalanceOfResponse :
    G ConCert.Examples.FA2.BalanceOfResponse := do
  let request ← gFA2BalanceOfRequest
  let balance ← chooseNatBetween 0 1000 (by decide)
  return { request, balance }

private def gFA2TotalSupplyResponse :
    G ConCert.Examples.FA2.TotalSupplyResponse := do
  let supply_resp_token_id ← gFA2SmallTokenId
  let total_supply ← chooseNatBetween 0 1000 (by decide)
  return { supply_resp_token_id, total_supply }

private def gFA2TokenMetadata :
    G ConCert.Examples.FA2.TokenMetadata := do
  let metadata_token_id ← gFA2SmallTokenId
  let metadata_decimals ← chooseNatBetween 0 18 (by decide)
  return { metadata_token_id, metadata_decimals }

private def gFA2BalanceOfParam :
    G ConCert.Examples.FA2.BalanceOfParam := do
  let request ← gFA2BalanceOfRequest
  let bal_callback ← gFA2Callback (gListOf 2 gFA2BalanceOfResponse)
  return { bal_requests := [request], bal_callback }

private def gFA2TotalSupplyParam :
    G ConCert.Examples.FA2.TotalSupplyParam := do
  let token_id ← gFA2SmallTokenId
  let supply_param_callback ← gFA2Callback (gListOf 2 gFA2TotalSupplyResponse)
  return { supply_param_token_ids := [token_id], supply_param_callback }

private def gFA2TokenMetadataParam :
    G ConCert.Examples.FA2.TokenMetadataParam := do
  let token_id ← gFA2SmallTokenId
  let metadata_callback ← gFA2Callback (gListOf 2 gFA2TokenMetadata)
  return { metadata_token_ids := [token_id], metadata_callback }

private def gFA2OperatorTokens :
    G ConCert.Examples.FA2.OperatorTokens := do
  let all ← chooseBool
  if all then
    return .all_tokens
  else do
    let tokenId ← gFA2SmallTokenId
    return .some_tokens [tokenId]

private def gFA2OperatorParam :
    G ConCert.Examples.FA2.OperatorParam := do
  let op_param_owner ← gLocalAccountAddress
  let op_param_operator ← gLocalAccountAddress
  let op_param_tokens ← gFA2OperatorTokens
  return { op_param_owner, op_param_operator, op_param_tokens }

private def gFA2UpdateOperator :
    G ConCert.Examples.FA2.UpdateOperator := do
  let param ← gFA2OperatorParam
  let add ← chooseBool
  return if add then .add_operator param else .remove_operator param

private def gFA2SelfTransferPolicy :
    G ConCert.Examples.FA2.SelfTransferPolicy := do
  let permitted ← chooseBool
  return if permitted then .self_transfer_permitted else .self_transfer_denied

private def gFA2OperatorTransferPolicy :
    G ConCert.Examples.FA2.OperatorTransferPolicy := do
  let permitted ← chooseBool
  return if permitted then
    .operator_transfer_permitted
  else
    .operator_transfer_denied

private def gFA2OwnerTransferPolicy :
    G ConCert.Examples.FA2.OwnerTransferPolicy := do
  let n ← chooseNatBetween 0 2 (by decide)
  return match n with
    | 0 => .owner_no_op
    | 1 => .optional_owner_hook
    | _ => .required_owner_hook

private def gFA2PermissionsDescriptor :
    G ConCert.Examples.FA2.PermissionsDescriptor := do
  let descr_self ← gFA2SelfTransferPolicy
  let descr_operator ← gFA2OperatorTransferPolicy
  let descr_receiver ← gFA2OwnerTransferPolicy
  let descr_sender ← gFA2OwnerTransferPolicy
  let hasCustom ← chooseBool
  let custom ← gLocalAccountAddress
  return { descr_self := descr_self,
           descr_operator := descr_operator,
           descr_receiver := descr_receiver,
           descr_sender := descr_sender,
           descr_custom := if hasCustom then some custom else none }

private def gFA2IsOperatorResponse :
    G ConCert.Examples.FA2.IsOperatorResponse := do
  let operator ← gFA2OperatorParam
  let is_operator ← chooseBool
  return { operator, is_operator }

private def gFA2IsOperatorParam :
    G ConCert.Examples.FA2.IsOperatorParam := do
  let is_operator_operator ← gFA2OperatorParam
  let is_operator_callback ← gFA2Callback gFA2IsOperatorResponse
  return { is_operator_operator, is_operator_callback }

private def gFA2TransferDestinationDescriptor :
    G ConCert.Examples.FA2.TransferDestinationDescriptor := do
  let hasTo ← chooseBool
  let to_ ← gLocalAccountAddress
  let transfer_dst_descr_token_id ← gFA2SmallTokenId
  let transfer_dst_descr_amount ← chooseNatBetween 0 100 (by decide)
  return { transfer_dst_descr_to_ := if hasTo then some to_ else none,
           transfer_dst_descr_token_id := transfer_dst_descr_token_id,
           transfer_dst_descr_amount := transfer_dst_descr_amount }

private def gFA2TransferDescriptor :
    G ConCert.Examples.FA2.TransferDescriptor := do
  let hasFrom ← chooseBool
  let from_ ← gLocalAccountAddress
  let tx ← gFA2TransferDestinationDescriptor
  return { transfer_descr_from_ := if hasFrom then some from_ else none,
           transfer_descr_txs := [tx] }

private def gFA2TransferDescriptorParam :
    G ConCert.Examples.FA2.TransferDescriptorParam := do
  let transfer_descr_fa2 ← gLocalAccountAddress
  let descr ← gFA2TransferDescriptor
  let transfer_descr_operator ← gLocalAccountAddress
  return { transfer_descr_fa2 := transfer_descr_fa2,
           transfer_descr_batch := [descr],
           transfer_descr_operator := transfer_descr_operator }

private def gFA2SetHookParam :
    G ConCert.Examples.FA2.SetHookParam := do
  let hook_addr ← gLocalAccountAddress
  let hook_permissions_descriptor ← gFA2PermissionsDescriptor
  return { hook_addr, hook_permissions_descriptor }

private def gFA2ReceiverMsgUnit :
    G (ConCert.Examples.FA2.FA2ReceiverMsg Unit) := do
  let n ← chooseNatBetween 0 5 (by decide)
  match n with
  | 0 =>
      let response ← gFA2BalanceOfResponse
      return .receive_balance_of_param [response]
  | 1 =>
      let response ← gFA2TotalSupplyResponse
      return .receive_total_supply_param [response]
  | 2 =>
      let metadata ← gFA2TokenMetadata
      return .receive_metadata_callback [metadata]
  | 3 =>
      let response ← gFA2IsOperatorResponse
      return .receive_is_operator response
  | 4 =>
      let permissions ← gFA2PermissionsDescriptor
      return .receive_permissions_descriptor permissions
  | _ => return .other_msg ()

private def gFA2TransferHookUnit :
    G (ConCert.Examples.FA2.FA2TransferHook Unit) := do
  let isHook ← chooseBool
  if isHook then do
    let param ← gFA2TransferDescriptorParam
    return .transfer_hook param
  else
    return .hook_other_msg ()

private def gFA2Msg : G ConCert.Examples.FA2.Msg := do
  let n ← chooseNatBetween 0 9 (by decide)
  match n with
  | 0 =>
      let transfer ← gFA2Transfer
      return .msg_transfer [transfer]
  | 1 =>
      let param ← gFA2SetHookParam
      return .msg_set_transfer_hook param
  | 2 =>
      let param ← gFA2TransferDescriptorParam
      return .msg_receive_hook_transfer param
  | 3 =>
      let param ← gFA2BalanceOfParam
      return .msg_balance_of param
  | 4 =>
      let param ← gFA2TotalSupplyParam
      return .msg_total_supply param
  | 5 =>
      let param ← gFA2TokenMetadataParam
      return .msg_token_metadata param
  | 6 =>
      let callback ← gFA2Callback gFA2PermissionsDescriptor
      return .msg_permissions_descriptor callback
  | 7 =>
      let update ← gFA2UpdateOperator
      return .msg_update_operators [update]
  | 8 =>
      let param ← gFA2IsOperatorParam
      return .msg_is_operator param
  | _ =>
      let tokenId ← gFA2SmallTokenId
      return .msg_create_tokens tokenId

private def gFA2Setup : G ConCert.Examples.FA2.Setup := do
  let metadata ← gFA2TokenMetadata
  let policy ← gFA2PermissionsDescriptor
  let hasHook ← chooseBool
  let hook ← gLocalAccountAddress
  return { setup_total_supply := [(metadata.metadata_token_id, 0)],
           setup_tokens := FMap.add metadata.metadata_token_id metadata FMap.empty,
           initial_permission_policy := policy,
           transfer_hook_addr_ := if hasHook then some hook else none }

private def gFA2State : G ConCert.Examples.FA2.State := do
  let owner ← gLocalAccountAddress
  let holder ← gLocalAccountAddress
  let operator ← gLocalAccountAddress
  let token_id ← gFA2SmallTokenId
  let metadata : ConCert.Examples.FA2.TokenMetadata :=
    { metadata_token_id := token_id, metadata_decimals := 8 }
  let balance ← chooseNatBetween 0 1000 (by decide)
  let policy ← gFA2PermissionsDescriptor
  let ledger : ConCert.Examples.FA2.TokenLedger :=
    { fungible := false,
      balances := FMap.add holder balance FMap.empty }
  let operatorMap := FMap.add operator (.some_tokens [token_id]) FMap.empty
  return { fa2_owner := owner,
           assets := FMap.add token_id ledger FMap.empty,
           operators := FMap.add holder operatorMap FMap.empty,
           permission_policy := policy,
           tokens := FMap.add token_id metadata FMap.empty,
           transfer_hook_addr := none }

private def fa2CallbackEq {A : Type} (eq : A → A → Bool)
    (a b : ConCert.Examples.FA2.Callback A) : Bool :=
  optionEq eq a.blob b.blob && addrEq a.return_addr b.return_addr

private def fa2TransferDestinationEq
    (a b : ConCert.Examples.FA2.TransferDestination) : Bool :=
  addrEq a.to_ b.to_ &&
    a.dst_token_id == b.dst_token_id &&
    a.amount == b.amount

private def fa2TransferEq
    (a b : ConCert.Examples.FA2.Transfer) : Bool :=
  addrEq a.from_ b.from_ &&
    listEq fa2TransferDestinationEq a.txs b.txs &&
    optionEq addrEq a.sender_callback_addr b.sender_callback_addr

private def fa2BalanceOfRequestEq
    (a b : ConCert.Examples.FA2.BalanceOfRequest) : Bool :=
  addrEq a.owner b.owner && a.bal_req_token_id == b.bal_req_token_id

private def fa2BalanceOfResponseEq
    (a b : ConCert.Examples.FA2.BalanceOfResponse) : Bool :=
  fa2BalanceOfRequestEq a.request b.request && a.balance == b.balance

private def fa2TotalSupplyResponseEq
    (a b : ConCert.Examples.FA2.TotalSupplyResponse) : Bool :=
  a.supply_resp_token_id == b.supply_resp_token_id &&
    a.total_supply == b.total_supply

private def fa2TokenMetadataEq
    (a b : ConCert.Examples.FA2.TokenMetadata) : Bool :=
  a.metadata_token_id == b.metadata_token_id &&
    a.metadata_decimals == b.metadata_decimals

private def fa2BalanceOfParamEq
    (a b : ConCert.Examples.FA2.BalanceOfParam) : Bool :=
  listEq fa2BalanceOfRequestEq a.bal_requests b.bal_requests &&
    fa2CallbackEq (listEq fa2BalanceOfResponseEq) a.bal_callback b.bal_callback

private def fa2TotalSupplyParamEq
    (a b : ConCert.Examples.FA2.TotalSupplyParam) : Bool :=
  listEq (fun a b => a == b) a.supply_param_token_ids b.supply_param_token_ids &&
    fa2CallbackEq (listEq fa2TotalSupplyResponseEq)
      a.supply_param_callback b.supply_param_callback

private def fa2TokenMetadataParamEq
    (a b : ConCert.Examples.FA2.TokenMetadataParam) : Bool :=
  listEq (fun a b => a == b) a.metadata_token_ids b.metadata_token_ids &&
    fa2CallbackEq (listEq fa2TokenMetadataEq) a.metadata_callback b.metadata_callback

private def fa2OperatorTokensEq
    (a b : ConCert.Examples.FA2.OperatorTokens) : Bool :=
  match a, b with
  | .all_tokens, .all_tokens => true
  | .some_tokens a, .some_tokens b => listEq (fun a b => a == b) a b
  | _, _ => false

private def fa2OperatorParamEq
    (a b : ConCert.Examples.FA2.OperatorParam) : Bool :=
  addrEq a.op_param_owner b.op_param_owner &&
    addrEq a.op_param_operator b.op_param_operator &&
    fa2OperatorTokensEq a.op_param_tokens b.op_param_tokens

private def fa2UpdateOperatorEq
    (a b : ConCert.Examples.FA2.UpdateOperator) : Bool :=
  match a, b with
  | .add_operator a, .add_operator b => fa2OperatorParamEq a b
  | .remove_operator a, .remove_operator b => fa2OperatorParamEq a b
  | _, _ => false

private def fa2SelfTransferPolicyEq
    (a b : ConCert.Examples.FA2.SelfTransferPolicy) : Bool :=
  match a, b with
  | .self_transfer_permitted, .self_transfer_permitted => true
  | .self_transfer_denied, .self_transfer_denied => true
  | _, _ => false

private def fa2OperatorTransferPolicyEq
    (a b : ConCert.Examples.FA2.OperatorTransferPolicy) : Bool :=
  match a, b with
  | .operator_transfer_permitted, .operator_transfer_permitted => true
  | .operator_transfer_denied, .operator_transfer_denied => true
  | _, _ => false

private def fa2OwnerTransferPolicyEq
    (a b : ConCert.Examples.FA2.OwnerTransferPolicy) : Bool :=
  match a, b with
  | .owner_no_op, .owner_no_op => true
  | .optional_owner_hook, .optional_owner_hook => true
  | .required_owner_hook, .required_owner_hook => true
  | _, _ => false

private def fa2PermissionsDescriptorEq
    (a b : ConCert.Examples.FA2.PermissionsDescriptor) : Bool :=
  fa2SelfTransferPolicyEq a.descr_self b.descr_self &&
    fa2OperatorTransferPolicyEq a.descr_operator b.descr_operator &&
    fa2OwnerTransferPolicyEq a.descr_receiver b.descr_receiver &&
    fa2OwnerTransferPolicyEq a.descr_sender b.descr_sender &&
    optionEq addrEq a.descr_custom b.descr_custom

private def fa2IsOperatorResponseEq
    (a b : ConCert.Examples.FA2.IsOperatorResponse) : Bool :=
  fa2OperatorParamEq a.operator b.operator && a.is_operator == b.is_operator

private def fa2IsOperatorParamEq
    (a b : ConCert.Examples.FA2.IsOperatorParam) : Bool :=
  fa2OperatorParamEq a.is_operator_operator b.is_operator_operator &&
    fa2CallbackEq fa2IsOperatorResponseEq
      a.is_operator_callback b.is_operator_callback

private def fa2TransferDestinationDescriptorEq
    (a b : ConCert.Examples.FA2.TransferDestinationDescriptor) : Bool :=
  optionEq addrEq a.transfer_dst_descr_to_ b.transfer_dst_descr_to_ &&
    a.transfer_dst_descr_token_id == b.transfer_dst_descr_token_id &&
    a.transfer_dst_descr_amount == b.transfer_dst_descr_amount

private def fa2TransferDescriptorEq
    (a b : ConCert.Examples.FA2.TransferDescriptor) : Bool :=
  optionEq addrEq a.transfer_descr_from_ b.transfer_descr_from_ &&
    listEq fa2TransferDestinationDescriptorEq
      a.transfer_descr_txs b.transfer_descr_txs

private def fa2TransferDescriptorParamEq
    (a b : ConCert.Examples.FA2.TransferDescriptorParam) : Bool :=
  addrEq a.transfer_descr_fa2 b.transfer_descr_fa2 &&
    listEq fa2TransferDescriptorEq a.transfer_descr_batch b.transfer_descr_batch &&
    addrEq a.transfer_descr_operator b.transfer_descr_operator

private def fa2SetHookParamEq
    (a b : ConCert.Examples.FA2.SetHookParam) : Bool :=
  addrEq a.hook_addr b.hook_addr &&
    fa2PermissionsDescriptorEq
      a.hook_permissions_descriptor b.hook_permissions_descriptor

private def fa2ReceiverMsgEq
    (a b : ConCert.Examples.FA2.FA2ReceiverMsg Unit) : Bool :=
  match a, b with
  | .receive_balance_of_param a, .receive_balance_of_param b =>
      listEq fa2BalanceOfResponseEq a b
  | .receive_total_supply_param a, .receive_total_supply_param b =>
      listEq fa2TotalSupplyResponseEq a b
  | .receive_metadata_callback a, .receive_metadata_callback b =>
      listEq fa2TokenMetadataEq a b
  | .receive_is_operator a, .receive_is_operator b =>
      fa2IsOperatorResponseEq a b
  | .receive_permissions_descriptor a, .receive_permissions_descriptor b =>
      fa2PermissionsDescriptorEq a b
  | .other_msg (), .other_msg () => true
  | _, _ => false

private def fa2TransferHookEq
    (a b : ConCert.Examples.FA2.FA2TransferHook Unit) : Bool :=
  match a, b with
  | .transfer_hook a, .transfer_hook b => fa2TransferDescriptorParamEq a b
  | .hook_other_msg (), .hook_other_msg () => true
  | _, _ => false

private def fa2MsgEq
    (a b : ConCert.Examples.FA2.Msg) : Bool :=
  match a, b with
  | .msg_transfer a, .msg_transfer b => listEq fa2TransferEq a b
  | .msg_set_transfer_hook a, .msg_set_transfer_hook b => fa2SetHookParamEq a b
  | .msg_receive_hook_transfer a, .msg_receive_hook_transfer b =>
      fa2TransferDescriptorParamEq a b
  | .msg_balance_of a, .msg_balance_of b => fa2BalanceOfParamEq a b
  | .msg_total_supply a, .msg_total_supply b => fa2TotalSupplyParamEq a b
  | .msg_token_metadata a, .msg_token_metadata b => fa2TokenMetadataParamEq a b
  | .msg_permissions_descriptor a, .msg_permissions_descriptor b =>
      fa2CallbackEq fa2PermissionsDescriptorEq a b
  | .msg_update_operators a, .msg_update_operators b =>
      listEq fa2UpdateOperatorEq a b
  | .msg_is_operator a, .msg_is_operator b => fa2IsOperatorParamEq a b
  | .msg_create_tokens a, .msg_create_tokens b => a == b
  | _, _ => false

private def fa2BalanceMapEq
    (a b : FMap TestAddress Nat) : Bool :=
  listEq (fun a b => addrEq a.1 b.1 && a.2 == b.2)
    (FMap.elements a) (FMap.elements b)

private def fa2TokenLedgerEq
    (a b : ConCert.Examples.FA2.TokenLedger) : Bool :=
  a.fungible == b.fungible && fa2BalanceMapEq a.balances b.balances

private def fa2AssetsMapEq
    (a b : FMap ConCert.Examples.FA2.TokenId ConCert.Examples.FA2.TokenLedger) :
    Bool :=
  listEq
    (fun a b => a.1 == b.1 && fa2TokenLedgerEq a.2 b.2)
    (FMap.elements a) (FMap.elements b)

private def fa2OperatorInnerMapEq
    (a b : FMap TestAddress ConCert.Examples.FA2.OperatorTokens) : Bool :=
  listEq
    (fun a b => addrEq a.1 b.1 && fa2OperatorTokensEq a.2 b.2)
    (FMap.elements a) (FMap.elements b)

private def fa2OperatorsMapEq
    (a b : FMap TestAddress (FMap TestAddress ConCert.Examples.FA2.OperatorTokens)) :
    Bool :=
  listEq
    (fun a b => addrEq a.1 b.1 && fa2OperatorInnerMapEq a.2 b.2)
    (FMap.elements a) (FMap.elements b)

private def fa2MetadataMapEq
    (a b : FMap ConCert.Examples.FA2.TokenId ConCert.Examples.FA2.TokenMetadata) :
    Bool :=
  listEq
    (fun a b => a.1 == b.1 && fa2TokenMetadataEq a.2 b.2)
    (FMap.elements a) (FMap.elements b)

private def fa2StateEq
    (a b : ConCert.Examples.FA2.State) : Bool :=
  addrEq a.fa2_owner b.fa2_owner &&
    fa2AssetsMapEq a.assets b.assets &&
    fa2OperatorsMapEq a.operators b.operators &&
    fa2PermissionsDescriptorEq a.permission_policy b.permission_policy &&
    fa2MetadataMapEq a.tokens b.tokens &&
    optionEq addrEq a.transfer_hook_addr b.transfer_hook_addr

private def fa2SetupEq
    (a b : ConCert.Examples.FA2.Setup) : Bool :=
  listEq (fun a b => a.1 == b.1 && a.2 == b.2)
      a.setup_total_supply b.setup_total_supply &&
    fa2MetadataMapEq a.setup_tokens b.setup_tokens &&
    fa2PermissionsDescriptorEq
      a.initial_permission_policy b.initial_permission_policy &&
    optionEq addrEq a.transfer_hook_addr_ b.transfer_hook_addr_

private def gDexterExchangeParam :
    G ConCert.Examples.Dexter.ExchangeParam := do
  let exchange_owner ← gLocalAccountAddress
  let tokens_sold ← chooseNatBetween 0 100 (by decide)
  return { exchange_owner, tokens_sold }

private def gDexterMsg : G ConCert.Examples.Dexter.Msg := do
  let exchange ← chooseBool
  if exchange then do
    let param ← gDexterExchangeParam
    return .tokens_to_asset param
  else
    return .add_to_tokens_reserve

private def gDexterSetup : G ConCert.Examples.Dexter.Setup := do
  let token_caddr_ ← gLocalAccountAddress
  let token_pool_ ← chooseNatBetween 0 1000 (by decide)
  return { token_caddr_, token_pool_ }

private def gDexterState : G ConCert.Examples.Dexter.State := do
  let token_pool ← chooseNatBetween 0 1000 (by decide)
  let price_history ← gListOf 4 gSmallAmount
  let token_caddr ← gLocalAccountAddress
  return { token_pool, price_history, token_caddr }

private def dexterExchangeParamEq
    (a b : ConCert.Examples.Dexter.ExchangeParam) : Bool :=
  addrEq a.exchange_owner b.exchange_owner && a.tokens_sold == b.tokens_sold

private def dexterMsgEq
    (a b : ConCert.Examples.Dexter.Msg) : Bool :=
  match a, b with
  | .tokens_to_asset a, .tokens_to_asset b => dexterExchangeParamEq a b
  | .add_to_tokens_reserve, .add_to_tokens_reserve => true
  | _, _ => false

private def dexterSetupEq
    (a b : ConCert.Examples.Dexter.Setup) : Bool :=
  addrEq a.token_caddr_ b.token_caddr_ && a.token_pool_ == b.token_pool_

private def dexterStateEq
    (a b : ConCert.Examples.Dexter.State) : Bool :=
  a.token_pool == b.token_pool &&
    listEq (fun a b => a == b) a.price_history b.price_history &&
    addrEq a.token_caddr b.token_caddr

private def gExchangeBuggyExchangeParam :
    G ConCert.Examples.ExchangeBuggy.ExchangeParam := do
  let exchange_owner ← gLocalAccountAddress
  let exchange_token_id ← gFA2SmallTokenId
  let tokens_sold ← chooseNatBetween 0 100 (by decide)
  let callback_addr ← gLocalAccountAddress
  return { exchange_owner, exchange_token_id, tokens_sold, callback_addr }

private def gExchangeBuggyExchangeMsg :
    G ConCert.Examples.ExchangeBuggy.ExchangeMsg := do
  let sell ← chooseBool
  if sell then do
    let param ← gExchangeBuggyExchangeParam
    return .tokens_to_asset param
  else do
    let tokenId ← gFA2SmallTokenId
    return .add_to_tokens_reserve tokenId

private def gExchangeBuggyMsg :
    G ConCert.Examples.ExchangeBuggy.Msg := do
  let balanceResponse ← chooseBool
  if balanceResponse then do
    let response ← gFA2BalanceOfResponse
    return .receive_balance_of_param [response]
  else do
    let msg ← gExchangeBuggyExchangeMsg
    return .other_msg msg

private def gExchangeBuggySetup :
    G ConCert.Examples.ExchangeBuggy.Setup := do
  let fa2_caddr_ ← gLocalAccountAddress
  return { fa2_caddr_ }

private def gExchangeBuggyState :
    G ConCert.Examples.ExchangeBuggy.State := do
  let fa2_caddr ← gLocalAccountAddress
  let exchange ← gExchangeBuggyExchangeParam
  let includeExchange ← chooseBool
  let price_history ← gListOf 4 gSmallAmount
  return { fa2_caddr := fa2_caddr,
           ongoing_exchanges := if includeExchange then [exchange] else [],
           price_history := price_history }

private def exchangeBuggyExchangeParamEq
    (a b : ConCert.Examples.ExchangeBuggy.ExchangeParam) : Bool :=
  addrEq a.exchange_owner b.exchange_owner &&
    a.exchange_token_id == b.exchange_token_id &&
    a.tokens_sold == b.tokens_sold &&
    addrEq a.callback_addr b.callback_addr

private def exchangeBuggyExchangeMsgEq
    (a b : ConCert.Examples.ExchangeBuggy.ExchangeMsg) : Bool :=
  match a, b with
  | .tokens_to_asset a, .tokens_to_asset b =>
      exchangeBuggyExchangeParamEq a b
  | .add_to_tokens_reserve a, .add_to_tokens_reserve b => a == b
  | _, _ => false

private def exchangeBuggyMsgEq
    (a b : ConCert.Examples.ExchangeBuggy.Msg) : Bool :=
  match a, b with
  | .receive_balance_of_param a, .receive_balance_of_param b =>
      listEq fa2BalanceOfResponseEq a b
  | .receive_total_supply_param a, .receive_total_supply_param b =>
      listEq fa2TotalSupplyResponseEq a b
  | .receive_metadata_callback a, .receive_metadata_callback b =>
      listEq fa2TokenMetadataEq a b
  | .receive_is_operator a, .receive_is_operator b =>
      fa2IsOperatorResponseEq a b
  | .receive_permissions_descriptor a, .receive_permissions_descriptor b =>
      fa2PermissionsDescriptorEq a b
  | .other_msg a, .other_msg b => exchangeBuggyExchangeMsgEq a b
  | _, _ => false

private def exchangeBuggySetupEq
    (a b : ConCert.Examples.ExchangeBuggy.Setup) : Bool :=
  addrEq a.fa2_caddr_ b.fa2_caddr_

private def exchangeBuggyStateEq
    (a b : ConCert.Examples.ExchangeBuggy.State) : Bool :=
  addrEq a.fa2_caddr b.fa2_caddr &&
    listEq exchangeBuggyExchangeParamEq
      a.ongoing_exchanges b.ongoing_exchanges &&
    listEq (fun a b => a == b) a.price_history b.price_history

private def gFA2ClientMsg :
    G ConCert.Examples.FA2.TestContracts.FA2ClientMsg := do
  let n ← chooseNatBetween 0 4 (by decide)
  match n with
  | 0 =>
      let param ← gFA2IsOperatorParam
      return .Call_fa2_is_operator param
  | 1 =>
      let response ← gFA2BalanceOfResponse
      return .Call_fa2_balance_of_param [response]
  | 2 =>
      let response ← gFA2TotalSupplyResponse
      return .Call_fa2_total_supply_param [response]
  | 3 =>
      let metadata ← gFA2TokenMetadata
      return .Call_fa2_metadata_callback [metadata]
  | _ =>
      let policy ← gFA2PermissionsDescriptor
      return .Call_fa2_permissions_descriptor policy

private def gFA2ClientWrappedMsg :
    G ConCert.Examples.FA2.TestContracts.ClientMsg := do
  let response ← chooseBool
  if response then do
    let isOperator ← gFA2IsOperatorResponse
    return .receive_is_operator isOperator
  else do
    let msg ← gFA2ClientMsg
    return .other_msg msg

private def gFA2ClientState :
    G ConCert.Examples.FA2.TestContracts.ClientState := do
  let fa2_caddr ← gLocalAccountAddress
  let bit ← chooseNatBetween 0 100 (by decide)
  return { fa2_caddr, bit }

private def gFA2ClientSetup :
    G ConCert.Examples.FA2.TestContracts.ClientSetup := do
  let fa2_caddr_ ← gLocalAccountAddress
  return { fa2_caddr_ }

private def gFA2TransferHookOtherMsg :
    G ConCert.Examples.FA2.TestContracts.FA2TransferHookMsg := do
  let policy ← gFA2PermissionsDescriptor
  return .set_permission_policy policy

private def gFA2TestHookMsg :
    G ConCert.Examples.FA2.TestContracts.TransferHookMsg := do
  let hook ← chooseBool
  if hook then do
    let param ← gFA2TransferDescriptorParam
    return .transfer_hook param
  else do
    let msg ← gFA2TransferHookOtherMsg
    return .hook_other_msg msg

private def gFA2HookState :
    G ConCert.Examples.FA2.TestContracts.HookState := do
  let hook_owner ← gLocalAccountAddress
  let hook_fa2_caddr ← gLocalAccountAddress
  let hook_policy ← gFA2PermissionsDescriptor
  return { hook_owner, hook_fa2_caddr, hook_policy }

private def gFA2HookSetup :
    G ConCert.Examples.FA2.TestContracts.HookSetup := do
  let hook_fa2_caddr_ ← gLocalAccountAddress
  let hook_policy_ ← gFA2PermissionsDescriptor
  return { hook_fa2_caddr_, hook_policy_ }

private def fa2ClientMsgEq
    (a b : ConCert.Examples.FA2.TestContracts.FA2ClientMsg) : Bool :=
  match a, b with
  | .Call_fa2_is_operator a, .Call_fa2_is_operator b =>
      fa2IsOperatorParamEq a b
  | .Call_fa2_balance_of_param a, .Call_fa2_balance_of_param b =>
      listEq fa2BalanceOfResponseEq a b
  | .Call_fa2_total_supply_param a, .Call_fa2_total_supply_param b =>
      listEq fa2TotalSupplyResponseEq a b
  | .Call_fa2_metadata_callback a, .Call_fa2_metadata_callback b =>
      listEq fa2TokenMetadataEq a b
  | .Call_fa2_permissions_descriptor a, .Call_fa2_permissions_descriptor b =>
      fa2PermissionsDescriptorEq a b
  | _, _ => false

private def fa2ClientWrappedMsgEq
    (a b : ConCert.Examples.FA2.TestContracts.ClientMsg) : Bool :=
  match a, b with
  | .receive_balance_of_param a, .receive_balance_of_param b =>
      listEq fa2BalanceOfResponseEq a b
  | .receive_total_supply_param a, .receive_total_supply_param b =>
      listEq fa2TotalSupplyResponseEq a b
  | .receive_metadata_callback a, .receive_metadata_callback b =>
      listEq fa2TokenMetadataEq a b
  | .receive_is_operator a, .receive_is_operator b =>
      fa2IsOperatorResponseEq a b
  | .receive_permissions_descriptor a, .receive_permissions_descriptor b =>
      fa2PermissionsDescriptorEq a b
  | .other_msg a, .other_msg b => fa2ClientMsgEq a b
  | _, _ => false

private def fa2ClientStateEq
    (a b : ConCert.Examples.FA2.TestContracts.ClientState) : Bool :=
  addrEq a.fa2_caddr b.fa2_caddr && a.bit == b.bit

private def fa2ClientSetupEq
    (a b : ConCert.Examples.FA2.TestContracts.ClientSetup) : Bool :=
  addrEq a.fa2_caddr_ b.fa2_caddr_

private def fa2TransferHookOtherMsgEq
    (a b : ConCert.Examples.FA2.TestContracts.FA2TransferHookMsg) : Bool :=
  match a, b with
  | .set_permission_policy a, .set_permission_policy b =>
      fa2PermissionsDescriptorEq a b

private def fa2TestHookMsgEq
    (a b : ConCert.Examples.FA2.TestContracts.TransferHookMsg) : Bool :=
  match a, b with
  | .transfer_hook a, .transfer_hook b => fa2TransferDescriptorParamEq a b
  | .hook_other_msg a, .hook_other_msg b => fa2TransferHookOtherMsgEq a b
  | _, _ => false

private def fa2HookStateEq
    (a b : ConCert.Examples.FA2.TestContracts.HookState) : Bool :=
  addrEq a.hook_owner b.hook_owner &&
    addrEq a.hook_fa2_caddr b.hook_fa2_caddr &&
    fa2PermissionsDescriptorEq a.hook_policy b.hook_policy

private def fa2HookSetupEq
    (a b : ConCert.Examples.FA2.TestContracts.HookSetup) : Bool :=
  addrEq a.hook_fa2_caddr_ b.hook_fa2_caddr_ &&
    fa2PermissionsDescriptorEq a.hook_policy_ b.hook_policy_

private def gContext
    (sender contract : TestAddress) (amount balance : Amount) :
    @ContractCallContext TestBase :=
  { ctx_origin := sender,
    ctx_from := sender,
    ctx_contract_address := contract,
    ctx_contract_balance := balance,
    ctx_amount := amount }

private def baseChain : Chain :=
  { chain_height := 0, current_slot := 0, finalized_height := 0 }

private def serializationCheckers : List (String × Checker) :=
  [ ("Nat serialization round-trip",
      forAllGen gSmallNat (roundTripWith (fun a b => a == b)))
  , ("Int serialization round-trip",
      forAllGen gSmallInt (roundTripWith (fun a b => a == b)))
  , ("Bool serialization round-trip",
      forAllGen chooseBool (roundTripWith (fun a b => a == b)))
  , ("List Nat serialization round-trip",
      forAllGen gNatList (roundTripWith (fun a b => a == b)))
  , ("Local address serialization round-trip",
      forAllGen (gLocalAddress AddrSize) (roundTripWith addrEq))
  , ("Counter message serialization round-trip",
      forAllGen gCounterMsg (roundTripWith counterMsgEq))
  , ("Counter state serialization round-trip",
      forAllGen gCounterState (roundTripWith counterStateEq))
  , ("PiggyBank tag serialization round-trip",
      forAllGen gPiggyStateTag (roundTripWith piggyStateTagEq))
  , ("PiggyBank message serialization round-trip",
      forAllGen gPiggyMsg (roundTripWith piggyMsgEq))
  , ("PiggyBank state serialization round-trip",
      forAllGen gPiggyState (roundTripWith piggyStateEq))
  , ("Escrow next-step serialization round-trip",
      forAllGen gEscrowNextStep (roundTripWith escrowNextStepEq))
  , ("Escrow message serialization round-trip",
      forAllGen gEscrowMsg (roundTripWith escrowMsgEq))
  , ("Escrow setup serialization round-trip",
      forAllGen gEscrowSetup (roundTripWith escrowSetupEq))
  , ("Escrow state serialization round-trip",
      forAllGen gEscrowState (roundTripWith escrowStateEq))
  , ("StackInterpreter op serialization round-trip",
      forAllGen gStackOp (roundTripWith stackOpEq))
  , ("StackInterpreter instruction serialization round-trip",
      forAllGen gStackInstruction (roundTripWith stackInstructionEq))
  , ("StackInterpreter value serialization round-trip",
      forAllGen gStackValue (roundTripWith stackValueEq))
  , ("StackInterpreter message serialization round-trip",
      forAllGen gStackMsg (roundTripWith stackMsgEq))
  , ("EIP20 message serialization round-trip",
      forAllGen gEIP20Msg (roundTripWith eip20MsgEq))
  , ("EIP20 setup serialization round-trip",
      forAllGen gEIP20Setup (roundTripWith eip20SetupEq))
  , ("EIP20 state serialization round-trip",
      forAllGen gEIP20State (roundTripWith eip20StateEq))
  , ("iTokenBuggy message serialization round-trip",
      forAllGen gITokenMsg (roundTripWith iTokenMsgEq))
  , ("iTokenBuggy setup serialization round-trip",
      forAllGen gITokenSetup (roundTripWith iTokenSetupEq))
  , ("iTokenBuggy state serialization round-trip",
      forAllGen gITokenState (roundTripWith iTokenStateEq))
  , ("FA1.2 callback serialization round-trip",
      forAllGen gFA12Callback (roundTripWith fa12CallbackEq))
  , ("FA1.2 transfer parameter serialization round-trip",
      forAllGen gFA12TransferParam (roundTripWith fa12TransferParamEq))
  , ("FA1.2 approve parameter serialization round-trip",
      forAllGen gFA12ApproveParam (roundTripWith fa12ApproveParamEq))
  , ("FA1.2 getAllowance parameter serialization round-trip",
      forAllGen gFA12GetAllowanceParam (roundTripWith fa12GetAllowanceParamEq))
  , ("FA1.2 getBalance parameter serialization round-trip",
      forAllGen gFA12GetBalanceParam (roundTripWith fa12GetBalanceParamEq))
  , ("FA1.2 getTotalSupply parameter serialization round-trip",
      forAllGen gFA12GetTotalSupplyParam
        (roundTripWith fa12GetTotalSupplyParamEq))
  , ("FA1.2 receiver message serialization round-trip",
      forAllGen gFA12ReceiverMsgUnit (roundTripWith fa12ReceiverMsgEq))
  , ("FA1.2 message serialization round-trip",
      forAllGen gFA12Msg (roundTripWith fa12MsgEq))
  , ("FA1.2 setup serialization round-trip",
      forAllGen gFA12Setup (roundTripWith fa12SetupEq))
  , ("FA1.2 state serialization round-trip",
      forAllGen gFA12State (roundTripWith fa12StateEq))
  , ("FA2 transfer serialization round-trip",
      forAllGen gFA2Transfer (roundTripWith fa2TransferEq))
  , ("FA2 permissions descriptor serialization round-trip",
      forAllGen gFA2PermissionsDescriptor
        (roundTripWith fa2PermissionsDescriptorEq))
  , ("FA2 receiver message serialization round-trip",
      forAllGen gFA2ReceiverMsgUnit (roundTripWith fa2ReceiverMsgEq))
  , ("FA2 transfer hook message serialization round-trip",
      forAllGen gFA2TransferHookUnit (roundTripWith fa2TransferHookEq))
  , ("FA2 message serialization round-trip",
      forAllGen gFA2Msg (roundTripWith fa2MsgEq))
  , ("FA2 setup serialization round-trip",
      forAllGen gFA2Setup (roundTripWith fa2SetupEq))
  , ("FA2 state serialization round-trip",
      forAllGen gFA2State (roundTripWith fa2StateEq))
  , ("Dexter message serialization round-trip",
      forAllGen gDexterMsg (roundTripWith dexterMsgEq))
  , ("Dexter setup serialization round-trip",
      forAllGen gDexterSetup (roundTripWith dexterSetupEq))
  , ("Dexter state serialization round-trip",
      forAllGen gDexterState (roundTripWith dexterStateEq))
  , ("ExchangeBuggy message serialization round-trip",
      forAllGen gExchangeBuggyMsg (roundTripWith exchangeBuggyMsgEq))
  , ("ExchangeBuggy setup serialization round-trip",
      forAllGen gExchangeBuggySetup (roundTripWith exchangeBuggySetupEq))
  , ("ExchangeBuggy state serialization round-trip",
      forAllGen gExchangeBuggyState (roundTripWith exchangeBuggyStateEq))
  , ("FA2 client message serialization round-trip",
      forAllGen gFA2ClientWrappedMsg (roundTripWith fa2ClientWrappedMsgEq))
  , ("FA2 client state serialization round-trip",
      forAllGen gFA2ClientState (roundTripWith fa2ClientStateEq))
  , ("FA2 client setup serialization round-trip",
      forAllGen gFA2ClientSetup (roundTripWith fa2ClientSetupEq))
  , ("FA2 hook message serialization round-trip",
      forAllGen gFA2TestHookMsg (roundTripWith fa2TestHookMsgEq))
  , ("FA2 hook state serialization round-trip",
      forAllGen gFA2HookState (roundTripWith fa2HookStateEq))
  , ("FA2 hook setup serialization round-trip",
      forAllGen gFA2HookSetup (roundTripWith fa2HookSetupEq)) ]

private def isNone {A : Type} : Option A → Bool
  | none => true
  | some _ => false

private def negativeSerializationCheckers : List (String × Checker) :=
  [ ("Nat deserialization rejects negative integers",
      checker <| isNone ((deserialize
        ({ ser_value_type := .ser_int, ser_value := (-1 : Int) } : SerializedValue)) :
          Option Nat))
  , ("Int deserialization rejects bool wire values",
      checker <| isNone ((deserialize
        ({ ser_value_type := .ser_bool, ser_value := true } : SerializedValue)) :
          Option Int))
  , ("Ascii deserialization rejects codepoints outside byte range",
      checker <| isNone ((deserialize (serialize (256 : Nat)) :
        Option ConCert.Execution.SerializableInstances.Ascii)))
  , ("String deserialization rejects invalid Unicode scalar values",
      checker <| isNone ((deserialize (serialize ([1114112] : List Nat)) :
        Option String)))
  , ("Constructor deserialization rejects wrong generated tags",
      forAllGen (chooseNatBetween 1 20 (by decide)) (fun tag =>
        isNone ((deserialize_constructor1 0 (serialize_constructor1 tag (7 : Int))) :
          Option Int)))
  , ("Constructor deserialization rejects wrong generated arity",
      checker <| isNone
        ((deserialize_constructor2 0 (serialize_constructor1 0 (7 : Int))) :
          Option (Int × Int))) ]

private def localChainCheckers : List (String × Checker) :=
  [ ("generated transfer block has a valid header",
      forAllGen (gFundedTransferBlock (lc_initial AddrSize)) (fun block =>
        validate_header AddrSize block.1 (lc_to_env AddrSize (lc_initial AddrSize)).toChain))
  , ("invalid-height header is rejected",
      forAllGen gLocalAccountAddress (fun creator =>
        !(validate_header AddrSize
          (invalidHeightHeader (lc_initial AddrSize) creator)
          (lc_to_env AddrSize (lc_initial AddrSize)).toChain)))
  , ("origin/from mismatch is detected",
      checker <|
        match find_origin_neq_from AddrSize [originMismatchTransferAction] with
        | some _ => true
        | none => false)
  , ("contract-origin root action is detected",
      checker <|
        match find_invalid_root_action AddrSize [invalidRootTransferAction] with
        | some _ => true
        | none => false)
  , ("generated funded transfer blocks execute",
      forAllGen (gFundedTransferBlock (lc_initial AddrSize)) (fun block =>
        match add_block_exec AddrSize DepthFirst (lc_initial AddrSize) block.1 block.2 with
        | .Ok lc' => lc'.lc_height == block.1.block_height && lc'.lc_slot == block.1.block_slot
        | .Err _ => false))
  , ("origin/from mismatch block fails with the expected error",
      checker <|
        let header := nextBlockHeader (lc_initial AddrSize) fixedUser10 0
        match add_block_exec AddrSize DepthFirst (lc_initial AddrSize) header
            [originMismatchTransferAction] with
        | .Err (.origin_from_mismatch _) => true
        | _ => false)
  , ("invalid root action block fails with the expected error",
      checker <|
        let header := nextBlockHeader (lc_initial AddrSize) fixedUser10 0
        match add_block_exec AddrSize DepthFirst (lc_initial AddrSize) header
            [invalidRootTransferAction] with
        | .Err (.invalid_root_action _) => true
        | _ => false)
  , ("generated local chains advance by the requested number of blocks",
      ConCert.Execution.Test.TestNotation.forAllGeneratedLocalChains 5
        (fun lc => lc.lc_height == 5 && lc.lc_slot == 5 && lc.lc_fin_height == 0))
  , ("generated local-chain builders expose concrete trace blocks",
      ConCert.Execution.Test.TestNotation.forAllGeneratedLocalChainBuilders 5
        (fun cb => (ConCert.Execution.Test.TraceGens.trace_blocks cb.lcb_trace).length == 5)) ]

private def counterBehaviorChecker : Checker := do
  let st ← gCounterState
  let msg ← gCounterMsg
  checker <|
    match ConCert.Examples.Counter.counter st msg with
    | .Ok st' =>
        match msg with
        | .Inc n => 0 < n && st'.count == st.count + n && addrEq st'.owner st.owner
        | .Dec n => 0 < n && st'.count == st.count - n && addrEq st'.owner st.owner
    | .Err _ =>
        match msg with
        | .Inc n => !(0 < n)
        | .Dec n => !(0 < n)

private def piggyInsertChecker : Checker := do
  let owner ← gLocalAccountAddress
  let amountNat ← chooseNatBetween 0 100 (by decide)
  let oldBalance ← chooseAmountBetween 0 100 (by decide)
  let st : ConCert.Examples.PiggyBank.State :=
    { balance := oldBalance, owner, piggyState := .Intact }
  let ctx := gContext owner fixedContractBase (amountNat : Int) oldBalance
  checker <|
    match ConCert.Examples.PiggyBank.insert st ctx with
    | .Ok (st', acts) =>
        st'.balance == oldBalance + (amountNat : Int) &&
          addrEq st'.owner owner &&
          piggyStateTagEq st'.piggyState .Intact &&
          acts.isEmpty
    | .Err _ => false

private def piggySmashChecker : Checker := do
  let owner ← gLocalAccountAddress
  let balance ← chooseAmountBetween 0 100 (by decide)
  let amountNat ← chooseNatBetween 0 20 (by decide)
  let st : ConCert.Examples.PiggyBank.State :=
    { balance, owner, piggyState := .Intact }
  let ctx := gContext owner fixedContractBase (amountNat : Int) balance
  checker <|
    match ConCert.Examples.PiggyBank.smash st ctx with
    | .Ok (st', acts) =>
        st'.balance == 0 &&
          piggyStateTagEq st'.piggyState .Smashed &&
          match acts with
          | [.act_transfer to_ amount] =>
              addrEq to_ owner && amount == balance + (amountNat : Int)
          | _ => false
    | .Err _ => false

private def escrowValidInitChecker : Checker := do
  let seller ← gLocalAccountAddress
  let buyer ← gLocalAccountAddress
  let itemPrice ← chooseNatBetween 1 50 (by decide)
  let amount : Amount := (itemPrice * 2 : Nat)
  let ctx := gContext seller fixedContractBase amount amount
  checker <|
    if addrEq buyer seller then
      ConCert.Execution.ResultMonad.isErr
        (ConCert.Examples.Escrow.init baseChain ctx { setup_buyer := buyer })
    else
      match ConCert.Examples.Escrow.init baseChain ctx { setup_buyer := buyer } with
      | .Ok st =>
          escrowNextStepEq st.next_step .buyer_commit &&
            addrEq st.seller seller &&
            addrEq st.buyer buyer &&
            st.seller_withdrawable == 0 &&
            st.buyer_withdrawable == 0
      | .Err _ => false

private def emptyStackMap : ConCert.Examples.StackInterpreter.ExtMap :=
  FMap.empty

private def stackStorageResultEq
    (r : ConCert.Execution.ResultMonad.Result
      ConCert.Examples.StackInterpreter.Storage
      ConCert.Examples.StackInterpreter.Error)
    (expected : ConCert.Examples.StackInterpreter.Storage) : Bool :=
  match r with
  | .Ok actual => decide (actual = expected)
  | .Err _ => false

private def stackInterpreterBehaviorChecker : Checker :=
  checker <|
    let key : ConCert.Examples.StackInterpreter.MapKey := ("x", 0)
    let ext : ConCert.Examples.StackInterpreter.ExtMap :=
      FMap.add key (.ZVal 9) emptyStackMap
    let branchProgram :=
      [ ConCert.Examples.StackInterpreter.Instruction.IPushB false
      , ConCert.Examples.StackInterpreter.Instruction.IIf
      , ConCert.Examples.StackInterpreter.Instruction.IObs ("missing", 0)
      , ConCert.Examples.StackInterpreter.Instruction.IElse
      , ConCert.Examples.StackInterpreter.Instruction.IPushZ 7
      , ConCert.Examples.StackInterpreter.Instruction.IEndIf ]
    stackStorageResultEq
      (ConCert.Examples.StackInterpreter.interp emptyStackMap
        [ .IPushZ 2, .IPushZ 3, .IOp .Add ] [] 0)
      [ConCert.Examples.StackInterpreter.Value.ZVal 5] &&
    stackStorageResultEq
      (ConCert.Examples.StackInterpreter.interp ext [ .IObs key ] [] 0)
      [ConCert.Examples.StackInterpreter.Value.ZVal 9] &&
    stackStorageResultEq
      (ConCert.Examples.StackInterpreter.interp emptyStackMap branchProgram [] 0)
      [ConCert.Examples.StackInterpreter.Value.ZVal 7] &&
    ConCert.Execution.ResultMonad.isErr
      (ConCert.Examples.StackInterpreter.receive baseChain
        (gContext fixedUser10 fixedContractBase 0 0)
        ([] : ConCert.Examples.StackInterpreter.Storage) none)

private def crowdfundingBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let donor := fixedUser11
    let cfAddr := fixedLocalAddress 17 (by decide)
    let chainBefore : Chain :=
      { chain_height := 0, current_slot := 5, finalized_height := 0 }
    let chainAfter : Chain :=
      { chain_height := 0, current_slot := 11, finalized_height := 0 }
    let ctx (sender : TestAddress) (amount : Amount) :
        @ContractCallContext TestBase :=
      { ctx_origin := sender,
        ctx_from := sender,
        ctx_contract_address := cfAddr,
        ctx_contract_balance := amount,
        ctx_amount := amount }
    let setup : ConCert.Examples.Crowdfunding.Setup :=
      { deadline := 10, goal := 25 }
    match ConCert.Examples.Crowdfunding.init chainBefore (ctx owner 0) setup with
    | .Err _ => false
    | .Ok st0 =>
        let donateNew :=
          match ConCert.Examples.Crowdfunding.receive chainBefore (ctx donor 7) st0
              (some .Donate) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
                st1.balance == 7 &&
                ConCert.Examples.Crowdfunding.donation_of donor st1 == 7
          | .Err _ => false
        let donateExisting :=
          match ConCert.Examples.Crowdfunding.receive chainBefore (ctx donor 7) st0
              (some .Donate) with
          | .Ok (st1, _) =>
              match ConCert.Examples.Crowdfunding.receive chainBefore
                  (ctx donor 5) st1 (some .Donate) with
              | .Ok (st2, acts) =>
                  acts.isEmpty &&
                    st2.balance == 12 &&
                    ConCert.Examples.Crowdfunding.donation_of donor st2 == 12
              | .Err _ => false
          | .Err _ => false
        let getFunds :=
          let funded : @ConCert.Examples.Crowdfunding.State TestBase :=
            { balance := 30,
              donations := FMap.add donor 30 FMap.empty,
              owner := st0.owner,
              deadline := st0.deadline,
              done := st0.done,
              goal := st0.goal }
          match ConCert.Examples.Crowdfunding.receive chainAfter (ctx owner 0)
              funded (some .GetFunds) with
          | .Ok (stDone, [.act_transfer to_ amount]) =>
              addrEq to_ owner && amount == 30 &&
                stDone.balance == 0 && stDone.done
          | _ => false
        let claim :=
          let failed : @ConCert.Examples.Crowdfunding.State TestBase :=
            { balance := 7,
              donations := FMap.add donor 7 FMap.empty,
              owner := st0.owner,
              deadline := st0.deadline,
              done := st0.done,
              goal := st0.goal }
          match ConCert.Examples.Crowdfunding.receive chainAfter (ctx donor 0)
              failed (some .Claim) with
          | .Ok (stClaimed, [.act_transfer to_ amount]) =>
              addrEq to_ donor && amount == 7 &&
                stClaimed.balance == 0 &&
                ConCert.Examples.Crowdfunding.donation_of donor stClaimed == 0
          | _ => false
        donateNew && donateExisting && getFunds && claim

private def eip20Balance
    (addr : TestAddress) (state : ConCert.Examples.EIP20.EIP20Token.State) : Nat :=
  (FMap.find addr state.balances).getD 0

private def eip20BehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let recipient := fixedUser11
    let delegate := fixedUser11
    let other : TestAddress := fixedLocalAddress 12 (by decide)
    let setup : ConCert.Examples.EIP20.EIP20Token.Setup :=
      { owner, init_amount := 100 }
    let ctxOwner := gContext owner fixedContractBase 0 0
    let ctxDelegate := gContext delegate fixedContractBase 0 0
    let ctxPayable := gContext owner fixedContractBase 1 0
    match ConCert.Examples.EIP20.EIP20Token.init baseChain ctxOwner setup with
    | .Err _ => false
    | .Ok st0 =>
        let transferOk :=
          match ConCert.Examples.EIP20.EIP20Token.receive baseChain ctxOwner st0
              (some (.transfer recipient 40)) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
              st1.total_supply == st0.total_supply &&
              eip20Balance owner st1 == 60 &&
              eip20Balance recipient st1 == 40
          | .Err _ => false
        let transferFromOk :=
          match ConCert.Examples.EIP20.EIP20Token.receive baseChain ctxOwner st0
              (some (.approve delegate 30)) with
          | .Err _ => false
          | .Ok (stApproved, acts1) =>
              acts1.isEmpty &&
              ConCert.Examples.EIP20.EIP20Token.get_allowance stApproved owner delegate == 30 &&
              match ConCert.Examples.EIP20.EIP20Token.receive baseChain ctxDelegate stApproved
                  (some (.transfer_from owner other 20)) with
              | .Ok (st2, acts2) =>
                  acts2.isEmpty &&
                  st2.total_supply == stApproved.total_supply &&
                  eip20Balance owner st2 == 80 &&
                  eip20Balance other st2 == 20 &&
                  ConCert.Examples.EIP20.EIP20Token.get_allowance st2 owner delegate == 10
              | .Err _ => false
        let rejectsPayable :=
          ConCert.Execution.ResultMonad.isErr
            (ConCert.Examples.EIP20.EIP20Token.receive baseChain ctxPayable st0
              (some (.approve delegate 1)))
        transferOk && transferFromOk && rejectsPayable

private def dexterEIP20TransferActionEq
    (tokenAddr : TestAddress) (expected : ConCert.Examples.EIP20.EIP20Token.Msg)
    (act : @ActionBody TestBase) : Bool :=
  match act with
  | .act_call to_ amount msg =>
      addrEq to_ tokenAddr && amount == 0 &&
        match (deserialize msg : Option ConCert.Examples.EIP20.EIP20Token.Msg) with
        | some decoded => eip20MsgEq decoded expected
        | none => false
  | _ => false

private def dexterBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let other := fixedUser11
    let tokenAddr : TestAddress := fixedLocalAddress 13 (by decide)
    let dexterAddr := fixedContractBase
    let state : ConCert.Examples.Dexter.State :=
      { token_pool := 100, price_history := [], token_caddr := tokenAddr }
    let param : ConCert.Examples.Dexter.ExchangeParam :=
      { exchange_owner := owner, tokens_sold := 10 }
    let ctxOwner := gContext owner dexterAddr 0 1000
    let ctxOther := gContext other dexterAddr 0 1000
    let expectedPrice :=
      ConCert.Examples.Dexter.getInputPrice (10 : Amount) (100 : Amount) (1000 : Amount)
    let exchangeOk :=
      match ConCert.Examples.Dexter.receive baseChain ctxOwner state
          (some (.tokens_to_asset param)) with
      | .Ok (st', acts) =>
          st'.token_pool == 110 &&
          listEq (fun a b => a == b) st'.price_history [expectedPrice] &&
          match acts with
          | [.act_transfer to_ amount, tokenAct] =>
              addrEq to_ owner &&
                amount == expectedPrice &&
                dexterEIP20TransferActionEq tokenAddr
                  (.transfer_from owner dexterAddr 10) tokenAct
          | _ => false
      | .Err _ => false
    let rejectsWrongCaller :=
      ConCert.Execution.ResultMonad.isErr
        (ConCert.Examples.Dexter.receive baseChain ctxOther state
          (some (.tokens_to_asset param)))
    let ignoresOtherMessages :=
      match ConCert.Examples.Dexter.receive baseChain ctxOwner state
          (some .add_to_tokens_reserve) with
      | .Ok (st', acts) => dexterStateEq st' state && acts.isEmpty
      | .Err _ => false
    exchangeOk && rejectsWrongCaller && ignoresOtherMessages

private def exchangeBuggyFA2ActionEq
    (fa2Addr : TestAddress) (amountExpected : Amount)
    (expected : ConCert.Examples.FA2.Msg)
    (act : @ActionBody TestBase) : Bool :=
  match act with
  | .act_call to_ amount msg =>
      addrEq to_ fa2Addr && amount == amountExpected &&
        match (deserialize msg : Option ConCert.Examples.FA2.Msg) with
        | some decoded => fa2MsgEq decoded expected
        | none => false
  | _ => false

private def exchangeBuggyBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let exchangeAddr := fixedContractBase
    let fa2Addr : TestAddress := fixedLocalAddress 13 (by decide)
    let callback : TestAddress := fixedLocalAddress 14 (by decide)
    let tokenId : ConCert.Examples.FA2.TokenId := 0
    let param : ConCert.Examples.ExchangeBuggy.ExchangeParam :=
      { exchange_owner := owner,
        exchange_token_id := tokenId,
        tokens_sold := 10,
        callback_addr := callback }
    let state0 : ConCert.Examples.ExchangeBuggy.State :=
      { fa2_caddr := fa2Addr, ongoing_exchanges := [], price_history := [] }
    let ctx0 := gContext owner exchangeAddr 0 1000
    let beginOk :=
      match ConCert.Examples.ExchangeBuggy.receive baseChain ctx0 state0
          (some (.other_msg (.tokens_to_asset param))) with
      | .Ok (st', [act]) =>
          exchangeBuggyStateEq st'
            { state0 with ongoing_exchanges := [param] } &&
          let ownerReq : ConCert.Examples.FA2.BalanceOfRequest :=
            { owner := owner, bal_req_token_id := tokenId }
          let exchangeReq : ConCert.Examples.FA2.BalanceOfRequest :=
            { owner := exchangeAddr, bal_req_token_id := tokenId }
          let expectedParam : ConCert.Examples.FA2.BalanceOfParam :=
            { bal_requests := [ownerReq, exchangeReq],
              bal_callback := { blob := none, return_addr := exchangeAddr } }
          exchangeBuggyFA2ActionEq fa2Addr 0
            (.msg_balance_of expectedParam) act
      | _ => false
    let responseOk :=
      let ownerReq : ConCert.Examples.FA2.BalanceOfRequest :=
        { owner := owner, bal_req_token_id := tokenId }
      let exchangeReq : ConCert.Examples.FA2.BalanceOfRequest :=
        { owner := exchangeAddr, bal_req_token_id := tokenId }
      let responses : List ConCert.Examples.FA2.BalanceOfResponse :=
        [ { request := ownerReq, balance := 20 },
          { request := exchangeReq, balance := 100 } ]
      let stPending : ConCert.Examples.ExchangeBuggy.State :=
        { state0 with ongoing_exchanges := [param] }
      let expectedPrice :=
        ConCert.Examples.ExchangeBuggy.getInputPrice
          (10 : Amount) (100 : Amount) (1000 : Amount)
      match ConCert.Examples.ExchangeBuggy.receive baseChain ctx0 stPending
          (some (.receive_balance_of_param responses)) with
      | .Ok (st', acts) =>
          exchangeBuggyStateEq st'
            { state0 with ongoing_exchanges := [], price_history := [expectedPrice] } &&
          match acts with
          | [.act_transfer to_ amount, tokenAct] =>
              addrEq to_ owner && amount == expectedPrice &&
                let expectedTransfer : ConCert.Examples.FA2.Transfer :=
                  { from_ := owner,
                    txs := [{ to_ := exchangeAddr,
                              dst_token_id := tokenId,
                              amount := 10 }],
                    sender_callback_addr := some callback }
                exchangeBuggyFA2ActionEq fa2Addr 0
                  (.msg_transfer [expectedTransfer]) tokenAct
          | _ => false
      | .Err _ => false
    let insufficientBalanceRejects :=
      let ownerReq : ConCert.Examples.FA2.BalanceOfRequest :=
        { owner := owner, bal_req_token_id := tokenId }
      let exchangeReq : ConCert.Examples.FA2.BalanceOfRequest :=
        { owner := exchangeAddr, bal_req_token_id := tokenId }
      let responses : List ConCert.Examples.FA2.BalanceOfResponse :=
        [ { request := ownerReq, balance := 1 },
          { request := exchangeReq, balance := 100 } ]
      let stPending : ConCert.Examples.ExchangeBuggy.State :=
        { state0 with ongoing_exchanges := [param] }
      ConCert.Execution.ResultMonad.isErr
        (ConCert.Examples.ExchangeBuggy.receive baseChain ctx0 stPending
          (some (.receive_balance_of_param responses)))
    let createReserveOk :=
      let ctxPay := gContext owner exchangeAddr 7 1000
      match ConCert.Examples.ExchangeBuggy.receive baseChain ctxPay state0
          (some (.other_msg (.add_to_tokens_reserve tokenId))) with
      | .Ok (st', [act]) =>
          exchangeBuggyStateEq st' state0 &&
            exchangeBuggyFA2ActionEq fa2Addr 7 (.msg_create_tokens tokenId) act
      | _ => false
    beginOk && responseOk && insufficientBalanceRejects && createReserveOk

private def iTokenBalance
    (addr : TestAddress) (state : ConCert.Examples.ITokenBuggy.State) : Nat :=
  (FMap.find addr state.balances).getD 0

private def iTokenBugExposedChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let delegate := fixedUser11
    let allowanceMap := FMap.add delegate 0 FMap.empty
    let st : ConCert.Examples.ITokenBuggy.State :=
      { total_supply := 10,
        balances := FMap.add owner 10 FMap.empty,
        allowances := FMap.add owner allowanceMap FMap.empty }
    match ConCert.Examples.ITokenBuggy.try_transfer_from_buggy
        delegate owner owner 1 st with
    | .Ok st' =>
        iTokenBalance owner st' == 11 &&
        st'.total_supply == 10 &&
        ((FMap.elements st'.balances).map (fun p : TestAddress × Nat => p.2)).sum !=
          st'.total_supply
    | .Err _ => false

private def fa12CallbackActionEq
    (callback : TestAddress)
    (expected : ConCert.Examples.FA1_2.FA12ReceiverMsg Unit)
    (act : @ActionBody TestBase) : Bool :=
  match act with
  | .act_call to_ amount msg =>
      addrEq to_ callback && amount == 0 &&
        match (deserialize msg :
            Option (ConCert.Examples.FA1_2.FA12ReceiverMsg Unit)) with
        | some decoded => fa12ReceiverMsgEq decoded expected
        | none => false
  | _ => false

private def fa12BehaviorChecker : Checker :=
  checker <|
    let provider := fixedUser10
    let recipient := fixedUser11
    let delegate := fixedUser11
    let other : TestAddress := fixedLocalAddress 12 (by decide)
    let callback : TestAddress := fixedLocalAddress 13 (by decide)
    let setup : ConCert.Examples.FA1_2.Setup :=
      { lqt_provider := provider, initial_pool := 100 }
    let ctxProvider := gContext provider fixedContractBase 0 0
    let ctxDelegate := gContext delegate fixedContractBase 0 0
    let ctxPayable := gContext provider fixedContractBase 1 0
    match ConCert.Examples.FA1_2.init baseChain ctxProvider setup with
    | .Err _ => false
    | .Ok st0 =>
        let initOk :=
          ConCert.Examples.FA1_2.get_balance provider st0 == 100 &&
            st0.total_supply == 100 &&
            ConCert.Examples.FA1_2.sum_balances st0 == 100 &&
            ConCert.Execution.ResultMonad.isErr
              (ConCert.Examples.FA1_2.init baseChain ctxPayable setup)
        let transferOk :=
          let param : ConCert.Examples.FA1_2.TransferParam :=
            { from_ := provider, to_ := recipient, value := 40 }
          match ConCert.Examples.FA1_2.receive baseChain ctxProvider st0
              (some (.transfer param)) with
          | .Ok (st1, acts) =>
              acts.isEmpty &&
              st1.total_supply == st0.total_supply &&
              ConCert.Examples.FA1_2.get_balance provider st1 == 60 &&
              ConCert.Examples.FA1_2.get_balance recipient st1 == 40
          | .Err _ => false
        let transferFromOk :=
          let approveParam : ConCert.Examples.FA1_2.ApproveParam :=
            { spender := delegate, value_ := 30 }
          match ConCert.Examples.FA1_2.receive baseChain ctxProvider st0
              (some (.approve approveParam)) with
          | .Err _ => false
          | .Ok (stApproved, acts1) =>
              let transferParam : ConCert.Examples.FA1_2.TransferParam :=
                { from_ := provider, to_ := other, value := 20 }
              acts1.isEmpty &&
              ConCert.Examples.FA1_2.get_allowance provider delegate stApproved == 30 &&
              ConCert.Execution.ResultMonad.isErr
                (ConCert.Examples.FA1_2.receive baseChain ctxProvider stApproved
                  (some (.approve { spender := delegate, value_ := 5 }))) &&
              match ConCert.Examples.FA1_2.receive baseChain ctxDelegate stApproved
                  (some (.transfer transferParam)) with
              | .Ok (st2, acts2) =>
                  acts2.isEmpty &&
                  st2.total_supply == stApproved.total_supply &&
                  ConCert.Examples.FA1_2.get_balance provider st2 == 80 &&
                  ConCert.Examples.FA1_2.get_balance other st2 == 20 &&
                  ConCert.Examples.FA1_2.get_allowance provider delegate st2 == 10
              | .Err _ => false
        let callbacksOk :=
          let allowanceParam : ConCert.Examples.FA1_2.GetAllowanceParam :=
            { request := (provider, delegate),
              allowance_callback := { return_addr := callback } }
          let balanceParam : ConCert.Examples.FA1_2.GetBalanceParam :=
            { owner_ := provider,
              balance_callback := { return_addr := callback } }
          let supplyParam : ConCert.Examples.FA1_2.GetTotalSupplyParam :=
            { request_ := (), supply_callback := { return_addr := callback } }
          let allowanceOk :=
            match ConCert.Examples.FA1_2.receive baseChain ctxProvider st0
                (some (.getAllowance allowanceParam)) with
            | .Ok (st', [act]) =>
                fa12StateEq st' st0 &&
                  fa12CallbackActionEq callback (.receive_allowance 0) act
            | _ => false
          let balanceOk :=
            match ConCert.Examples.FA1_2.receive baseChain ctxProvider st0
                (some (.getBalance balanceParam)) with
            | .Ok (st', [act]) =>
                fa12StateEq st' st0 &&
                  fa12CallbackActionEq callback (.receive_balance_of 100) act
            | _ => false
          let supplyOk :=
            match ConCert.Examples.FA1_2.receive baseChain ctxProvider st0
                (some (.getTotalSupply supplyParam)) with
            | .Ok (st', [act]) =>
                fa12StateEq st' st0 &&
                  fa12CallbackActionEq callback (.receive_total_supply 100) act
            | _ => false
          allowanceOk && balanceOk && supplyOk
        initOk && transferOk && transferFromOk && callbacksOk

private def fa2PolicyAll : ConCert.Examples.FA2.PermissionsDescriptor :=
  { descr_self := .self_transfer_permitted,
    descr_operator := .operator_transfer_permitted,
    descr_receiver := .owner_no_op,
    descr_sender := .owner_no_op,
    descr_custom := none }

private def fa2CallbackActionEq
    (callback : TestAddress)
    (expected : ConCert.Examples.FA2.FA2ReceiverMsg Unit)
    (act : @ActionBody TestBase) : Bool :=
  match act with
  | .act_call to_ amount msg =>
      addrEq to_ callback && amount == 0 &&
        match (deserialize msg :
            Option (ConCert.Examples.FA2.FA2ReceiverMsg Unit)) with
        | some decoded => fa2ReceiverMsgEq decoded expected
        | none => false
  | _ => false

private def fa2BehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let holder := fixedUser10
    let recipient := fixedUser11
    let operator := fixedUser11
    let other : TestAddress := fixedLocalAddress 12 (by decide)
    let callback : TestAddress := fixedLocalAddress 13 (by decide)
    let tokenId : ConCert.Examples.FA2.TokenId := 0
    let metadata : ConCert.Examples.FA2.TokenMetadata :=
      { metadata_token_id := tokenId, metadata_decimals := 8 }
    let setup : ConCert.Examples.FA2.Setup :=
      { setup_total_supply := [],
        setup_tokens := FMap.add tokenId metadata FMap.empty,
        initial_permission_policy := fa2PolicyAll,
        transfer_hook_addr_ := none }
    let ctxOwner0 := gContext owner fixedContractBase 0 0
    let ctxHolderCreate := gContext holder fixedContractBase 2 0
    let ctxHolder0 := gContext holder fixedContractBase 0 0
    let ctxOperator0 := gContext operator fixedContractBase 0 0
    let ctxPayingNonCreate := gContext holder fixedContractBase 1 0
    match ConCert.Examples.FA2.init baseChain ctxOwner0 setup with
    | .Err _ => false
    | .Ok st0 =>
        let initOk :=
          addrEq st0.fa2_owner owner &&
            ConCert.Examples.FA2.address_balance tokenId holder st0 == 0 &&
            ConCert.Examples.FA2.token_id_balance tokenId st0 == 0
        let createOk :=
          match ConCert.Examples.FA2.receive baseChain ctxHolderCreate st0
              (some (.msg_create_tokens tokenId)) with
          | .Ok (stMinted, acts) =>
              acts.isEmpty &&
              ConCert.Examples.FA2.address_balance tokenId holder stMinted == 200 &&
              ConCert.Examples.FA2.token_id_balance tokenId stMinted == 200
          | .Err _ => false
        let transferOk :=
          match ConCert.Examples.FA2.receive baseChain ctxHolderCreate st0
              (some (.msg_create_tokens tokenId)) with
          | .Err _ => false
          | .Ok (stMinted, _) =>
              let transfer : ConCert.Examples.FA2.Transfer :=
                { from_ := holder,
                  txs := [{ to_ := recipient, dst_token_id := tokenId, amount := 50 }],
                  sender_callback_addr := none }
              match ConCert.Examples.FA2.receive baseChain ctxHolder0 stMinted
                  (some (.msg_transfer [transfer])) with
              | .Ok (stTransferred, acts) =>
                  acts.isEmpty &&
                  ConCert.Examples.FA2.address_balance tokenId holder stTransferred == 150 &&
                  ConCert.Examples.FA2.address_balance tokenId recipient stTransferred == 50 &&
                  ConCert.Examples.FA2.token_id_balance tokenId stTransferred == 200
              | .Err _ => false
        let operatorOk :=
          match ConCert.Examples.FA2.receive baseChain ctxHolderCreate st0
              (some (.msg_create_tokens tokenId)) with
          | .Err _ => false
          | .Ok (stMinted, _) =>
              let opParam : ConCert.Examples.FA2.OperatorParam :=
                { op_param_owner := holder,
                  op_param_operator := operator,
                  op_param_tokens := .all_tokens }
              match ConCert.Examples.FA2.receive baseChain ctxHolder0 stMinted
                  (some (.msg_update_operators [.add_operator opParam])) with
              | .Err _ => false
              | .Ok (stOp, acts1) =>
                  let transfer : ConCert.Examples.FA2.Transfer :=
                    { from_ := holder,
                      txs := [{ to_ := other, dst_token_id := tokenId, amount := 30 }],
                      sender_callback_addr := none }
                  acts1.isEmpty &&
                  match ConCert.Examples.FA2.receive baseChain ctxOperator0 stOp
                      (some (.msg_transfer [transfer])) with
                  | .Ok (stTransferred, acts2) =>
                      acts2.isEmpty &&
                      ConCert.Examples.FA2.address_balance tokenId holder stTransferred == 170 &&
                      ConCert.Examples.FA2.address_balance tokenId other stTransferred == 30
                  | .Err _ => false
        let callbacksOk :=
          match ConCert.Examples.FA2.receive baseChain ctxHolderCreate st0
              (some (.msg_create_tokens tokenId)) with
          | .Err _ => false
          | .Ok (stMinted, _) =>
              let balReq : ConCert.Examples.FA2.BalanceOfRequest :=
                { owner := holder, bal_req_token_id := tokenId }
              let balParam : ConCert.Examples.FA2.BalanceOfParam :=
                { bal_requests := [balReq],
                  bal_callback := { blob := none, return_addr := callback } }
              let metadataParam : ConCert.Examples.FA2.TokenMetadataParam :=
                { metadata_token_ids := [tokenId],
                  metadata_callback := { blob := none, return_addr := callback } }
              let balanceOk :=
                match ConCert.Examples.FA2.receive baseChain ctxHolder0 stMinted
                    (some (.msg_balance_of balParam)) with
                | .Ok (st', [act]) =>
                    fa2StateEq st' stMinted &&
                      fa2CallbackActionEq callback
                        (.receive_balance_of_param
                          [{ request := balReq, balance := 200 }]) act
                | _ => false
              let metadataOk :=
                match ConCert.Examples.FA2.receive baseChain ctxHolder0 stMinted
                    (some (.msg_token_metadata metadataParam)) with
                | .Ok (st', [act]) =>
                    fa2StateEq st' stMinted &&
                      fa2CallbackActionEq callback
                        (.receive_metadata_callback [metadata]) act
                | _ => false
              balanceOk && metadataOk
        let rejectsPayingNonCreate :=
          ConCert.Execution.ResultMonad.isErr
            (ConCert.Examples.FA2.receive baseChain ctxPayingNonCreate st0
              (some (.msg_transfer [])))
        initOk && createOk && transferOk && operatorOk && callbacksOk &&
          rejectsPayingNonCreate

private def fa2TestContractsBehaviorChecker : Checker :=
  checker <|
    let owner := fixedUser10
    let fa2Addr : TestAddress := fixedLocalAddress 13 (by decide)
    let hookAddr : TestAddress := fixedLocalAddress 14 (by decide)
    let clientState : ConCert.Examples.FA2.TestContracts.ClientState :=
      { fa2_caddr := fa2Addr, bit := 0 }
    let tokenId : ConCert.Examples.FA2.TokenId := 0
    let opParam : ConCert.Examples.FA2.OperatorParam :=
      { op_param_owner := owner,
        op_param_operator := fixedUser11,
        op_param_tokens := .all_tokens }
    let isOpParam : ConCert.Examples.FA2.IsOperatorParam :=
      { is_operator_operator := opParam,
        is_operator_callback :=
          { blob := none, return_addr := fixedLocalAddress 15 (by decide) } }
    let clientReceivesCallback :=
      match ConCert.Examples.FA2.TestContracts.client_receive baseChain
          (gContext owner hookAddr 0 0) clientState
          (some (.receive_is_operator { operator := opParam, is_operator := true })) with
      | .Ok (st', acts) => st'.bit == 42 && acts.isEmpty
      | .Err _ => false
    let clientCallsFA2 :=
      match ConCert.Examples.FA2.TestContracts.client_receive baseChain
          (gContext owner hookAddr 0 0) clientState
          (some (.other_msg (.Call_fa2_is_operator isOpParam))) with
      | .Ok (st', [act]) =>
          st'.bit == 2 &&
            exchangeBuggyFA2ActionEq fa2Addr 0 (.msg_is_operator isOpParam) act
      | _ => false
    let hookState : ConCert.Examples.FA2.TestContracts.HookState :=
      { hook_owner := owner,
        hook_fa2_caddr := fa2Addr,
        hook_policy := fa2PolicyAll }
    let descriptor : ConCert.Examples.FA2.TransferDescriptor :=
      { transfer_descr_from_ := some owner,
        transfer_descr_txs :=
          [{ transfer_dst_descr_to_ := some fixedUser11,
             transfer_dst_descr_token_id := tokenId,
             transfer_dst_descr_amount := 5 }] }
    let transferParam : ConCert.Examples.FA2.TransferDescriptorParam :=
      { transfer_descr_fa2 := fa2Addr,
        transfer_descr_batch := [descriptor],
        transfer_descr_operator := owner }
    let hookForwards :=
      match ConCert.Examples.FA2.TestContracts.hook_receive baseChain
          (gContext fa2Addr hookAddr 0 0) hookState
          (some (.transfer_hook transferParam)) with
      | .Ok (st', [act]) =>
          fa2HookStateEq st' hookState &&
            exchangeBuggyFA2ActionEq fa2Addr 0
              (.msg_receive_hook_transfer transferParam) act
      | _ => false
    let hookRejectsWrongCaller :=
      ConCert.Execution.ResultMonad.isErr
        (ConCert.Examples.FA2.TestContracts.hook_receive baseChain
          (gContext fixedUser11 hookAddr 0 0) hookState
          (some (.transfer_hook transferParam)))
    let newPolicy :=
      { fa2PolicyAll with descr_self := .self_transfer_denied }
    let hookUpdatesPolicy :=
      match ConCert.Examples.FA2.TestContracts.hook_receive baseChain
          (gContext owner hookAddr 0 0) hookState
          (some (.hook_other_msg (.set_permission_policy newPolicy))) with
      | .Ok (st', acts) =>
          acts.isEmpty && fa2PermissionsDescriptorEq st'.hook_policy newPolicy
      | .Err _ => false
    clientReceivesCallback && clientCallsFA2 && hookForwards &&
      hookRejectsWrongCaller && hookUpdatesPolicy

private def contractBehaviorCheckers : List (String × Checker) :=
  [ ("Counter executable step law", counterBehaviorChecker)
  , ("BAT original executable laws",
      ConCert.Examples.BAT.Tests.originalBehaviorChecker)
  , ("BAT fixed executable laws",
      ConCert.Examples.BAT.Tests.fixedBehaviorChecker)
  , ("BAT alternative fix executable laws",
      ConCert.Examples.BAT.Tests.altFixBehaviorChecker)
  , ("BoardroomVoting executable laws",
      ConCert.Examples.BoardroomVoting.Tests.boardroomBehaviorChecker)
  , ("BoardroomVoting local-chain example",
      ConCert.Examples.BoardroomVoting.Tests.localChainExampleChecker)
  , ("CIS1 WCCD executable laws",
      ConCert.Examples.CIS1.Tests.wccdBehaviorChecker)
  , ("PiggyBank insert executable law", piggyInsertChecker)
  , ("PiggyBank smash executable law", piggySmashChecker)
  , ("Escrow valid init executable law", escrowValidInitChecker)
  , ("Escrow generated correctness predicate",
      ConCert.Examples.Escrow.Tests.escrowGeneratedCorrectnessChecker 7)
  , ("Escrow generated next-step sequence predicate",
      ConCert.Examples.Escrow.Tests.escrowGeneratedValidStepsChecker 7)
  , ("StackInterpreter executable laws", stackInterpreterBehaviorChecker)
  , ("Crowdfunding executable laws", crowdfundingBehaviorChecker)
  , ("Congress executable laws",
      ConCert.Examples.Congress.Tests.congressBehaviorChecker)
  , ("Congress buggy finish witness",
      ConCert.Examples.Congress.Tests.buggyFinishWitnessChecker)
  , ("EIP20 executable laws", eip20BehaviorChecker)
  , ("EIP20 generated supply invariants",
      ConCert.Examples.EIP20.EIP20Token.Tests.generatedSupplyInvariantChecker 7)
  , ("EIP20 receive postconditions",
      ConCert.Examples.EIP20.EIP20Token.Tests.receivePostconditionsChecker)
  , ("EIP20 transfer postcondition",
      ConCert.Examples.EIP20.EIP20Token.Tests.transferCorrectChecker)
  , ("EIP20 self-transfer postcondition",
      ConCert.Examples.EIP20.EIP20Token.Tests.selfTransferCorrectChecker)
  , ("EIP20 transfer_from postcondition",
      ConCert.Examples.EIP20.EIP20Token.Tests.transferFromCorrectChecker)
  , ("EIP20 approve postcondition",
      ConCert.Examples.EIP20.EIP20Token.Tests.approveCorrectChecker)
  , ("Dexter executable laws", dexterBehaviorChecker)
  , ("Dexter generated pool/token-balance invariant",
      ConCert.Examples.Dexter.Tests.generatedPoolMatchesTokenBalanceChecker 5)
  , ("Dexter single-trade local-chain law",
      ConCert.Examples.Dexter.Tests.singleTradeCorrectChecker)
  , ("Dexter2 liquidity token executable laws",
      ConCert.Examples.Dexter2.Tests.lqtBehaviorChecker)
  , ("Dexter2 CPMM executable laws",
      ConCert.Examples.Dexter2.Tests.cpmmBehaviorChecker)
  , ("ExchangeBuggy executable laws", exchangeBuggyBehaviorChecker)
  , ("ExchangeBuggy reentrancy local-chain witness",
      ConCert.Examples.ExchangeBuggy.Tests.reentrancyBugWitnessChecker)
  , ("iTokenBuggy self-transfer bug is executable", iTokenBugExposedChecker)
  , ("iTokenBuggy self-transfer bug chain witness",
      ConCert.Examples.ITokenBuggy.Tests.selfTransferBugWitnessChecker)
  , ("iTokenBuggy non-self transfer_from preserves supply",
      ConCert.Examples.ITokenBuggy.Tests.nonSelfTransferFromPreservesSupplyChecker)
  , ("iTokenBuggy approve preserves supply",
      ConCert.Examples.ITokenBuggy.Tests.approvePreservesSupplyChecker)
  , ("FA1.2 executable laws", fa12BehaviorChecker)
  , ("FA2 executable laws", fa2BehaviorChecker)
  , ("FA2 generated supply invariant",
      ConCert.Examples.FA2.Tests.generatedSupplyInvariantChecker 6)
  , ("FA2 direct transfer update law",
      ConCert.Examples.FA2.Tests.directTransferUpdateChecker)
  , ("FA2 last update-operator occurrence law",
      ConCert.Examples.FA2.Tests.lastUpdateOperatorOccurrenceChecker)
  , ("FA2 test-contract executable laws", fa2TestContractsBehaviorChecker) ]

def run : IO Unit := do
  for test in serializationCheckers ++
      ConCert.Examples.Congress.Tests.serializationCheckers ++
      [("Dexter2 serialization round-trips",
        ConCert.Examples.Dexter2.Tests.serializationChecker),
       ("BAT serialization round-trips",
        ConCert.Examples.BAT.Tests.serializationChecker),
       ("BoardroomVoting serialization round-trips",
        ConCert.Examples.BoardroomVoting.Tests.serializationChecker),
       ("CIS1 WCCD serialization round-trips",
        ConCert.Examples.CIS1.Tests.serializationChecker)] ++
      negativeSerializationCheckers ++ localChainCheckers ++
      contractBehaviorCheckers do
    assertChecker test.1 cfg test.2
  assertCheckerFails "expected-failure runner"
    { cfg with numTests := 8, maxSize := 4 }
    (forAllGen gLocalAccountAddress (fun _ => false))
  assertCheckerFails "iTokenBuggy self-transfer violates supply invariant"
    cfg
    ConCert.Examples.ITokenBuggy.Tests.selfTransferSupplyInvariantChecker
  assertCheckerFails "EIP20 allowance sum can exceed supply"
    cfg
    ConCert.Examples.EIP20.EIP20Token.Tests.allowancesExceedSupplyChecker
  assertCheckerFails "EIP20 reapproval race safety is invalid"
    cfg
    ConCert.Examples.EIP20.EIP20Token.Tests.reapproveTransferFromSafetyChecker
  assertCheckerFails "ExchangeBuggy reentrancy violates price consistency"
    cfg
    ConCert.Examples.ExchangeBuggy.Tests.reentrancyPriceConsistencyChecker
  assertCheckerFails "CongressBuggy finish violates action conservation"
    cfg
    ConCert.Examples.Congress.Tests.buggyActionConservationChecker
  assertForAllShrinkFails "expected shrinking failure runner"
    { cfg with numTests := 4, maxSize := 16, seed := 99 }
    (chooseNatBetween 10 100 (by decide))
    shrinkNat
    toString
    (fun n => n < 5)

end GeneratedProperties

def localActionEvaluationDecidableSmoke :=
  letI : ConCert.Execution.Finite.Finite TestBase.Address :=
    (inferInstance :
      ConCert.Execution.Finite.Finite
        (ConCert.Execution.BoundedN ConCert.Execution.Test.TestUtils.AddrSize))
  ConCert.Execution.BlockchainBuilder.BuildUtils.action_evaluation_decidable_of_finite
    (Base := TestBase)

def main : IO Unit := do
  GeneratedProperties.run
  IO.println "ConCert generated property tests passed"
