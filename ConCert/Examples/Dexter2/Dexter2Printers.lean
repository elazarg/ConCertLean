/- Port of examples/dexter2/Dexter2Printers.v as string renderers. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Execution.Test.TestUtils
import ConCert.Examples.Dexter2.Dexter2CPMM
import ConCert.Examples.Dexter2.Dexter2FA12
import ConCert.Examples.FA2.FA2Printers

namespace ConCert.Examples.Dexter2.Printers

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.Test.ChainPrinters
open ConCert.Execution.Test.TestUtils

namespace CPMM

open ConCert.Examples.Dexter2.CPMM

variable [Base : ChainBase]

def string_of_add_liquidity_param (showAddr : Base.Address → String)
    (p : @AddLiquidityParam Base) : String :=
  "params{owner=" ++ showAddr p.owner ++ sep ++
    "min_lqt_minted=" ++ toString p.minLqtMinted ++ sep ++
    "max_tokens_deposited=" ++ toString p.maxTokensDeposited ++ sep ++
    "deadline=" ++ toString p.add_deadline ++ "}"

def string_of_remove_liquidity_param (showAddr : Base.Address → String)
    (p : @RemoveLiquidityParam Base) : String :=
  "params{to=" ++ showAddr p.liquidity_to ++ sep ++
    "lqt_burned=" ++ toString p.lqtBurned ++ sep ++
    "min_xtz_withdrawn=" ++ toString p.minXtzWithdrawn ++ sep ++
    "min_tokens_withdrawn=" ++ toString p.minTokensWithdrawn ++ sep ++
    "deadline=" ++ toString p.remove_deadline ++ "}"

def string_of_xtz_to_token_param (showAddr : Base.Address → String)
    (p : @XtzToTokenParam Base) : String :=
  "params{to=" ++ showAddr p.tokens_to ++ sep ++
    "min_tokens_bought=" ++ toString p.minTokensBought ++ sep ++
    "deadline=" ++ toString p.xtt_deadline ++ "}"

def string_of_token_to_xtz_param (showAddr : Base.Address → String)
    (p : @TokenToXtzParam Base) : String :=
  "params{to=" ++ showAddr p.xtz_to ++ sep ++
    "tokens_sold=" ++ toString p.tokensSold ++ sep ++
    "min_xtz_bought=" ++ toString p.minXtzBought ++ sep ++
    "deadline=" ++ toString p.ttx_deadline ++ "}"

def string_of_token_to_token_param (showAddr : Base.Address → String)
    (p : @TokenToTokenParam Base) : String :=
  "params{exchange_address=" ++ showAddr p.outputDexterContract ++ sep ++
    "to=" ++ showAddr p.to_ ++ sep ++
    "min_tokens_bought=" ++ toString p.minTokensBought_ ++ sep ++
    "tokens_sold=" ++ toString p.tokensSold_ ++ sep ++
    "deadline=" ++ toString p.ttt_deadline ++ "}"

def string_of_baker (showAddr : Base.Address → String) :
    @BakerAddress Base → String
  | none => "none"
  | some addr => showAddr addr

def string_of_set_baker_param (showAddr : Base.Address → String)
    (p : @SetBakerParam Base) : String :=
  "params{baker=" ++ string_of_baker showAddr p.baker ++ sep ++
    "freeze=" ++ toString p.freezeBaker_ ++ "}"

def string_of_dexter_msg (showAddr : Base.Address → String) :
    @DexterMsg Base → String
  | .AddLiquidity param =>
      "add_liquidity " ++ string_of_add_liquidity_param showAddr param
  | .RemoveLiquidity param =>
      "remove_liquidity " ++ string_of_remove_liquidity_param showAddr param
  | .XtzToToken param =>
      "xtz_to_token " ++ string_of_xtz_to_token_param showAddr param
  | .TokenToXtz param =>
      "token_to_xtz " ++ string_of_token_to_xtz_param showAddr param
  | .SetBaker param =>
      "set_baker " ++ string_of_set_baker_param showAddr param
  | .SetManager addr => "set_manager " ++ showAddr addr
  | .SetLqtAddress addr => "set_lqt_address " ++ showAddr addr
  | .UpdateTokenPool => "update_token_pool"
  | .TokenToToken param =>
      "token_to_token " ++ string_of_token_to_token_param showAddr param

def string_of_msg (showAddr : Base.Address → String) : @Msg Base → String
  | .receive_balance_of_param _ => "receive_balance_of_param"
  | .receive_total_supply_param _ => "receive_total_supply_param"
  | .receive_metadata_callback _ => "receive_metadata_callback"
  | .receive_is_operator _ => "receive_is_operator"
  | .receive_permissions_descriptor _ => "receive_permissions_descriptor"
  | .other_msg msg => string_of_dexter_msg showAddr msg

def string_of_setup (showAddr : Base.Address → String) (p : @Setup Base) :
    String :=
  "Setup{lqt_total=" ++ toString p.lqtTotal_ ++ sep ++
    "manager=" ++ showAddr p.manager_ ++ sep ++
    "token_address=" ++ showAddr p.tokenAddress_ ++ sep ++
    "token_id=" ++ toString p.tokenId_ ++ "}"

def string_of_state (showAddr : Base.Address → String) (p : @State Base) :
    String :=
  "State{token_pool=" ++ toString p.tokenPool ++ sep ++
    "xtz_pool=" ++ toString p.xtzPool ++ sep ++
    "lqt_total=" ++ toString p.lqtTotal ++ sep ++
    "is_updating_token_pool=" ++ toString p.selfIsUpdatingTokenPool ++ sep ++
    "baker_frozen=" ++ toString p.freezeBaker ++ sep ++
    "manager=" ++ showAddr p.manager ++ sep ++
    "token_address=" ++ showAddr p.tokenAddress ++ sep ++
    "lqt_address=" ++ showAddr p.lqtAddress ++ sep ++
    "token_id=" ++ toString p.tokenId ++ "}"

end CPMM

namespace FA12

open ConCert.Examples.Dexter2.FA12

variable [Base : ChainBase]

def string_of_callback (showAddr : Base.Address → String)
    (cb : @Callback Base) : String :=
  "return_addr=" ++ showAddr cb.return_addr

def string_of_setup (showAddr : Base.Address → String) (p : @Setup Base) :
    String :=
  "Setup{admin=" ++ showAddr p.admin_ ++ sep ++
    "lqt_provider=" ++ showAddr p.lqt_provider ++ sep ++
    "initial_pool=" ++ toString p.initial_pool ++ "}"

def string_of_state (showAddr : Base.Address → String) (p : @State Base) :
    String :=
  "State{tokens=" ++ string_of_FMap showAddr toString p.tokens ++ sep ++
    "allowances=" ++
      string_of_FMap
        (fun pair => "(" ++ showAddr pair.1 ++ "," ++ showAddr pair.2 ++ ")")
        toString p.allowances ++ sep ++
    "total_supply=" ++ toString p.total_supply ++ sep ++
    "admin=" ++ showAddr p.admin ++ "}"

def string_of_transfer_param (showAddr : Base.Address → String)
    (p : @TransferParam Base) : String :=
  "params{from=" ++ showAddr p.from_ ++ sep ++
    "to=" ++ showAddr p.to_ ++ sep ++
    "value=" ++ toString p.value ++ "}"

def string_of_approve_param (showAddr : Base.Address → String)
    (p : @ApproveParam Base) : String :=
  "params{spender=" ++ showAddr p.spender ++ sep ++
    "value=" ++ toString p.value_ ++ "}"

def string_of_mint_or_burn_param (showAddr : Base.Address → String)
    (p : @MintOrBurnParam Base) : String :=
  "params{quantity=" ++ toString p.quantity ++ sep ++
    "target=" ++ showAddr p.target ++ "}"

def string_of_get_allowance_param (showAddr : Base.Address → String)
    (p : @GetAllowanceParam Base) : String :=
  "params{request=(" ++ showAddr p.request.1 ++ "," ++ showAddr p.request.2 ++
    ")" ++ sep ++
    "callback_addr=" ++ string_of_callback showAddr p.allowance_callback ++ "}"

def string_of_get_balance_param (showAddr : Base.Address → String)
    (p : @GetBalanceParam Base) : String :=
  "params{owner=" ++ showAddr p.owner_ ++ sep ++
    "callback_addr=" ++ string_of_callback showAddr p.balance_callback ++ "}"

def string_of_get_total_supply_param (showAddr : Base.Address → String)
    (p : @GetTotalSupplyParam Base) : String :=
  "params{callback_addr=" ++ string_of_callback showAddr p.supply_callback ++ "}"

def string_of_msg (showAddr : Base.Address → String) : @Msg Base → String
  | .msg_transfer param =>
      "transfer " ++ string_of_transfer_param showAddr param
  | .msg_approve param =>
      "approve " ++ string_of_approve_param showAddr param
  | .msg_mint_or_burn param =>
      "mint_or_burn " ++ string_of_mint_or_burn_param showAddr param
  | .msg_get_allowance param =>
      "get_allowance " ++ string_of_get_allowance_param showAddr param
  | .msg_get_balance param =>
      "get_balance " ++ string_of_get_balance_param showAddr param
  | .msg_get_total_supply param =>
      "get_total_supply " ++ string_of_get_total_supply_param showAddr param

end FA12

def string_of_serialized_msg
    (v : ConCert.Execution.SerializableBase.SerializedValue) : String :=
  string_of_serialized_value v

end ConCert.Examples.Dexter2.Printers
