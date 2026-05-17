/- Port of examples/dexter/Dexter.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Examples.EIP20.EIP20Token

namespace ConCert.Examples.Dexter

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

structure ExchangeParam where
  exchange_owner : Base.Address
  tokens_sold : Nat
  deriving Serializable

inductive Msg where
  | tokens_to_asset (param : @ExchangeParam Base)
  | add_to_tokens_reserve
  deriving Serializable

structure Setup where
  token_caddr_ : Base.Address
  token_pool_ : Nat
  deriving Serializable

structure State where
  token_pool : Nat
  price_history : List Amount
  token_caddr : Base.Address
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

def getInputPrice
    (tokens_to_be_sold tokens_reserve asset_reserve : Amount) : Amount :=
  (tokens_to_be_sold * 997 * asset_reserve) /
    (tokens_reserve * 1000 + tokens_to_be_sold * 997)

def begin_exchange_tokens_to_assets
    (dexter_asset_reserve : Amount) (caller : Base.Address)
    (params : @ExchangeParam Base) (dexter_caddr : Base.Address)
    (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match throwIf (!(Base.address_eqb caller params.exchange_owner)) default_error with
  | .Err e => .Err e
  | .Ok _ =>
      let tokens_to_sell : Amount := params.tokens_sold
      let tokens_price :=
        getInputPrice tokens_to_sell state.token_pool dexter_asset_reserve
      let asset_transfer_msg :=
        ActionBody.act_transfer params.exchange_owner tokens_price
      let token_transfer_param : ConCert.Examples.EIP20.EIP20Token.Msg :=
        .transfer_from params.exchange_owner dexter_caddr params.tokens_sold
      let token_transfer_msg :=
        ActionBody.act_call state.token_caddr 0 (serialize token_transfer_param)
      let new_state :=
        { state with
          token_pool := state.token_pool + params.tokens_sold,
          price_history := state.price_history ++ [tokens_price] }
      .Ok (new_state, [asset_transfer_msg, token_transfer_msg])

def receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let sender := ctx.ctx_from
  let caddr := ctx.ctx_contract_address
  let dexter_balance := ctx.ctx_contract_balance
  match maybe_msg with
  | some (.tokens_to_asset params) =>
      begin_exchange_tokens_to_assets dexter_balance sender params caddr state
  | _ =>
      .Ok (state, [])

def init (_chain : Chain) (_ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  .Ok
    { token_pool := setup.token_pool_,
      token_caddr := setup.token_caddr_,
      price_history := [] }

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

end ConCert.Examples.Dexter
