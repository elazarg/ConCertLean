/- Port of examples/exchangeBuggy/ExchangeBuggy.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Examples.FA2.FA2LegacyInterface
import ConCert.Examples.FA2.FA2Token

namespace ConCert.Examples.ExchangeBuggy

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

structure ExchangeParam where
  exchange_owner : Base.Address
  exchange_token_id : ConCert.Examples.FA2.TokenId
  tokens_sold : Nat
  callback_addr : Base.Address
  deriving Serializable

inductive ExchangeMsg where
  | tokens_to_asset (param : @ExchangeParam Base)
  | add_to_tokens_reserve (token_id : ConCert.Examples.FA2.TokenId)
  deriving Serializable

abbrev Msg : Type := ConCert.Examples.FA2.FA2ReceiverMsg ExchangeMsg

structure State where
  fa2_caddr : Base.Address
  ongoing_exchanges : List (@ExchangeParam Base)
  price_history : List Amount
  deriving Serializable

structure Setup where
  fa2_caddr_ : Base.Address
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

def begin_exchange_tokens_to_assets
    (ctx : @ContractCallContext Base) (params : @ExchangeParam Base)
    (exchange_caddr : Base.Address) (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let owner_balance_param : ConCert.Examples.FA2.BalanceOfRequest :=
    { owner := params.exchange_owner,
      bal_req_token_id := params.exchange_token_id }
  let exchange_balance_param : ConCert.Examples.FA2.BalanceOfRequest :=
    { owner := exchange_caddr,
      bal_req_token_id := params.exchange_token_id }
  let act : ConCert.Examples.FA2.BalanceOfParam :=
    { bal_requests := [owner_balance_param, exchange_balance_param],
      bal_callback := { blob := none, return_addr := ctx.ctx_contract_address } }
  let ser_msg := serialize (ConCert.Examples.FA2.Msg.msg_balance_of act)
  let acts := [ActionBody.act_call state.fa2_caddr 0 ser_msg]
  let state := { state with ongoing_exchanges := params :: state.ongoing_exchanges }
  .Ok (state, acts)

def getInputPrice
    (tokens_to_be_sold tokens_reserve asset_reserve : Amount) : Amount :=
  (tokens_to_be_sold * 997 * asset_reserve) /
    (tokens_reserve * 1000 + tokens_to_be_sold * 997)

def receive_balance_response
    (responses : List ConCert.Examples.FA2.BalanceOfResponse)
    (exchange_caddr : Base.Address)
    (exchange_asset_reserve : Amount)
    (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  if !(responses.length == 2) then
    .Err default_error
  else
    match responses[0]?, responses[1]? with
    | some trx_owner_balance_response, some exchange_balance_response =>
        if !(Base.address_eqb exchange_caddr exchange_balance_response.request.owner) then
          .Err default_error
        else
          match state.ongoing_exchanges.getLast? with
          | none => .Err default_error
          | some related_exchange =>
              if trx_owner_balance_response.balance < related_exchange.tokens_sold then
                .Err default_error
              else
                let exchange_token_reserve := exchange_balance_response.balance
                let tokens_to_sell : Amount := related_exchange.tokens_sold
                let tokens_price :=
                  getInputPrice tokens_to_sell exchange_token_reserve exchange_asset_reserve
                let asset_transfer_msg :=
                  ActionBody.act_transfer related_exchange.exchange_owner tokens_price
                let token_transfer_param : ConCert.Examples.FA2.Msg :=
                  .msg_transfer
                    [{ from_ := related_exchange.exchange_owner,
                       txs :=
                        [{ to_ := exchange_caddr,
                           dst_token_id := related_exchange.exchange_token_id,
                           amount := related_exchange.tokens_sold }],
                       sender_callback_addr := some related_exchange.callback_addr }]
                let token_transfer_msg :=
                  ActionBody.act_call state.fa2_caddr 0 (serialize token_transfer_param)
                let state :=
                  { state with
                    ongoing_exchanges := state.ongoing_exchanges.dropLast,
                    price_history := tokens_price :: state.price_history }
                .Ok (state, [asset_transfer_msg, token_transfer_msg])
    | _, _ => .Err default_error

def create_tokens
    (tokenid : ConCert.Examples.FA2.TokenId) (nr_tokens : Amount)
    (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let msg := serialize (ConCert.Examples.FA2.Msg.msg_create_tokens tokenid)
  let create_tokens_act := ActionBody.act_call state.fa2_caddr nr_tokens msg
  .Ok (state, [create_tokens_act])

def receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let caddr := ctx.ctx_contract_address
  let exchange_balance := ctx.ctx_contract_balance
  let amount := ctx.ctx_amount
  match maybe_msg with
  | some (.receive_balance_of_param responses) =>
      receive_balance_response responses caddr exchange_balance state
  | some (.other_msg (.tokens_to_asset params)) =>
      begin_exchange_tokens_to_assets ctx params caddr state
  | some (.other_msg (.add_to_tokens_reserve tokenid)) =>
      create_tokens tokenid amount state
  | _ =>
      .Err default_error

def init (_chain : Chain) (_ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  .Ok { fa2_caddr := setup.fa2_caddr_, ongoing_exchanges := [], price_history := [] }

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

end ConCert.Examples.ExchangeBuggy
