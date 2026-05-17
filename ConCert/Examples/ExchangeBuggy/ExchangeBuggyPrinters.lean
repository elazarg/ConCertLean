/- Port of examples/exchangeBuggy/ExchangeBuggyPrinters.v. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Examples.ExchangeBuggy.ExchangeBuggy
import ConCert.Examples.FA2.FA2Token

namespace ConCert.Examples.ExchangeBuggy.Printers

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Test.ChainPrinters
open ConCert.Examples.ExchangeBuggy

variable [Base : ChainBase]

def string_of_exchange_param (showAddr : Base.Address → String)
    (t : @ExchangeParam Base) : String :=
  "exchange{exchange_owner=" ++ showAddr t.exchange_owner ++ sep ++
    "exchange_token_id=" ++ toString t.exchange_token_id ++ sep ++
    "tokens_sold=" ++ toString t.tokens_sold ++ "}"

def string_of_exchange_msg (showAddr : Base.Address → String) :
    @ExchangeMsg Base → String
  | .tokens_to_asset param =>
      "tokens_to_asset " ++ string_of_exchange_param showAddr param
  | .add_to_tokens_reserve tokenid =>
      "add_to_tokens_reserve(token_id=" ++ toString tokenid ++ ")"

def string_of_msg (showAddr : Base.Address → String) : @Msg Base → String
  | .other_msg msg => string_of_exchange_msg showAddr msg
  | .receive_balance_of_param responses =>
      "receive_balance_of_param(" ++ toString responses.length ++ " responses)"
  | .receive_total_supply_param responses =>
      "receive_total_supply_param(" ++ toString responses.length ++ " responses)"
  | .receive_metadata_callback metadata =>
      "receive_metadata_callback(" ++ toString metadata.length ++ " items)"
  | .receive_is_operator _ => "receive_is_operator"
  | .receive_permissions_descriptor _ => "receive_permissions_descriptor"

def string_of_state (showAddr : Base.Address → String) (s : @State Base) :
    String :=
  "ExchangeState{fa2_caddr=" ++ showAddr s.fa2_caddr ++ sep ++
    "ongoing_exchanges=" ++ toString s.ongoing_exchanges.length ++ sep ++
    "price_history=" ++ toString s.price_history ++ "}"

def string_of_setup (showAddr : Base.Address → String) (s : @Setup Base) :
    String :=
  "ExchangeSetup{fa2_caddr_=" ++ showAddr s.fa2_caddr_ ++ "}"

def string_of_serialized_msg
    (v : ConCert.Execution.SerializableBase.SerializedValue) : String :=
  string_of_serialized_value v

end ConCert.Examples.ExchangeBuggy.Printers
