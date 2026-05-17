/- Port of examples/dexter/DexterPrinters.v. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Examples.Dexter.Dexter
import ConCert.Examples.EIP20.EIP20TokenPrinters

namespace ConCert.Examples.Dexter.Printers

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Test.ChainPrinters
open ConCert.Examples.Dexter

variable [Base : ChainBase]

def string_of_exchange_param (showAddr : Base.Address → String)
    (t : @ExchangeParam Base) : String :=
  "exchange{exchange_owner=" ++ showAddr t.exchange_owner ++ sep ++
    "tokens_sold=" ++ toString t.tokens_sold ++ "}"

def string_of_msg (showAddr : Base.Address → String) : @Msg Base → String
  | .tokens_to_asset param =>
      "tokens_to_asset " ++ string_of_exchange_param showAddr param
  | .add_to_tokens_reserve => "add_to_tokens_reserve"

def string_of_state (showAddr : Base.Address → String) (s : @State Base) :
    String :=
  "DexterState{token_caddr=" ++ showAddr s.token_caddr ++ sep ++
    "token_pool=" ++ toString s.token_pool ++ sep ++
    "price_history=" ++ toString s.price_history ++ "}"

def string_of_setup (showAddr : Base.Address → String) (s : @Setup Base) :
    String :=
  "DexterSetup{token_caddr_=" ++ showAddr s.token_caddr_ ++ sep ++
    "token_pool_=" ++ toString s.token_pool_ ++ "}"

def string_of_serialized_msg
    (v : ConCert.Execution.SerializableBase.SerializedValue) : String :=
  string_of_serialized_value v

end ConCert.Examples.Dexter.Printers
