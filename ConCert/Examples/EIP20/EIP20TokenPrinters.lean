/- Port of examples/EIP20/EIP20TokenPrinters.v. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Examples.EIP20.EIP20Token

namespace ConCert.Examples.EIP20.EIP20Token.Printers

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.Test.ChainPrinters
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.EIP20.EIP20Token

variable [Base : ChainBase]

def string_of_token_value (v : TokenValue) : String :=
  toString v

def string_of_msg (showAddr : Base.Address → String) : @Msg Base → String
  | .transfer to_ amount =>
      "transfer " ++ showAddr to_ ++ " " ++ string_of_token_value amount
  | .transfer_from from_ to_ amount =>
      "transfer_from " ++ showAddr from_ ++ " " ++ showAddr to_ ++ " " ++
        string_of_token_value amount
  | .approve delegate amount =>
      "approve " ++ showAddr delegate ++ " " ++ string_of_token_value amount

def string_of_setup (showAddr : Base.Address → String) (setup : @Setup Base) :
    String :=
  "Setup{owner=" ++ showAddr setup.owner ++ sep ++
    "init_amount=" ++ string_of_token_value setup.init_amount ++ "}"

def string_of_allowances
    (showAddr : Base.Address → String)
    (m : FMap Base.Address (FMap Base.Address TokenValue)) : String :=
  string_of_FMap showAddr (string_of_FMap showAddr string_of_token_value) m

def string_of_state (showAddr : Base.Address → String) (s : @State Base) :
    String :=
  "State{total_supply=" ++ string_of_token_value s.total_supply ++ sep ++
    "balances=" ++ string_of_FMap showAddr string_of_token_value s.balances ++
    sep ++ "allowances=" ++ string_of_allowances showAddr s.allowances ++ "}"

def string_of_serialized_msg
    (v : ConCert.Execution.SerializableBase.SerializedValue) : String :=
  string_of_serialized_value v

end ConCert.Examples.EIP20.EIP20Token.Printers
