/- Port of examples/bat/BATPrinters.v as string renderers. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Examples.BAT.BAT
import ConCert.Examples.EIP20.EIP20TokenPrinters

namespace ConCert.Examples.BAT.Printers

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Test.ChainPrinters
open ConCert.Examples.BAT

variable [Base : ChainBase]

def string_of_token_value (v : TokenValue) : String := toString v

def string_of_msg (showAddr : Base.Address → String) : @Msg Base → String
  | .tokenMsg msg =>
      ConCert.Examples.EIP20.EIP20Token.Printers.string_of_msg showAddr msg
  | .create_tokens => "create_tokens"
  | .finalize => "finalize"
  | .refund => "refund"

def string_of_setup (showAddr : Base.Address → String) (setup : @Setup Base) :
    String :=
  "Setup{initSupply=" ++ string_of_token_value setup.batFund ++ sep ++
    "fundDeposit=" ++ showAddr setup.fundDeposit_ ++ sep ++
    "batFundDeposit=" ++ showAddr setup.batFundDeposit_ ++ sep ++
    "fundingStart=" ++ toString setup.fundingStart_ ++ sep ++
    "fundingEnd=" ++ toString setup.fundingEnd_ ++ sep ++
    "tokenExchangeRate=" ++ string_of_token_value setup.tokenExchangeRate_ ++ sep ++
    "tokenCreationCap=" ++ string_of_token_value setup.tokenCreationCap_ ++ sep ++
    "tokenCreationMin=" ++ string_of_token_value setup.tokenCreationMin_ ++ "}"

def string_of_state (showAddr : Base.Address → String) (s : @State Base) :
    String :=
  "State{initSupply=" ++ string_of_token_value s.initSupply ++ sep ++
    "token_state=" ++
      ConCert.Examples.EIP20.EIP20Token.Printers.string_of_state showAddr s.token_state ++
    sep ++ "isFinalized=" ++ toString s.isFinalized ++ sep ++
    "fundDeposit=" ++ showAddr s.fundDeposit ++ sep ++
    "batFundDeposit=" ++ showAddr s.batFundDeposit ++ sep ++
    "fundingStart=" ++ toString s.fundingStart ++ sep ++
    "fundingEnd=" ++ toString s.fundingEnd ++ sep ++
    "tokenExchangeRate=" ++ string_of_token_value s.tokenExchangeRate ++ sep ++
    "tokenCreationCap=" ++ string_of_token_value s.tokenCreationCap ++ sep ++
    "tokenCreationMin=" ++ string_of_token_value s.tokenCreationMin ++ "}"

def string_of_serialized_msg
    (v : ConCert.Execution.SerializableBase.SerializedValue) : String :=
  string_of_serialized_value v

end ConCert.Examples.BAT.Printers
