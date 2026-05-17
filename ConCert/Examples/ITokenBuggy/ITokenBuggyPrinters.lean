/- Port of examples/iTokenBuggy/iTokenBuggyPrinters.v. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Examples.ITokenBuggy.ITokenBuggy

namespace ConCert.Examples.ITokenBuggy.Printers

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.Test.ChainPrinters
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.ITokenBuggy

variable [Base : ChainBase]

def string_of_msg (showAddr : Base.Address → String) : @Msg Base → String
  | .transfer_from from_ to_ amount =>
      "transfer_from " ++ showAddr from_ ++ " " ++ showAddr to_ ++ " " ++
        toString amount
  | .approve delegate amount =>
      "approve " ++ showAddr delegate ++ " " ++ toString amount
  | .mint amount => "mint " ++ toString amount
  | .burn amount => "burn " ++ toString amount

def string_of_setup (showAddr : Base.Address → String) (setup : @Setup Base) :
    String :=
  "Setup{owner=" ++ showAddr setup.owner ++ sep ++
    "init_amount=" ++ toString setup.init_amount ++ "}"

def string_of_allowances
    (showAddr : Base.Address → String)
    (m : FMap Base.Address (FMap Base.Address Nat)) : String :=
  string_of_FMap showAddr (string_of_FMap showAddr toString) m

def string_of_state (showAddr : Base.Address → String) (s : @State Base) :
    String :=
  "State{total_supply=" ++ toString s.total_supply ++ sep ++
    "balances=" ++ string_of_FMap showAddr toString s.balances ++ sep ++
    "allowances=" ++ string_of_allowances showAddr s.allowances ++ "}"

def string_of_serialized_msg
    (v : ConCert.Execution.SerializableBase.SerializedValue) : String :=
  string_of_serialized_value v

end ConCert.Examples.ITokenBuggy.Printers
