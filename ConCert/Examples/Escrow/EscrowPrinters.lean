/- Port of examples/escrow/tests/EscrowPrinters.v. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Examples.Escrow.Escrow

namespace ConCert.Examples.Escrow.Printers

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Test.ChainPrinters
open ConCert.Examples.Escrow

variable [Base : ChainBase]

def string_of_next_step : NextStep → String
  | .buyer_commit => "buyer_commit"
  | .buyer_confirm => "buyer_confirm"
  | .withdrawals => "withdrawals"
  | .no_next_step => "no_next_step"

def string_of_msg : Msg → String
  | .commit_money => "commit_money"
  | .confirm_item_received => "confirm_item_received"
  | .withdraw => "withdraw"

def string_of_setup (showAddr : Base.Address → String) (setup : @Setup Base) : String :=
  "Setup{buyer=" ++ showAddr setup.setup_buyer ++ "}"

def string_of_state (showAddr : Base.Address → String) (s : @State Base) : String :=
  "EscrowState{last_action=" ++ toString s.last_action ++ sep ++
    "next_step=" ++ string_of_next_step s.next_step ++ sep ++
    "seller=" ++ showAddr s.seller ++ sep ++
    "buyer=" ++ showAddr s.buyer ++ sep ++
    "seller_withdrawable=" ++ toString s.seller_withdrawable ++ sep ++
    "buyer_withdrawable=" ++ toString s.buyer_withdrawable ++ "}"

def string_of_serialized_msg (v : ConCert.Execution.SerializableBase.SerializedValue) :
    String :=
  string_of_serialized_value v

end ConCert.Examples.Escrow.Printers
