/- Port of execution/test/ChainPrinters.v.

   Minimal compatibility layer. The original derives `Show` instances for
   chain types via QuickChick's `Derive Show` Ltac; this port provides simple
   stringification shells. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Serializable
import ConCert.Execution.ChainedList
import ConCert.Execution.Test.TestUtils

namespace ConCert.Execution.Test.ChainPrinters

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils

def sep : String := ", "

variable [Base : ChainBase]

def string_of_serialized_type : SerializedType → String
  | .ser_unit         => "unit"
  | .ser_int          => "int"
  | .ser_bool         => "bool"
  | .ser_pair a b     => "(" ++ string_of_serialized_type a ++ " * " ++ string_of_serialized_type b ++ ")"
  | .ser_list a       => "list " ++ string_of_serialized_type a

def ex_serialized_type : SerializedType :=
  .ser_pair (.ser_list (.ser_list .ser_bool)) .ser_int

def string_of_interp_type : (st : SerializedType) → interp_type st → String
  | .ser_unit, _ => "()"
  | .ser_int,  _ => "<int>"
  | .ser_bool, _ => "<bool>"
  | .ser_pair _ _, _ => "<pair>"
  | .ser_list _, _ => "<list>"

end ConCert.Execution.Test.ChainPrinters
