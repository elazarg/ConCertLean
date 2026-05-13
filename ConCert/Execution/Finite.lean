/- Port of execution/theories/Finite.v -/

namespace ConCert.Execution.Finite

class Finite (T : Type) where
  elements : List T
  elements_set : List.Nodup elements
  elements_all : ∀ (t : T), t ∈ elements

end ConCert.Execution.Finite
