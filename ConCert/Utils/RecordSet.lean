/- Port of utils/theories/RecordSet.v.

The original is a MetaRocq Template-monad macro that generates `set_<R>_<field>`
functions and `SetterFromGetter` instances for each record field, plus
record-update notations `r <| field := v |>` / `r <| field ::= f |>`.

In Lean 4, record update is built into the language as `{ r with field := v }`,
so this whole file is subsumed by core Lean. We provide the `SetterFromGetter`
typeclass for any code that mentions it, and a placeholder for `make_setters`. -/

namespace ConCert.Utils.RecordSet

class SetterFromGetter {A B : Type} (getter : A → B) where
  setter_from_getter : (B → B) → A → A

end ConCert.Utils.RecordSet
