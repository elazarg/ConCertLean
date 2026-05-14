/- Port of utils/theories/RecordSet.v.

The original is a MetaRocq Template-monad macro that generates `set_<R>_<field>`
functions and `SetterFromGetter` instances for each record field, plus
record-update notations `r <| field := v |>` / `r <| field ::= f |>`.

In Lean 4, record update is built into the language as `{ r with field := v }`,
so the metaprogramming half is intentionally not reproduced. This file keeps
the application helpers and notations used by source ports that provide
`SetterFromGetter` instances explicitly. -/

namespace ConCert.Utils.RecordSet

class SetterFromGetter {A B : Type} (getter : A → B) where
  setter_from_getter : (B → B) → A → A

namespace SetterFromGetter

@[inline] def modify {A B : Type} (getter : A → B) [SetterFromGetter getter]
    (f : B → B) (x : A) : A :=
  SetterFromGetter.setter_from_getter (getter := getter) f x

@[inline] def set {A B : Type} (getter : A → B) [SetterFromGetter getter]
    (v : B) (x : A) : A :=
  modify getter (fun _ => v) x

end SetterFromGetter

@[inline] def modify_from_getter {A B : Type} (getter : A → B)
    [SetterFromGetter getter] (f : B → B) (x : A) : A :=
  SetterFromGetter.modify getter f x

@[inline] def set_from_getter {A B : Type} (getter : A → B)
    [SetterFromGetter getter] (v : B) (x : A) : A :=
  SetterFromGetter.set getter v x

syntax:12 term:12 " <| " term:13 " ::= " term:13 " |>" : term
syntax:12 term:12 " <| " term:13 " := " term:13 " |>" : term

macro_rules
  | `($x <| $getter ::= $f |>) =>
      `(modify_from_getter $getter $f $x)
  | `($x <| $getter := $v |>) =>
      `(set_from_getter $getter $v $x)

end ConCert.Utils.RecordSet
