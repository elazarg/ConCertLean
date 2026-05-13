/- Port of execution/theories/ResultMonad.v.

   `Result T E` is `Except E T` modulo naming. We keep the upstream name
   and the `Ok`/`Err` constructors. -/

import ConCert.Execution.Monad

namespace ConCert.Execution.ResultMonad

inductive Result (T E : Type) where
  | Ok  (t : T) : Result T E
  | Err (e : E) : Result T E

export Result (Ok Err)

@[inline] def Result.bind {T U E : Type}
    (mt : Result T E) (f : T → Result U E) : Result U E :=
  match mt with
  | .Ok t  => f t
  | .Err e => .Err e

@[inline] def Result.pure {T E : Type} (t : T) : Result T E := .Ok t

instance {E : Type} : Monad (Result · E) where
  pure := Result.pure
  bind := Result.bind

instance {E : Type} : LawfulMonad (Result · E) :=
  LawfulMonad.mk' (Result · E)
    (id_map := by intro α x; cases x <;> rfl)
    (pure_bind := by intro α β x f; rfl)
    (bind_assoc := by intro α β γ x f g; cases x <;> rfl)

def result_of_option {T E : Type} (o : Option T) (err : E) : Result T E :=
  match o with
  | some a => .Ok a
  | none   => .Err err

def option_of_result {T E : Type} (r : Result T E) : Option T :=
  match r with
  | .Ok t  => some t
  | .Err _ => none

/-- Coq's `MonadTrans (fun T => E -> Result T E) Option`. -/
instance instOptionToResult {E : Type} :
    ConCert.Execution.Monad.MonadTrans (fun T => E → Result T E) Option where
  lift := fun opt err => result_of_option opt err

/-- Coq's `MonadTrans Option (fun T => Result T E)`. -/
instance instResultToOption {E : Type} :
    ConCert.Execution.Monad.MonadTrans Option (fun T => Result T E) where
  lift := option_of_result

def unpack_result {T E : Type} (r : Result T E) :
    (match r with | .Ok _ => T | .Err _ => E) :=
  match r with
  | .Ok t  => t
  | .Err e => e

def bind_error {T E1 E2 : Type} (f : E1 → E2) (r : Result T E1) : Result T E2 :=
  match r with
  | .Ok t  => .Ok t
  | .Err e => .Err (f e)

def isOk {T E : Type} (r : Result T E) : Bool :=
  match r with | .Ok _ => true | .Err _ => false

def isErr {T E : Type} (r : Result T E) : Bool :=
  match r with | .Ok _ => false | .Err _ => true

axiom result_of_option_eq_some :
  ∀ {T E : Type} (x : Option T) (e : E) (y : T),
    result_of_option x e = .Ok y ↔ x = some y

axiom result_of_option_eq_none :
  ∀ {T E : Type} (x : Option T) (e1 e2 : E),
    result_of_option x e1 = .Err e2 → x = none

axiom isOk_Ok :
  ∀ {T E : Type} (r : Result T E) (x : T),
    r = .Ok x → isOk r = true

axiom isOk_Err :
  ∀ {T E : Type} (r : Result T E) (e : E),
    r = .Err e → isOk r = false

axiom isOk_exists :
  ∀ {T E : Type} (r : Result T E),
    isOk r = true ↔ ∃ x : T, r = .Ok x

axiom isOk_not_exists :
  ∀ {T E : Type} (r : Result T E),
    isOk r = false ↔ ∀ x : T, r ≠ .Ok x

axiom isOk_neq_isErr :
  ∀ {T E : Type} (r : Result T E),
    isOk r ≠ isErr r

end ConCert.Execution.ResultMonad
