/- Port of execution/theories/Monad.v.

   Upstream's `Monad` / `MonadLaws` are subsumed by Lean's built-in
   `Monad` / `LawfulMonad`. `MonadTrans` (not in Lean core) is provided
   below. -/

namespace ConCert.Execution.Monad

/-- Monad transformer: a way to lift `mt α` into `m α`. -/
class MonadTrans (m : Type → Type) (mt : Type → Type) where
  lift : ∀ {t : Type}, mt t → m t

export MonadTrans (lift)

def monad_map {A B : Type} {m : Type → Type} [Monad m]
    (f : A → m B) : List A → m (List B)
  | []      => pure []
  | x :: xs => do
    let v ← f x
    let vs ← monad_map f xs
    pure (v :: vs)

axiom monad_map_map :
  ∀ {A B Z : Type} {m : Type → Type} [Monad m]
    (f : A → m B) (g : Z → A) (xs : List Z),
    monad_map f (xs.map g) = monad_map (fun z => f (g z)) xs

def monad_foldr {A B : Type} {m : Type → Type} [Monad m]
    (f : A → B → m A) (a : A) : List B → m A
  | []      => pure a
  | x :: xs => do
    let v ← monad_foldr f a xs
    f v x

def monad_foldl {A B : Type} {m : Type → Type} [Monad m]
    (f : A → B → m A) (a : A) : List B → m A
  | []      => pure a
  | x :: xs => do
    let v ← f a x
    monad_foldl f v xs

end ConCert.Execution.Monad
