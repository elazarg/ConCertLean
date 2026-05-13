/- Port of execution/theories/SerializableDerive.v.

   ## Scope

   The Coq file is 173 lines of Ltac1 + Ltac2 tactics that *automatically*
   derive a `Serializable` instance for any inductive given its `_rect` and
   constructor list:

   ```coq
   Derive Serializable Msg_rect < commit_money, confirm_item_received, withdraw >.
   ```

   The equivalent Lean 4 mechanism is a `deriving` handler — a small piece of
   metaprogramming using `Lean.Elab.Deriving` that inspects the inductive's
   constructors and emits the encode/decode functions plus the round-trip
   proof.

   We have **not** ported this. Until it lands, contracts have to provide
   their `Serializable` instances by hand. Counter and Escrow do this (via
   `Sum`-of-`Sum` and `Nat`-tag encodings respectively).

   ## Hand-writing recipe

   For a contract message `inductive Msg | C1 (a : A) | C2 (b : B) | C3`
   the conventional encoding is:

   * `serialize` builds a `Sum`-tagged value: `C1 a` → `Sum.inl a`,
     `C2 b` → `Sum.inr (Sum.inl b)`, `C3` → `Sum.inr (Sum.inr ())`, then
     delegate to the `Sum`/`Unit` `Serializable` instances.
   * `deserialize` runs the reverse.
   * The round-trip proof is a one-line `cases`/`simp`.

   For record types, encode as the tuple of fields and use the `product`
   instance.

   See `ConCert.Examples.Counter.Counter` and `ConCert.Examples.Escrow.Escrow`
   for worked examples. -/

namespace ConCert.Execution.SerializableDerive

end ConCert.Execution.SerializableDerive
