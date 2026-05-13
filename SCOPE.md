# Port scope

This document records deliberate scope boundaries for the ConCert to Lean 4
port. Items listed here are not expected to be faithful to the Rocq source until
explicitly closed. The goal of the in-scope port is to preserve the definitions,
theorem statements, and executable behavior needed to begin proof porting, within
Lean's libraries and idioms.

This is not a promise of byte-for-byte serialization compatibility, tactic
compatibility, or exact public-name compatibility with every Rocq helper.

## Out of scope subprojects

- **`embedding/`**: the lambda-smart deep embedding is removed.
  Reason: it depends on Rocq/MetaRocq syntax and metatheory.
  Possible approach: design a separate Lean-native embedding, or target Lean's
  own elaborator/compiler representations as a new project.

- **`extraction/`**: the verified extraction pipeline to Liquidity, CameLIGO,
  Elm, and Rust is removed.
  Reason: it is built on MetaRocq's erased AST, which has no direct Lean
  equivalent.
  Possible approach: build a new extraction story around Lean compiler IR such
  as `Lean.Compiler.LCNF`, with separate correctness arguments.

## Retained modules with scoped deviations

### Metaprogramming and tactics

- **`ConCert.Execution.SerializableDerive`** is a stub.
  Reason: the Rocq file is an Ltac/Ltac2 deriving tactic; Lean needs an
  elaborator command, deriving handler, or macro implementation.
  Possible approach: implement a Lean `deriving Serializable` handler and use
  the existing handwritten instances as expected encodings.

- **`ConCert.Utils.Automation`** is a tactic stub.
  Reason: Rocq Ltac tactics such as `propify`, `destruct_match`, and
  `perm_simplify` do not translate directly to Lean.
  Possible approach: port only the tactics that materially reduce proof-porting
  friction, using Lean tactic macros and existing tactics such as `simp`,
  `omega`, `rcases`, and `aesop`.

- **`ConCert.Utils.RecordSet` / `RecordUpdate`** keep only the
  `SetterFromGetter` class.
  Reason: the Rocq files use MetaRocq to generate setters and record-update
  notation; Lean already has built-in `{ r with field := value }` syntax.
  Possible approach: add compatibility notation or an elaborator command if
  proof ports need the generated setter names.

### Local blockchain tests and generators

- **`ConCert.Execution.Test.LocalBlockchain` trace witnesses** are
  propositional (`Nonempty (ChainTrace ...)`) rather than stored trace data.
  Reason: constructing the concrete `ChainTrace` values is proof work over the
  `ChainStep` semantics, while the executable builder can already run.
  Possible approach: replace `add_block_trace` with constructive trace proofs
  and store the trace data directly in the builder.

- **`ConCert.Execution.Test.TraceGens`, `TestUtils`, and `TestNotation`** are
  Plausible-backed shims.
  Reason: the Rocq files are QuickChick generator/checker infrastructure; full
  generator parity is not needed for the core proof-porting surface.
  Possible approach: port the generator combinators and checkers when examples
  and property-based testing become in scope.

### Serialization and data representation

- **`BoundedN` serialization** uses raw `Int` with non-negativity and bound
  checks.
  Reason: the Rocq encoding goes through `countable.encode` and `positive`,
  while the Lean port does not retain the same `Countable` infrastructure.
  Possible approach: port `encode_bounded`/`decode_bounded` and positive/N
  serialization, then switch the `BoundedN` instance to the Rocq wire format.

- **`String` serialization** uses Lean Unicode scalar codepoints.
  Reason: Lean `String`/`Char` is Unicode-based, while Rocq `string` is a list
  of `ascii`; the Rocq instance rejects character codes greater than or equal to
  256.
  Possible approach: introduce an ASCII string wrapper or port an `Ascii`
  datatype and use it for format-faithful serialization.

- **Some Rocq serialization helper declarations are not public Lean names**.
  Examples include `serialize_sum`, `deserialize_sum`, `serialize_list`, and
  related round-trip helper names.
  Reason: Lean instances expose the behavior, but local helpers are private or
  named idiomatically.
  Possible approach: add public compatibility wrappers and theorem aliases with
  Rocq-style names.

### Architectural substitutions

- **`FMap` is backed by `Std.ExtTreeMap`** — Lean's standard quotient-
  wrapped, extensional ordered tree map — rather than Rocq/stdpp `gmap`
  with `Countable`. `ExtTreeMap` is propositionally extensional
  (`Std.ExtTreeMap.ext_getElem?`, `toList_inj`): two maps with the same
  `get?` view are propositionally equal. This gives us `gmap`'s key
  property without rolling a canonicalization layer. `Std.TreeMap` was
  rejected as a backing — it exposes the underlying tree shape, so
  insertion order can yield different propositionally-distinct maps
  with the same view.

- **FMap algebraic facts (`add_remove`, `add_add`, `add_commute`,
  `of_elements_eq`, the `Serializable` round-trip, etc.) are stated as
  propositional `=`** thanks to the extensional `ExtTreeMap` backing.
  Most are axiomatized for now; they are derivable from `ExtTreeMap`'s
  lemma library (`getElem?_insert`, `getElem?_erase`, `ext_getElem?`,
  `toList_inj`).

- **`ChainBase` uses Lean equality/order structures**:
  `DecidableEq`, `Ord`, and `LawfulOrd` replace Rocq's `EqDecision` and
  `Countable` fields.
  Reason: these are the structures needed by the Lean map implementation.
  Possible approach: add Rocq-style compatibility fields or wrappers if proof
  ports need to unfold the original typeclass structure.

- **`Monad`/`MonadLaws` map to Lean's built-in `Monad`/`LawfulMonad`**;
  `MonadTrans` is provided as a thin class in
  `ConCert.Execution.Monad`. All four `ContractMonads` `MonadTrans`
  instances (`reader→initer`, `result→initer`, `reader→receiver`,
  `result→receiver`) are present.

### Intentional source corrections

- **`ConCert.Utils.StringExtra.str_map` applies its function argument**.
  Reason: the Rocq source's `str_map` body ignores the function argument; this
  appears to be an upstream oversight.
  Possible approach: add a separate compatibility definition for the Rocq no-op
  behavior if a proof depends on it.

- **`StepNotPermute.snp_action_invalid` targets `step_action_invalid`**.
  Reason: the Rocq statement appears to point at `step_action` by copy-paste
  mistake.
  Possible approach: add a compatibility lemma for the exact Rocq statement if
  needed for proof scripts, but do not rely on it semantically.

### Induction principles

- **`contract_induction` and `dfs_contract_induction` bundle case premises in
  `ContractInductionCases`**.
  Reason: the Rocq statements have many flat premises; bundling keeps the Lean
  theorem usable while preserving the same seven case obligations.
  Possible approach: expose flat-argument compatibility theorems with the Rocq
  premise order.

- **`nonrecursive_contract_induction` uses `NonRecursiveContractInductionCases`**.
  Reason: the Rocq nonrecursive theorem omits the recursive-call case.
  Possible approach: expose a compatibility theorem if a flat Rocq-style
  statement is useful for proof ports.

## Examples

- **Counter and Escrow executable contracts are included.**
  Reason: they are useful smoke tests for the executable surface and
  serialization conventions.
  Possible approach: keep these executable contracts aligned as the core proof
  surface evolves.

- **Example correctness proofs are deferred.**
  Reason: example proof ports depend on the core induction and contract-property
  infrastructure.
  Possible approach: before porting example proofs, restore the full Rocq
  theorem statements where they are currently compressed, especially in
  `EscrowCorrect`.

## In-scope guarantees

- The retained `utils`, `execution/theories`, and `execution/test` source files
  have Lean module counterparts, subject to the deviations above.
- Definitions intended to execute have real Lean bodies.
- Theorem/proof obligations are represented as `Prop`-typed axioms awaiting
  proofs.
- The port should build with `lake build`.

## Not guaranteed

- Exact tactic compatibility with Rocq proofs.
- Exact public declaration names for helper definitions and lemmas.
- Byte-for-byte compatibility with Rocq serialization formats unless explicitly
  stated.
- Full example-correctness theorem parity until examples are brought back into
  scope.
