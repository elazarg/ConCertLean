# Port scope

This document records the deliberate scope boundaries for the ConCert to Lean 4
port. The current project is a buildable Lean port of the executable ConCert
core, not a full port of every subproject and example in the parent Rocq
repository.

## Current state

- The retained `utils/theories`, `execution/theories`, and `execution/test`
  Rocq files have Lean module counterparts.
- The port builds with `lake build`, and `lake test` runs a small executable
  smoke-test target.
- There are no `sorry` or `admit` placeholders in the Lean sources.
- The only project-specific Lean axiom is
  `ConCert.Execution.BlockchainBuilder.BuildUtils.deployable_address_decidable`.
  This mirrors an upstream Rocq `Axiom`; it is not newly introduced proof debt.
- Counter, Escrow, and PiggyBank executable contracts are included. Counter
  safety and Escrow functional correctness are proved in Lean.

Lean foundational axioms used through mathlib and Lean's libraries, such as
`propext`, quotient soundness, and classical choice, are not counted as ConCert
port debt.

This is not a promise of byte-for-byte serialization compatibility, exact tactic
compatibility, or exact public-name compatibility with every Rocq helper.

## Out of scope subprojects

- **`embedding/`**: the lambda-smart deep embedding is removed.
  Reason: it depends on Rocq/MetaRocq syntax and metatheory.
  Feasibility: not a reasonable direct port. A Lean version would be a separate
  design project, likely targeting Lean's own elaborator/compiler
  representations.

- **`extraction/`**: the verified extraction pipeline to Liquidity, CameLIGO,
  Elm, and Rust is removed.
  Reason: it is built on MetaRocq's erased AST, which has no direct Lean
  equivalent.
  Feasibility: not a reasonable direct port. A Lean-native extraction story
  could be built around compiler IR such as `Lean.Compiler.LCNF`, but that is a
  separate research/engineering project with new correctness arguments.

## Retained modules with scoped deviations

### Metaprogramming and tactics

- **`ConCert.Execution.SerializableDerive`** has a bounded Lean
  `deriving Serializable` handler.
  It supports non-indexed structures/inductives with constructors of arity up
  to 6 and emits the Rocq `Derive Ser` wire shape: a zero-based `Nat`
  constructor tag plus a right-associated `SerializedValue` payload chain.
  Indexed, recursive, and larger-arity derivations should still be written by
  hand or added deliberately when they appear in source ports.

- **`ConCert.Utils.Automation`** provides conservative tactic wrappers.
  Rocq Ltac tactics such as `propify`, `destruct_match`, `perm_simplify`,
  `tryfalse`, and related names are exposed as Lean tactic macros over native
  tactics such as `simp_all`, `split`, `constructor`, and `contradiction`.
  They preserve common call names for proof ports, but scripts still need local
  adaptation when Ltac search behavior mattered.

- **`ConCert.Utils.RecordSet` / `RecordUpdate`** keep the
  `SetterFromGetter` class plus application helpers and compatibility notation.
  The MetaRocq `make_setters` generator is not reproduced because Lean has
  built-in `{ r with field := value }` syntax. Ports can use
  `r <| getter := v |>` and `r <| getter ::= f |>` when explicit
  `SetterFromGetter` instances are available.

- **Proof-port convenience tactics and notations are intentionally shallow.**
  `Env` lookup/update notation plus focused wrappers such as
  `destruct_chain_step`, `contract_simpl`, and `trace_induction` are exposed as
  Lean `syntax`/`macro_rules` wrappers over native tactics. These preserve
  common call names for ports, but exact Ltac search behavior is not a good
  target.

### Local blockchain tests and generators

- **`ConCert.Execution.Test.LocalBlockchain` trace witnesses** are stored as
  propositional `Nonempty (ChainTrace ...)` witnesses rather than as direct
  trace data in the executable builder.
  Reason: the executable builder stays computational, while concrete trace
  construction remains proof-carrying.
  Feasibility: replacing the `Nonempty` field with stored trace data is
  possible: `LocalChainBuilder.lcb_trace` would become the actual
  `LCTrace`, `add_block_trace` would return that trace directly, and
  `LocalChainBuilderImpl.builder_trace` would no longer use `Nonempty.some`.
  This is medium implementation churn with little proof or execution benefit unless
  downstream tests need executable trace inspection or trace shrinking.

- **`ConCert.Execution.Test.TraceGens`, `TestUtils`, `TestNotation`, and
  `ChainPrinters`** are Plausible-backed or deterministic compatibility
  layers.
  Reason: the Rocq files are QuickChick generator/checker/printing
  infrastructure. Full generator and notation parity is not needed for the core
  proof-porting surface. `TestUtils` includes the common local-chain constants,
  deterministic address generator wrappers, and checker combinators such as
  `conjoin_no_discard`, but does not attempt QuickChick shrinking/search
  parity.
  Feasibility: adding the common generators, checkers, and printers is
  reasonable if the parent test suites are ported. Exact QuickChick behavior is
  not worth treating as a compatibility requirement.

- **A Lake smoke-test driver is present.**
  `Tests.lean` checks a small executable surface for serialization,
  `LocalBlockchain`, proof symbols, and compatibility wrappers. It is not intended
  to replace broader example-specific or property-based tests.

### Serialization and data representation

- **`BoundedN` serialization** follows the Rocq/stdpp wire shape.
  The Lean port has an explicit `Positive` wrapper plus
  `encode_bounded`/`decode_bounded`; `BoundedN` values serialize through the
  stdpp-compatible `N` encoding `n ↦ n + 1`.

- **`String` serialization** uses Lean Unicode scalar codepoints.
  Reason: Lean `String`/`Char` is Unicode-based, while Rocq `string` is a list
  of `ascii`; the Rocq instance rejects character codes greater than or equal to
  256.
  Compatibility path: `ConCert.Execution.SerializableInstances.Ascii` and
  `AsciiString` provide Rocq-style ASCII serialization while leaving Lean
  `String` Unicode-native.

- **Core Rocq serialization helper declarations are public Lean names.**
  `serialize_sum`, `deserialize_sum`, `serialize_product`,
  `deserialize_product`, `serialize_list`, `deserialize_list`,
  `serialize_option`, and their round-trip theorems are exposed. Less common
  theorem aliases can be added as proof ports discover exact-name needs.

- **Rocq `Derive Ser` constructor-wire helpers are public Lean names.**
  `serialize_constructor0` through `serialize_constructor6`,
  `deserialize_constructor0` through `deserialize_constructor6`, and their
  tag-sensitive round-trip lemmas expose the original constructor-tag encoding
  for handwritten instances and the Lean deriving handler.

### Architectural substitutions

- **`FMap` is backed by `Std.ExtTreeMap`** — Lean's quotient-extensional
  ordered tree map — rather than Rocq/stdpp `gmap` with `Countable`.
  `ExtTreeMap` is propositionally extensional (`Std.ExtTreeMap.ext_getElem?`,
  `toList_inj`): two maps with the same `get?` view are propositionally equal.
  `Std.TreeMap` was rejected as a backing because it exposes tree shape, so
  insertion order can yield different propositionally-distinct maps with the
  same view.

- **FMap algebraic facts are proved as propositional equalities.**
  This includes `add_remove`, `add_add`, `add_commute`, `of_elements_eq`, and
  serialization round-trip facts.

- **`ChainBase` uses Lean equality/order structures**:
  `DecidableEq`, `Ord`, and `LawfulOrd` replace Rocq's `EqDecision` and
  `Countable` fields.
  Feasibility: Rocq-style compatibility wrappers can be added if a proof port
  needs to unfold those original typeclass structures.

- **`Monad`/`MonadLaws` map to Lean's built-in `Monad`/`LawfulMonad`**;
  `MonadTrans` is provided as a thin class in
  `ConCert.Execution.Monad`. All four `ContractMonads` `MonadTrans` instances
  (`reader→initer`, `result→initer`, `reader→receiver`, `result→receiver`) are
  present.

## Upstream corrections and proved upstream gaps

- **`ConCert.Utils.StringExtra.str_map` applies its function argument.**
  The Rocq source's `str_map` body ignores the function argument, so operations
  built from it, such as upper/lower casing, cannot have the intended behavior.
  The Lean port fixes this rather than preserving the no-op behavior.

- **`StepNotPermute.snp_action_invalid` targets `step_action_invalid`.**
  The Rocq `BlockchainBFS.v` constructor appears to target `step_action` by
  mistake. The Lean port corrects it to the invalid-action step.

- **The upstream `BlockchainBFS.v` `dfs_contract_induction` admit is proved.**
  The Lean proof works over the corrected permutation-free trace predicate and
  uses `DFSContractInductionCases`, a bundled version of the Rocq premises that
  omits the permutation case.

- **The upstream `ContractProperties.v` `NonPayable_balance_zero` admit is
  proved.**
  The proof needs the nonnegative-amount invariant supplied by the blockchain
  semantics: from `NonPayable` and a successful init/receive one gets
  `¬ ctx_amount > 0`; over `Int`, concluding `ctx_amount = 0` also requires
  `ctx_amount ≥ 0`. The Lean proof carries that fact through the induction.

- **`deployable_address_decidable` remains an inherited axiom.**
  This is not provable from the current generic `ChainBase`; it assumes a
  decidable search for some fresh deployable contract address. The required
  assumption is factored as
  `BlockchainBuilder.BuildUtils.DeployableAddressDecidableAssumption`, and the
  main decidability proof is also available in a parameterized form,
  `action_evaluation_decidable_of_deployable_address_decidable`. The axiom-backed
  `action_evaluation_decidable` theorem remains for compatibility. The axiom
  can be eliminated for concrete chain bases, or generically after strengthening
  `ChainBase` with an explicit fresh-address/search assumption.

## Axiom audit

`#print axioms` reports that the main proved results advertised by this port
use only Lean/mathlib foundational axioms (`propext`, `Classical.choice`, and
`Quot.sound`):

- `Counter.counter_safe`
- `EscrowCorrectness.escrow_correct`
- `BlockchainBFS.dfs_contract_induction`
- `ContractProperties.NonPayable_balance_zero`

The compatibility theorem `BlockchainBuilder.BuildUtils.action_evaluation_decidable`
also depends on the inherited project axiom
`deployable_address_decidable`. Its parameterized variant,
`action_evaluation_decidable_of_deployable_address_decidable`, depends only on
the explicit deployable-address assumption supplied as an argument, plus
standard Lean/mathlib axioms.

## Induction principles

- **`contract_induction` and `dfs_contract_induction` bundle case premises in
  records.**
  `ContractInductionCases` and `DFSContractInductionCases` keep the Lean
  theorem statements usable while preserving the same case obligations.
  Flat constructor aliases `contract_induction_cases` and
  `dfs_contract_induction_cases` expose the same case premises positionally for
  proof ports that do not need a separate theorem wrapper.

- **`nonrecursive_contract_induction` uses
  `NonRecursiveContractInductionCases`.**
  The Rocq nonrecursive theorem omits the recursive-call case. The Lean record
  mirrors that shape. The flat constructor alias
  `nonrecursive_contract_induction_cases` exposes those premises positionally.

## Examples

- **Counter, Escrow, and PiggyBank executable contracts are included.**
  Their serializer instances use the Rocq `Derive Ser` constructor-tag wire
  shape, and the serializer round-trip obligations are theorem proofs.

- **Counter safety and Escrow correctness are included.**
  `Counter.counter_safe`, `EscrowCorrectness.escrow_correct_strong`, and
  `EscrowCorrectness.escrow_correct` are proved in Lean.

- **PiggyBank is execution-only.**
  `examples/piggybank/PiggyBank.v` is ported, but
  `PiggyBankCorrect.v` is not included.

- **Most parent examples remain out of scope.**
  Feasibility varies. Examples that primarily depend on the execution layer are
  reasonable to port one at a time. Examples that depend heavily on the removed
  extraction or embedding subprojects, generated QuickChick infrastructure, or
  substantial external mathematics are larger projects.

## Reasonable future work

These omissions are practical next steps, roughly sorted by value per unit of
implementation/proof effort:

- Add exact-name theorem aliases where downstream ports depend on Rocq names.
- Add more proof-port notations and tactic wrappers only when downstream proof
  ports need them.
- Add full flat theorem wrappers for `contract_induction`,
  `nonrecursive_contract_induction`, and `dfs_contract_induction` only if a
  proof port needs exact theorem names or exact Rocq premise order beyond the
  existing constructor aliases.
- Discharge `deployable_address_decidable` for concrete chain bases, using the
  explicit `DeployableAddressDecidableAssumption` shape as the proof target.
- Port additional execution-only examples incrementally.
- Expand Plausible-backed generators/checkers enough to port selected tests.
- Replace `LocalBlockchain`'s `Nonempty` trace storage with explicit trace data
  only if selected tests need executable trace inspection or trace shrinking.

These omissions are not reasonable as direct compatibility work:

- Directly porting MetaRocq-based `embedding/`.
- Directly porting the MetaRocq erased-AST extraction pipeline.
- Reproducing exact Ltac search behavior.
- Reproducing exact QuickChick generation/shrinking behavior.
- Making Lean `String` byte-for-byte identical to Rocq `ascii` strings by
  default; use `AsciiString` for that compatibility surface instead.

## In-scope guarantees

- The retained core source files have Lean module counterparts, subject to the
  deviations above.
- Definitions intended to execute have real Lean bodies.
- Included theorem statements are proved, except for the inherited
  `deployable_address_decidable` axiom.
- The port should build with `lake build`; smoke checks should pass with
  `lake test`.

## Not guaranteed

- Exact tactic compatibility with Rocq proofs.
- Exact public declaration names for every helper definition and lemma.
- Byte-for-byte compatibility with Rocq serialization formats unless explicitly
  stated.
- Full example, embedding, extraction, or QuickChick test parity with the parent
  repository.
