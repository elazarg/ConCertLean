# Port Scope

ConCertLean is a Lean 4 port of the executable smart-contract framework from
ConCert's Rocq sources. The port is centered on executable definitions,
local-chain testing, and the application-level proofs that use the executable
framework.

The project has no `sorry`, no `admit`, and no project-specific Lean axioms.
Lean and mathlib foundational axioms such as `propext`, `Classical.choice`, and
`Quot.sound` are not counted as ConCert port debt.

## Included Surface

- The retained `utils/theories`, `execution/theories`, and `execution/test`
  sources have Lean module counterparts.
- The executable example families included are BAT, BoardroomVoting, CIS1,
  Counter, Crowdfunding, Congress, Escrow, PiggyBank, StackInterpreter, EIP20,
  iTokenBuggy, FA1.2, FA2, Dexter, Dexter2, and ExchangeBuggy.
- The included proof surface covers Counter safety, Escrow correctness,
  Congress action-depth correctness, BoardroomVoting trace correctness, BAT
  original/fixed/alt-fixed invariants, Dexter2 FA1.2 and CPMM handler
  correctness, CIS1 balance preservation, PiggyBank reachability safety, EIP20
  supply/balance invariants, and FA1.2 supply/balance invariants.
- `lake build` builds the library, and `lake test` runs the executable generated
  property tests.

## Out Of Scope

- `embedding/` is not ported. It depends on Rocq/MetaRocq syntax and metatheory.
  A Lean version would be a separate design around Lean's own syntax,
  elaborator, or compiler representations.
- `extraction/` is not ported. It depends on MetaRocq's erased AST. A
  Lean-native extraction project would need its own IR choice and soundness
  argument.
- MetaRocq/deep-embedding Crowdfunding files are not direct ports:
  `Crowdfunding.v`, `CrowdfundingData.v`, `CrowdfundingDataExt.v`,
  `CrowdfundingExt.v`, `CrowdfundingCorrect.v`, and
  `ExecFrameworkIntegration.v`.
- Example extraction wrappers are not ported, including files named
  `*Extraction*.v`, `*Extract*.v`, and `*CommonExtract.v`.
- Exact Ltac script replay and exact QuickChick generation/shrinking behavior
  are not goals.
- Lean `String` is not made byte-for-byte identical to Rocq `ascii` strings by
  default. Rocq-style ASCII serialization is exposed through `AsciiString`.

## Public Names

Public Lean names follow the Rocq source names where that is reasonable for
executable definitions, user-facing data types, and advertised theorem
statements. Lean-generated recursor, projection, deriving, and instance names
are outside this audit. Intentional public module and namespace deviations are
listed here; unlisted public-name drift should be fixed or documented.

- **Terminal file-module elision.** Lean declarations usually live in the
  example or library namespace rather than under a repeated final file
  component. For example, declarations from `examples/counter/Counter.v` live
  under `ConCert.Examples.Counter`, not
  `ConCert.Examples.Counter.Counter`. The same convention is used for the main
  files of Crowdfunding, Escrow, ExchangeBuggy, iTokenBuggy, PiggyBank,
  StackInterpreter, and core files such as `ConCert.Execution.BoundedN`.

- **Example-family grouping.** Related files with colliding local names are
  grouped under one family namespace with variant subnamespaces. BAT uses
  `ConCert.Examples.BAT.Original`, `.Fixed`, and `.AltFix`. CIS1's WCCD token
  uses `ConCert.Examples.CIS1.WCCD`. Congress's buggy variant uses
  `ConCert.Examples.Congress.Buggy`. Dexter2 uses
  `ConCert.Examples.Dexter2.FA12` and `.CPMM`. FA2's executable token uses the
  main `ConCert.Examples.FA2` namespace.

- **Lowercase Rocq type names become Lean type names.** Rocq records and
  inductives that denote types but are lowercase in the source are PascalCase in
  Lean. This affects the FA2 interface types `callback`,
  `transfer_destination`, `transfer`, `balance_of_request`,
  `balance_of_response`, `balance_of_param`, `total_supply_response`,
  `total_supply_param`, `token_metadata`, `token_metadata_param`,
  `operator_tokens`, `operator_param`, `update_operator`,
  `is_operator_response`, `is_operator_param`, `self_transfer_policy`,
  `operator_transfer_policy`, `owner_transfer_policy`,
  `permissions_descriptor`, `transfer_destination_descriptor`,
  `transfer_descriptor`, `transfer_descriptor_param`, `fa2_token_receiver`,
  `fa2_token_sender`, and `set_hook_param`.

- **Prefix-heavy CIS1 specification types are shortened inside namespaces.**
  In `ConCert.Examples.CIS1.Spec`, the Rocq names `receive_hook_params`,
  `CIS1ReceiverMsg`, `CIS1_transfer_data`, `CIS1_transfer_params`,
  `CIS1_updateOperator_kind`, `CIS1_updateOperator_update`,
  `CIS1_updateOperator_params`, `CIS1_balanceOf_query`,
  `CIS1_balanceOf_params`, `CIS1_entry_points`, `transfer_spec`,
  `updateOperator_spec`, `balanceOf_callback_type`, and `balanceOf_spec` become
  `ReceiveHook.Params`, `ReceiveHook.ReceiverMsg`, `Axioms.TransferData`,
  `Axioms.TransferParams`, `Axioms.UpdateOperatorKind`,
  `Axioms.UpdateOperatorUpdate`, `Axioms.UpdateOperatorParams`,
  `Axioms.BalanceOfQuery`, `Axioms.BalanceOfParams`, `Axioms.EntryPoint`,
  `Axioms.TransferSpec`, `Axioms.UpdateOperatorSpec`,
  `Axioms.BalanceOfCallbackType`, and `Axioms.BalanceOfSpec`.

- **Support-file roles are namespace suffixes.** Generator, printer, test, and
  test-common files use role namespaces under their example family rather than
  file-module names. This applies to BAT's `.Gens`, `.Printers`, `.Tests`, and
  `.TestCommon`; BoardroomVoting's `.Tests`; Congress's `.Gens`, `.Printers`,
  `.Tests`, `.BuggyGens`, `.BuggyPrinters`, `.LocalBlockchainTests`, and the
  buggy proof namespace `.Buggy`; Dexter's and Dexter2's `.Gens`, `.Printers`,
  and `.Tests`; EIP20Token's `.Gens`, `.Printers`, and `.Tests`; Escrow's
  `.Gens`, `.Printers`, `.Tests`, and `.EscrowCorrectness`; ExchangeBuggy's
  `.Gens`, `.Printers`, and `.Tests`; FA2's `.Gens`, `.Printers`, `.Tests`,
  and `.TestContracts`; iTokenBuggy's `.Gens`, `.Printers`, and `.Tests`;
  CIS1's `.Tests`, `.RemoveProperties`, and `.Spec`; and PiggyBank's
  `.Correctness`.

- **Correctness files either extend the contract namespace or use a named proof
  namespace.** EIP20 and FA1.2 local correctness lemmas extend
  `ConCert.Examples.EIP20.EIP20Token` and `ConCert.Examples.FA1_2`. BAT and
  Dexter2 correctness files use variant namespaces such as
  `ConCert.Examples.BAT.FixedCorrect` and
  `ConCert.Examples.Dexter2.CPMM.Correct`. Escrow and PiggyBank use
  `ConCert.Examples.Escrow.EscrowCorrectness` and
  `ConCert.Examples.PiggyBank.Correctness`.

- **Rocq module functors are flattened into Lean namespaces and typeclasses.**
  Rocq module names such as `FA12Serializable`, `FA12SInstances`,
  `FA12Instance`, `WccdTypes`, `WccdView`, and `WccdReceiveSpec` do not appear
  as separate Lean modules. Their executable definitions and proofs live under
  `ConCert.Examples.FA1_2` and `ConCert.Examples.CIS1`, with serialization
  handled by Lean `Serializable` instances.

- **Upstream-path import modules preserve source-file layout where definitions
  are grouped.** Thin modules with the upstream file names are kept for grouped
  files such as `BATFixed`, `BATAltFix`, `BATFixedTests`, `BATAltFixTests`,
  `BoardroomVotingTest`, `BoardroomVotingZ`, `CIS1wccd`, `Congress_Buggy`,
  `Congress_BuggyGens`, `Congress_BuggyPrinters`, and `Congress_BuggyTests`.
  They import the canonical implementation namespace or grouped test module and
  do not introduce a second set of definitions.

- **`examples/AllTests.v` maps to two Lean entry points.**
  `ConCert.Examples.AllTests` is the examples-level aggregate import module.
  The runnable Lake test driver is repository-root `Tests.lean`.

## Implementation Choices

- `ConCert.Execution.SerializableDerive` provides a bounded
  `deriving Serializable` handler for non-indexed structures and inductives
  with constructors of arity up to 10. It emits the Rocq `Derive Ser` wire
  shape: a zero-based constructor tag plus a right-associated serialized-value
  payload chain.
- `ConCert.Utils.Automation` retains the non-tactic helper lemma used from the
  Rocq automation file. The Ltac-only tactic layer is not ported unless a
  Lean proof actually uses the corresponding tactic.
- `ConCert.Utils.RecordSet` and `ConCert.Utils.RecordUpdate` keep the
  `SetterFromGetter` class and source-style update notation. The MetaRocq
  `make_setters` generator is not reproduced because Lean has built-in record
  update syntax.
- `FMap` is backed by `Std.ExtTreeMap`, Lean's quotient-extensional ordered tree
  map, rather than Rocq/stdpp `gmap` with `Countable`.
- `ChainBase` uses Lean's `DecidableEq`, `Ord`, and `LawfulOrd` structures in
  place of Rocq's `EqDecision` and `Countable` fields.
- `Monad` and `MonadLaws` map to Lean's built-in `Monad` and `LawfulMonad`.
  `MonadTrans` is provided as a thin class in `ConCert.Execution.Monad`.
- `ConCert.Execution.Test.TraceGens`, `TestUtils`, `TestNotation`, and
  `ChainPrinters` are Plausible-backed replacements for the QuickChick test
  layers used by the ported executable tests.
- `ConCert.Execution.Test.LocalBlockchain` stores concrete trace data in
  `LocalChainBuilder.lcb_trace`, so generated tests can inspect block/action
  traces directly.

## Serialization

- `BoundedN` serialization follows the Rocq/stdpp wire shape. `BoundedN` values
  serialize through the explicit `Positive` wrapper and the stdpp `N` encoding
  `n -> n + 1`.
- Lean `String` serialization uses Lean Unicode scalar codepoints.
  `ConCert.Execution.SerializableInstances.Ascii` and `AsciiString` expose the
  Rocq-style ASCII serialization surface.
- Core serialization helper names are public Lean names:
  `serialize_sum`, `deserialize_sum`, `serialize_product`,
  `deserialize_product`, `serialize_list`, `deserialize_list`,
  `serialize_option`, and their round-trip theorems.
- Rocq `Derive Ser` constructor-wire helpers are public Lean names:
  `serialize_constructor0` through `serialize_constructor6`,
  `deserialize_constructor0` through `deserialize_constructor6`, and their
  tag-sensitive round-trip lemmas.

## Upstream Corrections

- `ConCert.Utils.StringExtra.str_map` applies its function argument. The Rocq
  source body ignores the function argument, so the Lean port implements the
  intended behavior rather than preserving the no-op.
- `StepNotPermute.snp_action_invalid` targets `step_action_invalid`. The Rocq
  `BlockchainBFS.v` constructor appears to target `step_action` by mistake.
- `BlockchainBFS.v`'s admitted `dfs_contract_induction` is proved over the
  corrected permutation-free trace predicate.
- `ContractProperties.v`'s admitted `NonPayable_balance_zero` is proved by
  carrying the nonnegative-amount invariant required over `Int`.
- `deployable_address_decidable` is a theorem, not a project axiom. The
  parameterized form is
  `BlockchainBuilder.BuildUtils.action_evaluation_decidable_of_deployable_address_decidable`;
  finite-address chain bases can use
  `deployable_address_decidable_of_finite` and
  `action_evaluation_decidable_of_finite`.

## Axiom Footprint

The advertised theorem surface depends only on Lean/mathlib foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`, or subsets of those. The
following theorem groups are included in that footprint.

Core results:

- `ConCert.Examples.Counter.counter_safe`
- `ConCert.Examples.Counter.counter_correct`
- `ConCert.Examples.Escrow.EscrowCorrectness.escrow_correct_strong`
- `ConCert.Examples.Escrow.EscrowCorrectness.escrow_correct`
- `ConCert.Execution.BlockchainBFS.dfs_contract_induction`
- `ConCert.Execution.ContractProperties.NonPayable_balance_zero`
- `ConCert.Execution.BlockchainBuilder.BuildUtils.{action_evaluation_decidable,
  action_evaluation_decidable_of_deployable_address_decidable,
  deployable_address_decidable_of_finite,
  action_evaluation_decidable_of_finite}`

Headline example results:

- `ConCert.Examples.Congress.{congress_correct,
  congress_correct_after_block}`
- `ConCert.Examples.Congress.Buggy.do_finish_proposal_violates_action_conservation`
- `ConCert.Examples.BoardroomVoting.{boardroom_voting_core_correct_strong,
  boardroom_voting_correct, boardroom_voting_correct_strong}`
- `ConCert.Examples.BAT.Correct.{constants_are_constant, final_is_final,
  receive_total_supply_increasing}`
- `ConCert.Examples.BAT.FixedCorrect.{constants_are_constant, final_is_final,
  receive_total_supply_increasing}`
- `ConCert.Examples.BAT.AltFixCorrect.{constants_are_constant, final_is_final,
  receive_total_supply_increasing}`

Local correctness families:

- `ConCert.Examples.EIP20.EIP20Token.{receive_not_payable, receive_no_acts,
  try_transfer_balance_correct, try_transfer_from_balance_correct,
  try_approve_allowance_correct, try_approve_preserves_balances_sum,
  try_transfer_preserves_balances_sum,
  try_transfer_from_preserves_balances_sum, total_supply_eq_init_supply,
  sum_balances_eq_total_supply, outgoing_acts_nil}`
- `ConCert.Examples.FA1_2.{contract_not_payable,
  try_transfer_balance_correct, try_transfer_allowance_correct,
  try_transfer_new_acts_correct, try_transfer_preserves_total_supply,
  try_transfer_preserves_balances_sum, try_transfer_is_some,
  try_approve_new_acts_correct, try_approve_preserves_total_supply,
  try_approve_preserves_balances_sum, try_approve_allowance_correct,
  try_approve_is_some, try_get_allowance_new_acts_correct,
  try_get_balance_new_acts_correct, try_get_total_supply_new_acts_correct,
  init_total_supply_correct, total_supply_correct,
  sum_balances_eq_total_supply, token_balance_le_total_supply,
  zero_balances_removed, zero_allowances_removed}`
- `ConCert.Examples.PiggyBank.Correctness.{receive_is_correct,
  receive_produces_no_calls_when_running_insert, owner_remains,
  owner_correct, no_self_calls, balance_on_chain', balance_on_chain,
  balance_on_pos, no_outgoing_actions_when_intact,
  state_balance_zero_when_smashed, balance_is_zero_when_smashed',
  balance_is_zero_when_smashed, stay_smashed,
  if_intact_then_balance_can_only_increase, initializes_correctly}`
- `ConCert.Examples.Dexter2.FA12.Correct.{try_transfer_balance_correct,
  try_transfer_allowance_correct, try_approve_allowance_correct,
  try_mint_or_burn_total_supply_correct, init_total_supply_correct}`
- `ConCert.Examples.Dexter2.CPMM.Correct.{add_liquidity_correct,
  xtz_to_token_correct, token_to_xtz_correct, token_to_token_correct,
  remove_liquidity_correct, init_correct}`
- `ConCert.Examples.CIS1.Spec.Operators.{compose_updateOperator_add_add,
  compose_updateOperator_add_remove_same,
  compose_updateOperator_remove_one_remove_another}`
- `ConCert.Examples.CIS1.Spec.Balances.{transfer_preserves_sum_of_balances,
  balanceOf_preserves_sum_of_balances,
  updateOperator_preserves_sum_of_balances}`

The smaller footprints are:

- `propext` only:
  `ConCert.Examples.Dexter2.CPMM.Correct.init_correct`,
  `ConCert.Examples.CIS1.Spec.Operators.{compose_updateOperator_add_add,
  compose_updateOperator_add_remove_same,
  compose_updateOperator_remove_one_remove_another}`,
  `ConCert.Examples.PiggyBank.Correctness.{receive_is_correct,
  receive_produces_no_calls_when_running_insert, owner_remains, stay_smashed,
  initializes_correctly}`, and
  `ConCert.Execution.BlockchainBuilder.BuildUtils.{action_evaluation_decidable_of_deployable_address_decidable,
  deployable_address_decidable_of_finite,
  action_evaluation_decidable_of_finite}`.
- `propext` and `Quot.sound`:
  `ConCert.Examples.CIS1.Spec.Balances.{balanceOf_preserves_sum_of_balances,
  updateOperator_preserves_sum_of_balances}`.

The BoardroomVoting trace theorem is parameterized by the explicit
`BoardroomVotingProtocolCorrect` assumption. That parameter packages the
cryptographic and brute-force tally facts expected by the executable
Z-specialized contract; it is part of the theorem statement, not a Lean axiom.

There is no Lean theorem literally named `piggybank_correct`; the PiggyBank
proof surface keeps the upstream theorem names that exist in
`PiggyBankCorrect.v`, headed by `receive_is_correct` and the reachability
safety lemmas above.

## Example Coverage

- **BAT** ports `BATCommon.v`, `BAT.v`, `BATFixed.v`, `BATAltFix.v`, the three
  correctness files, and the generator/printer/test-common files over the
  local-chain backend.
- **BoardroomVoting** ports the executable `BoardroomVotingZ.v` contract, the
  Egcd/Euler/BoardroomMath pieces needed by the executable contract, tests, and
  the trace-level correctness theorem under `BoardroomVotingProtocolCorrect`.
- **CIS1** ports the WCCD token, list-removal utilities, abstract specification
  records, and generic operator-update and balance-sum preservation proofs.
- **Congress** ports the executable contract, the buggy variant and exploit
  contract, local-chain tests, generators/printers, and the action-depth
  correctness theorems.
- **Counter, Escrow, and PiggyBank** include executable code and their retained
  safety/correctness proofs. PiggyBank omits only the upstream admitted
  `smash_poss` exploit-construction tail.
- **EIP20 and iTokenBuggy** include executable code, generated tests, and EIP20
  local plus chain-level supply/balance preservation proofs. The iTokenBuggy
  self-transfer inflation behavior is preserved and tested as a bug witness.
- **FA1.2** includes executable code, generated tests, and local plus
  chain-level supply/balance correctness lemmas.
- **FA2** includes the interface files, executable token, test contracts,
  generated tests, generators, and printers.
- **Dexter and Dexter2** include executable contracts and generated tests.
  Dexter2 includes the FA1.2 liquidity token and CPMM local handler/init
  correctness files.
- **Crowdfunding** is a shallow executable counterpart of the MetaRocq-based
  upstream example. The deep embedding, extraction wrappers, and reachability
  proofs are out of scope.
- **ExchangeBuggy and StackInterpreter** include executable code and retained
  test coverage.

## Guarantees

- Definitions intended to execute have Lean bodies.
- Included theorem statements are proved.
- The retained core source files have Lean module counterparts, subject to the
  public-name and implementation choices recorded above.
- Public-name deviations are limited to the cases documented in this file.
- The project builds with `lake build`, and the executable test suite runs with
  `lake test`.
