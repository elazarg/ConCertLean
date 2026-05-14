# ConCertLean

Lean 4 port of the executable core of ConCert's Rocq sources.

This is not a full port of the parent repository. The current scope is the
`utils/theories`, `execution/theories`, and `execution/test` core, plus the
Counter, Escrow, and PiggyBank examples. The Lean tree builds, contains no `sorry` or
`admit`, and currently has one project-specific axiom:
`ConCert.Execution.BlockchainBuilder.BuildUtils.deployable_address_decidable`,
which is inherited from the upstream Rocq development.

See [SCOPE.md](SCOPE.md) for the exact boundaries, intentional deviations from
the Rocq sources, upstream fixes, and a feasibility assessment for the omitted
parts.

## Build

The Lean toolchain and mathlib revision are pinned to Lean 4.29.0.

```bash
lake build
lake test
```

`lake test` runs a small smoke-test executable over serialization,
`LocalBlockchain`, proof symbols, and compatibility wrappers.

## Status

- In-scope file coverage: all retained `utils/theories`, `execution/theories`,
  and `execution/test` Rocq files have Lean module counterparts.
- Counter, Escrow, and PiggyBank executable contracts are ported.
- Counter safety and Escrow functional-correctness proofs are included.
- The upstream admitted `NonPayable_balance_zero` proof is completed in Lean by
  carrying the needed nonnegative-amount invariant through the induction.
- The upstream admitted DFS induction principle from `BlockchainBFS.v` is
  completed in Lean for permutation-free traces.
- Two upstream source bugs are intentionally corrected:
  `StringExtra.str_map` applies its function argument, and
  `StepNotPermute.snp_action_invalid` targets `step_action_invalid`.

## Layout

- `ConCert/Utils/` from `utils/theories/`
- `ConCert/Execution/` from `execution/theories/`
- `ConCert/Execution/Test/` from `execution/test/`
- `ConCert/Examples/Counter/` from `examples/counter/Counter.v`
- `ConCert/Examples/Escrow/` from `examples/escrow/Escrow.v` and
  `examples/escrow/EscrowCorrect.v`
- `ConCert/Examples/PiggyBank/` from `examples/piggybank/PiggyBank.v`

## Not Included

- `embedding/`, which depends on Rocq/MetaRocq syntax and metatheory.
- `extraction/`, which depends on MetaRocq's erased AST.
- Most examples from the parent repository.
- Full QuickChick generator, checker, notation, and printer parity.
- Exact Ltac script compatibility.
