# ConCertLean

Lean 4 port of ConCert's Rocq sources.

This repository is a starting point for proof porting: definitions and
executable behavior are ported where in scope, while theorem statements that
still need Lean proofs are represented as `axiom`. See [SCOPE.md](SCOPE.md) for
the current port boundaries and deliberate deviations from the Rocq project.

## Build

The Lean toolchain and mathlib revision are pinned to Lean 4.29.0.

```bash
lake build
```

## Layout

- `ConCert/Utils/` from `utils/theories/`
- `ConCert/Execution/` from `execution/theories/`
- `ConCert/Execution/Test/` from `execution/test/`
- `ConCert/Examples/` from `examples/`

Convention: axiomatized theorems live under namespace `ConCert.<...>` with the
original name. Run `#print axioms <thm>` to audit proof debt.
