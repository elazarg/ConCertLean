# ConCertLean

A Lean 4 port of [ConCert](https://github.com/AU-COBRA/ConCert)'s
executable smart-contract verification framework.

ConCertLean ports the executable framework, example contracts, local-chain test
support, and application-level proof developments from ConCert's Rocq sources
to Lean 4.

The port covers the main parts needed to run and verify the examples:
framework utilities, blockchain execution semantics, serialization, executable
contract models, generated-property tests, and correctness proofs for the
included example families. Those families include governance and voting, token
standards, escrow and payment flows, DeFi contracts, bug-witness examples, and
small executable examples.

The Lean tree builds with no `sorry`, `admit`, or project-specific axioms. See
[SCOPE.md](SCOPE.md) for exact module coverage, intentional source deviations,
upstream fixes, and the axiom footprint.

## How to build

The Lean toolchain and mathlib revision are pinned to Lean 4.29.0.

After cloning the repository, run:

```bash
lake build
lake test
```

`lake test` runs deterministic generated-property checks over serialization,
local-chain execution, executable example behavior, bug-witness traces,
expected-failure handling, proof symbols, and upstream-path wrappers.

## Structure of the project

The project keeps the source layout close to the retained parts of the Rocq
development.

The [ConCert/Utils](ConCert/Utils/) folder contains utility libraries ported
from `utils/theories`.

The [ConCert/Execution](ConCert/Execution/) folder contains the formalization of
the executable smart-contract execution layer, including chain state, actions,
blocks, builders, induction principles, serialization support, and local-chain
testing infrastructure.

The [ConCert/Execution/Test](ConCert/Execution/Test/) folder contains the
execution tests and generated-property support used by the Lean test suite.

The [ConCert/Examples](ConCert/Examples/) folder contains executable contracts,
tests, and proofs for the ported examples. It includes BAT, BoardroomVoting,
CIS1, Counter, Crowdfunding, Congress, Escrow, PiggyBank, StackInterpreter,
EIP20, iTokenBuggy, FA1.2, FA2, Dexter, Dexter2, and ExchangeBuggy.

The [SCOPE.md](SCOPE.md) file records the precise port boundary, retained
source-layout wrappers, proof coverage, out-of-scope subprojects, upstream fixes,
and axiom audit.

## Notes for developers

The project is a Lake package. `lake build` builds the library, and `lake test`
runs the generated executable tests.

The main library namespace is `ConCert`. Example modules live under
`ConCert.Examples.*`; framework modules live under `ConCert.Execution.*` and
`ConCert.Utils.*`.

## Documentation

The source files are the primary documentation for the Lean port. For exact
coverage and audit details, see [SCOPE.md](SCOPE.md).

For background on the original framework, see the upstream
[ConCert documentation](https://au-cobra.github.io/ConCert/toc.html).

## Papers

The ConCert papers describe the framework, execution model, property-based
testing, extraction work, and smart-contract case studies. See the
[Papers section](https://github.com/AU-COBRA/ConCert#papers) in the upstream
repository.

## Videos

A video collection presenting parts of ConCert is available on
[YouTube](https://www.youtube.com/playlist?list=PLWcJeGdOHpbxb_DhcfppHRrZKW7wPO9qQ).

## Projects using ConCert

See the upstream
[Projects using ConCert](https://github.com/AU-COBRA/ConCert#projects-using-concert)
section for related projects.
