# A Generalized Stein Lemma for Quantum Channels in Lean

A Lean 4 formalization of *A Generalized Stein Lemma for Quantum Channels* by Minbo Gao, Zhengfeng Ji, and Chenghua Liu ([arXiv:2609.30762v1](https://arxiv.org/abs/2609.30762v1)).

The development formalizes all **29 numbered proof statements**, the correlated-family construction in Example 24, and the independent Appendix B limit argument. It proves the generalized Stein identity under F1–F3, exponential channel approximation, exact trace-preserving smoothing, the operational threshold and strong converse, perturbation stability, and finite-block completion under F1–F5. Resource-family applications and exact isometric benchmarks are included.

## Build and verify

Install [Lean via elan](https://lean-lang.org/install/) and Python 3, then run from the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

Lean is pinned to **4.29.0-rc6**. The exact mathlib revision and transitive dependencies are locked in `lake-manifest.json`. Source dependencies in `vendor/` are included; downloaded package caches and compiled objects are excluded from the release.

The check validates sources and vendored hashes, builds the complete library and paper interface, audits transitive axioms of every imported project and vendored theorem and safe definition, and checks the independent Appendix B proof dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. On machines with limited memory, use `bash scripts/check.sh --serial`.

See [verification](docs/verification.md) for checks actually run on this release.

## Review the mathematical statements

Start with [Paper/Statements.lean](Paper/Statements.lean): 54 explicit propositions expose the assumptions, quantifier order, and conclusions separately from their proofs. The [paper correspondence](docs/paper-correspondence.md) maps all numbered results, explains the underlying definitions, and records strengthened conclusions and alternative proof routes. [Paper/Proofs.lean](Paper/Proofs.lean) connects the specification to the implementation.

[Lean Comparator](https://github.com/leanprover/comparator) compares the specification and proof environments, checks allowed axioms, and replays the proofs in the Lean kernel:

```sh
# Trusted local sources, including macOS; no OS sandbox.
bash scripts/check_comparator.sh --local

# Linux with Landrun installed.
bash scripts/check_comparator.sh
```

The intentional proof holes in `Paper/Challenge.lean` belong only to the expected-statement specification. They are excluded from the default build and never imported by the proof library. Shared definition modules also contain supporting proofs; reviewing the intended mathematics includes inspecting those definitions. Comparator checks agreement with the specification; correspondence with the informal paper is a separate review. See [Comparator setup](docs/comparator.md).

## Repository layout

| Path | Contents |
| --- | --- |
| `GeneralizedChannelStein/` | All 177 mathematical source modules |
| `GeneralizedChannelStein.lean` | Public import of the complete development |
| `Paper/` | Explicit statements, proof interface, and Comparator challenge |
| `comparator/` | Pinned checking-tool configuration |
| `scripts/` | Source, build, axiom, and Appendix B checks |
| `docs/` | Paper correspondence, verification, and dependency provenance |
| `vendor/` | Required source closure of the earlier channel-Stein library and its dependencies |
| `.github/workflows/` | Continuous integration |

## Mathematical conventions

Channels are actual finite complex matrix maps, with a proved equivalence to normalized finite Kraus representations. Tests allow arbitrary finite references and mixed inputs; one tester is chosen before the worst-case alternative. Family relative entropy takes the infimum over alternatives after the stabilized input supremum. Support failure gives infinite Umegaki entropy.

Information quantities use base-two logarithms. The diamond norm is the full, unhalved completely bounded trace norm. Smoothing optimizes over exactly trace-preserving channels. Choi matrices are input-first and unnormalized. Positive physical dimensions and positive blocklengths are explicit; the unused zero-block family is unconstrained.

## Citation and license

Please cite the [paper](https://arxiv.org/abs/2609.30762v1) when using this formalization; metadata is in [CITATION.cff](CITATION.cff).

The source is released under the [Apache License 2.0](LICENSE). Reused code retains its original attribution and licenses; see [NOTICE](NOTICE) and [dependency provenance](docs/dependencies.md). The paper is linked rather than bundled and remains under its original arXiv license.
