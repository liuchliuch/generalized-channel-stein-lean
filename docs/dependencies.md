# Dependencies and provenance

The toolchain is `leanprover/lean4:v4.29.0-rc6`. The root `lake-manifest.json` locks all downloaded dependencies. Vendored dependencies use relative paths and contain source, licenses, notices, and integrity manifests. No external workspace path or prebuilt proof object is required.

## mathlib

- Source: [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)
- Revision: `f156f7abd91ac67adb22bf999e5a71ba22e22e41`
- License: Apache-2.0

All packages use this same revision. The official mathlib cache may be used for its dependencies; local proof sources are compiled by Lake.

## Earlier channel-Stein formalization

- Directory: `vendor/first-paper/`
- Paper: [Quantum Channel Stein's Lemma with an Exponential Strong Converse](https://arxiv.org/abs/2609.27196v1)
- Recorded checkpoint: `7f67d3ea4e6f2edd595f9c1f356da2fcc9124c4d`
- Distributed closure: 185 mathematical modules and one umbrella import

The checkpoint is provenance supplied with the original source snapshot. This repository does not claim to reconstruct or independently authenticate its Git history. The retained modules are exactly those imported by the generalized-channel development. Unused modules and historical documentation/scripts are omitted; the umbrella import is adjusted to the subset.

Retained mathematical tokens are unchanged. Three comments are updated to describe the current bridge and point license references to `LICENSE`. `UPSTREAM_SHA256` preserves original supplied hashes, including omitted sources; `SOURCE_SHA256` records the distributed sources. The source checker verifies the latter.

The adapted `SimultaneousDiagonalization` and `TraceNorm` modules retain their Physlib copyright headers. Other reused foundations include actual CPTP matrix-map semantics, CP order, Stinespring dilation, trace and diamond norms, reference reduction, support-aware entropy, testing optimization, and the ordinary state-Stein bridge. These are reused results, not new generalized-family theorem counts.

## Quantum

- Source: [Hayata-Yamasaki-Group/lean-quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum)
- Revision: `bf1c4f6aaec84948f1a1c76c0728432813404a0f`
- Directory: `vendor/first-paper/vendor/lean-quantum/`
- Distributed closure: 19 mathematical modules and one umbrella import

This supplies spectral inequalities and sandwiched Rényi foundations. Four Japanese comments are translated into English; retained mathematical tokens are unchanged. Packaging pins mathlib and omits the unused `checkdecls` dependency. Original and distributed hashes are in `UPSTREAM_SHA256` and `SOURCE_SHA256`.

## Physlib state-Stein port

- Source: [leanprover-community/physlib](https://github.com/leanprover-community/physlib)
- Revision: `f6e446ca99fd83b3a60743a61900cb2acb98f531`
- Directory: `vendor/first-paper/vendor/physlib-state/`
- Distributed closure: 60 upstream modules and seven bridge modules

The supplied port adapts the source to this project's Lean/mathlib versions using import relocations, API and coercion adjustments, explicit simplifications, and finite-dimensional positivity/coordinate proof changes. The present cleanup leaves all retained port proofs unchanged. The original port covered 68 upstream modules; eight unused modules and the obsolete audit driver are omitted here.

The bridge modules are `SingletonTheory`, `SingletonSteinBridge`, `TupleCoherence`, `TupleStates`, `OrdinaryStateStein`, `KernelFilledAlternative`, and `StateSteinDirect`. They prove singleton state-Stein statements, tensor coherence, supported singular reduction, and literal eventual tests. Overlapping trace inequalities re-export Quantum; Sion minimax has a single implementation in this package.

`upstream-source-sha256.txt` records the original upstream inventory; `source-sha256.txt` records the distributed subset. Original author and license headers are retained. See each vendor's `LICENSE` and `NOTICE`; attribution does not imply endorsement.

## Comparator tools

These optional tools build under `.lake/comparator/` and are locked independently in `comparator/lake-manifest.json`.

| Tool | Revision |
| --- | --- |
| [Comparator](https://github.com/leanprover/comparator) | `066c3bc9e966ccad9a633d780ae4de13cd0f27b6` |
| [lean4export](https://github.com/leanprover/lean4export) | `048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d` |
| [Lean4Checker](https://github.com/leanprover/lean4checker) | `b7398199245524275543dec6113229c9bb4902e5` |

Their upstream licenses apply. The toolchain matches the proof library. See [Comparator instructions](comparator.md) for local and sandbox modes.
