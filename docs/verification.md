# Verification record

Verified locally on **2026-10-02**, on macOS arm64, using Lean `4.29.0-rc6` and mathlib revision `f156f7abd91ac67adb22bf999e5a71ba22e22e41`.

## Checks performed

| Check | Result |
| --- | --- |
| Original development build | Passed: 3,993 Lake jobs, with project and vendored proof modules compiled from source |
| Reviewed paper revision | Downloaded arXiv v1 TeX matches the original recorded SHA-256 |
| Numbered statement review | All 29 numbered proof statements, Definitions 1/14, and Example 24 mapped to actual definitions and endpoints |
| Final release build | Passed: 3,996 Lake jobs, including `Paper.Statements` and `Paper.Proofs` |
| Source scan | Passed: 455 proof-source files; no proof placeholders or custom axioms outside the isolated Comparator challenge |
| Source integrity | All distributed vendor hashes match; all 177 project mathematical modules are byte-for-byte unchanged from the supplied sources |
| Import closure | All 449 original local build modules remain reachable; no mathematical dependency was lost during pruning |
| Full transitive axiom audit | Passed: 451 imported project/vendor/interface modules, 9,643 theorems, and 2,148 safe definitions |
| Permitted axiom union | Exactly `propext`, `Quot.sound`, and `Classical.choice` |
| Appendix B dependency audit | All eight required constructive dependencies present; twelve main-route endpoints/helpers absent |
| Official Comparator | Passed for all 54 contracts; Lean's default kernel accepted the exported solution |
| Packaging checks | English text, portable paths, local documentation links, shell syntax, citation YAML, and CI YAML checked |

Builds emit inherited linter warnings; no build errors remain. The first attempted build exposed an invalid serialized dependency name in the supplied lockfile. The package name is now correctly escaped as a Lean name; dependency revisions were not changed.

## Paper and semantic review

The paper source is [arXiv:2609.30762v1](https://arxiv.org/abs/2609.30762v1). Its `stein-full.tex` SHA-256 is:

```text
233c18bcc51a9f7601296b8485876df49c936c9f1416cca7032dea20687824a0
```

The review checked each numbered result's assumptions, quantifier placement, parameter ranges, conclusions, and underlying definitions. Particular attention was given to F1–F3 versus F4–F5, actual correlated channel families, tester/alternative optimization order, support-sensitive extended entropy, finite-to-real conversions, full diamond norm, exact trace preservation, and uniformity of finite-block constants.

No substantive endpoint mismatch was found within that review. Some formal results are stronger or use different proof routes; these are documented in [paper correspondence](paper-correspondence.md). This is a source and endpoint review, not an assertion that every informal proof line has a separate formal counterpart or that independent external human peer review has occurred.

## Reproduce

```sh
lake exe cache get
bash scripts/check.sh
bash scripts/check_comparator.sh --local
```

For lower memory use, the build driver also accepts `--serial`. It builds the 451 local proof/interface modules in dependency order before running the same audits. The default build and the module-order inventory were checked locally; the complete serial loop was not rerun for this release.

`check_sources.py` verifies vendor integrity, excludes the challenge from proof dependencies, checks the complete 54-target interface, and verifies that all project modules are reachable. `audit_axioms.lean` obtains declarations from Lean's compiled module environment, including private declarations and declarations outside the project namespace. It checks every theorem and safe definition in the project and its selected vendored sources. Compiler-generated unsafe runtime implementations are not mathematical roots. The audit traverses transitive dependencies and rejects any nonstandard axiom.

`audit_appendix.lean` checks the actual transitive proof dependencies of the Appendix B endpoint. It requires the completion/tensor/near-subadditivity construction and rejects the twelve listed main asymptotic endpoints and helpers.

## Environment and verification boundary

- Exact-version third-party package caches were reused, after checking all nine Git revisions against the lockfile. The initial project and vendored proof builds started without local compiled objects. The cleaned sources and added interfaces were then rebuilt and audited with Lake.
- Comparator and its exporter use the separately pinned revisions in `comparator/lake-manifest.json`. Its macOS `--local` mode performs statement comparison, axiom checking, and Lean kernel replay without an OS sandbox. Nanoda was not enabled.
- Linux Landrun isolation and GitHub-hosted CI were not run on this macOS host. The supplied CI uses the trusted-source local Comparator mode.
- On this host, Apple's installed Command Line Tools were selected for the build process with `export DEVELOPER_DIR=/Library/Developer/CommandLineTools`. No system-wide developer-directory or license setting was changed.
- Compiled objects and downloaded packages remain local caches under `.lake/`; Git and release packaging exclude them. The release ZIP is checked for integrity, byte equality, and source-check success after extraction. It contains no raw historical build logs or older verification certificates.

## Release recheck on 2026-10-04

The standard Lake build, source checks, and transitive axiom audit were rerun
successfully in a separate local workspace, using the pinned toolchain and
previously compiled caches. Comparator passed all 54 obligations and Lean
kernel replay in macOS development mode without process sandboxing.

All Lean source files are byte-for-byte unchanged from the 2 October source
distribution. Release edits are limited to packaging exclusions, documentation,
and CI version references. Source checks, archive integrity, script syntax,
configuration formats, and local documentation links were checked again.
The separate Appendix B dependency audit also passed again.
