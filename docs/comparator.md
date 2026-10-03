# Statement comparison

The repository uses the official [Lean Comparator](https://github.com/leanprover/comparator), pinned to a revision compatible with Lean 4.29.0-rc6.

## Reviewed specification and implementation

- `Paper/Statements.lean` defines the explicit propositions for the 29 numbered proof statements, Example 24, Appendix B, and key semantic bridges. Separate clauses give 54 comparison targets.
- `Paper/Challenge.lean` declares those targets with intentional `sorry` proofs, importing only the statement specification. It is an expected-statement environment, never a proof dependency.
- `Paper/Proofs.lean` declares the same target names with checked proofs from the implementation library.
- `comparator/config.json` lists every target and permits only `propext`, `Quot.sound`, and `Classical.choice`.

The statement file does not derive propositions from implementation theorem types. It imports five shared definition modules; the complete implementation root is imported separately by `Paper/Proofs.lean`. Shared definition modules also contain supporting proofs; the specification is a separate review surface, rather than a reimplementation of every mathematical foundation. Reviewers must inspect the meanings of the imported quantities as well as the displayed quantifiers.

Comparator compares target types and their recursively used declarations across the two exported environments. It also checks solution axiom dependencies and replays the exported solution in the Lean kernel. A pass establishes agreement with this specification; it does not establish that the specification faithfully translates the informal paper.

## Run locally

For a trusted checkout on macOS or Linux:

```sh
bash scripts/check_comparator.sh --local
```

The script builds the pinned Comparator and `lean4export` tools in `.lake/comparator/`, then runs comparison and kernel replay. The explicit `--local` option replaces the Linux Landrun invocation with an unsandboxed development runner. It provides the statement and proof checks, without OS isolation, and should only be used with trusted local sources.

## Run with the Linux sandbox

Install [Landrun](https://github.com/Zouuup/landrun) and put its executable in `PATH`, then run:

```sh
bash scripts/check_comparator.sh
```

This uses the sandbox invocation implemented by the pinned Comparator. For adversarial proof submissions, follow the [upstream security assumptions](https://github.com/leanprover/comparator/tree/066c3bc9e966ccad9a633d780ae4de13cd0f27b6), including a trusted specification and an uncompromised checking environment. The local release checks and CI operate on repository sources and do not claim adversarial-submission isolation.

## Update policy

Treat `Paper/Statements.lean` as the reviewed specification. Change it deliberately when the intended mathematical scope changes; do not regenerate it automatically from theorem implementations. Run both `bash scripts/check.sh` and Comparator after changing statements, definitions, or proofs.

Tool revisions are locked independently of the main proof dependencies in `comparator/lake-manifest.json`. The script copies the repository's toolchain into the build directory, so exports and comparison use the same Lean version as the proofs.
