# Comparator replay — 25 October 2026

**42 of 45 targets passed.** The serial queue contains 44 harnesses:

- 38 of 39 model-specific existence targets passed: all nine Chevalley models and 29 of the 30 earlier models.
- All four strengthened involution/Sylow-center targets passed.
- The Albert-model F₄ target and the two aggregate actual-model comparison targets stopped at the 9 GiB owned RSS-plus-swap cap. These are incomplete checks, not passes or proof rejections.

[Original queue result](RESULT.json) · [Proof-source hashes](SOURCE_HASHES.json) ·
[Reference-source hashes](REFERENCE_SOURCE_HASHES.json) · [Publication file hashes](BUNDLE.json)

Each harness directory preserves its exact Reference/Challenge, Solution, Comparator configuration,
pinned Lake inputs, original `RESULT.json`, monitor receipt and timing. Complete logs are gzip-compressed;
their decompressed SHA256 values equal the original `stage.log_sha256` records. No original receipt
or historical success record was edited. Deliberate proof holes occur only in reference specifications.

Every pass has exit code zero, statement/axiom comparison, standard Lean-kernel replay and Comparator's
final accepted-solution verdict (including its quotient post-check). Comparator is not a separate kernel
implementation; this bundle makes no new Nanoda claim. The 43 existence/discriminator references use
Mathlib-only imports. The two aggregate references share the explicit concrete-model registry and
normalization definitions with their solutions.

These runs checked the local principal snapshot `95c13b57b188b350503fe3a5d6aace5f0a79047b` and the exact working-tree
hashes above. That local development history differs from the filtered GitHub history. The snapshot
includes unfinished sources outside this export, so publishing these records does not claim a fresh
build or replay of the entire GitHub tree. The actual contract files are checked against the published
references; all 4,974 recorded proof-source/pin hashes still matched when this bundle was prepared.
The `reference-source-snapshot/` directory retains all 48 reference/configuration source files as they
were during the run, including the registry metadata before its replay-status update.

Tool revisions and binary hashes, original absolute harness paths, resource bounds and timings remain
in `RESULT.json`. The archived `driver.rb` and `monitor.rb` are provenance, not relocated entry points.
Use [the contract guide](../README.md) and [Chevalley reproduction instructions](../chevalley/README.md)
to prepare fresh harnesses; preserve the original records when repeating checks.

Historical 13 October passes remain at their original paths. In particular, the earlier Albert-model
F₄ pass is preserved but is not substituted for its incomplete 25 October attempt.
