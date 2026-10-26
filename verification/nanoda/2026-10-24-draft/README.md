# Independent Nanoda check — 24 October 2026

**Kernel check passed: 139,617 declarations, with zero typechecker errors.**
The checker exited successfully. A separate pretty-printer warning prevented the
wrapper's narrower success-string test from accepting the run; its original
`incomplete` receipt is preserved, alongside the reviewed kernel result.

[Kernel result](KERNEL_RESULT.json) · [Exact checker output](nanoda.log) ·
[Process receipt](nanoda.json) · [Original wrapper receipt](RESULT.json) ·
[Scope and exclusions](SCOPE.json) · [File hashes](BUNDLE.json)

The checked local snapshot contains all 59,500 ATLAS theorems and 9,883 other
kernel declarations from 4,957 built modules: 69,383 roots and their full proof/type
dependencies. Every module in the 4,934-module `import Atlas` closure is covered.
The [14 excluded draft modules](COVERAGE_GAPS.json) are outside that closure and
are not certified. Exactly [45 compiler-generated partial implementations](EXCLUDED_IMPLEMENTATIONS.json)
ending in `._unsafe_rec` were removed from the export; none is a theorem.
The mathematical declarations and proof terms were retained unchanged.
The [root inventory](inventory.jsonl.gz), [coverage report](EXPORT_COVERAGE.json)
and exact filtering script record this boundary.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted. The configuration
rejects unpermitted axioms; it does not skip all axioms or permit arbitrary ones.
Nanoda revision `4c544ed4099c8227f07d5de77ad1e69fb0740a27` checks every declaration before
pretty-printing in [the retained source](reporting-source/src/main.rs).
`print_axioms` was enabled without an output destination. The log explicitly reports
no typechecker errors and one `Unable to print axioms` reporting error. The
[review script](record-kernel-result.rb) checked the output, configuration, axioms,
export coverage and hashes before recording `KERNEL_RESULT.json`.

This run finished on 24 October at 16:10:14 UTC, with one checker thread and about
8.26 GiB peak owned RSS plus swap under its 9 GiB cap. It is distinct from earlier
memory-stopped retries and from the [25 October Comparator contracts](../../existence/RESULTS.md).

The [4,974 source/pin hashes](SOURCE_HASHES.json) identify the local working snapshot
at principal commit `95c13b57b188b350503fe3a5d6aace5f0a79047b`. Local and filtered GitHub
histories differ; this is not a new full-export replay or proof of unfinished
mathematical claims. All recorded sources and both original/filtered proof-export
hashes were rechecked when this bundle was prepared. The multi-gigabyte proof exports
remain local; their hashes are preserved in the receipts. The original build log is
losslessly compressed as `source-attempt/build.log.gz`; its uncompressed hash is
recorded in `BUNDLE.json` and the original build receipt. This publication performs
no new Nanoda run. Earlier records keep their original dates and results.

The scripts and absolute paths are exact run provenance. For fresh verification,
use [the independent-checker guide](../../INDEPENDENT_CHECKERS.md), retaining the
stated scope and any exclusions rather than silently treating drafts as passed.
