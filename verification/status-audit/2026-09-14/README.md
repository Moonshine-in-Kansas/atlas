# Reproducible ATLAS status audit

Start with STATUS.md and NOTE_SUMMARY.md. GROUPS.csv records completed and missing entries; AUXILIARY_GROUPS.csv keeps full groups and covers separate. PROPERTIES.csv includes exact compiled public signatures, not just links or expected statements. Aliases and checks are included for coverage but are not independent mathematical achievements.

The proof snapshot is **9cf371923c57ce7c83c87ded71521b2e57560236**, branch **master**, in `/home/gerald/atlas`. SNAPSHOT.json records the UTC time, dependency revisions, dirty owner files and hashes of every current Atlas source file. That proof snapshot remains the reference even if this audit is committed later. Existing untracked drafts are preserved and not silently attributed to HEAD.

## Reproduce

From this same pinned checkout, run:

```sh
cd /home/gerald/atlas
bash verification/status-audit/2026-09-14/reproduce.sh
```

This verifies the mathematical source snapshot, runs the default current Lake build and the seven extraction/mapping drivers, recomputes declaration closures and line unions with Ruby, regenerates numerical reports and inventories, and validates the results. It does not use Python or alter proofs/pins. It overwrites generated files **inside this audit directory only**. For a later mathematical snapshot, use a new dated directory and snapshot rather than attributing changed proofs to this certificate.

The principal individual checking commands are:

```sh
/home/gerald/.elan/bin/lake build
/home/gerald/.elan/bin/lake env lean verification/status-audit/2026-09-14/Extract.lean
/home/gerald/.elan/bin/lake env lean verification/status-audit/2026-09-14/Extra.lean
/home/gerald/.elan/bin/lake env lean verification/status-audit/2026-09-14/Auxiliary.lean
ruby verification/status-audit/2026-09-14/validate.rb
```

The extraction drivers write their node streams inside this directory; reproduce.sh also captures their printed output. Definitions.lean prints model dependencies and foundations; Evidence.lean prints the small concrete example and imported-module inventory. Ranges.lean resolves the compiler module of each inherited source-range parent. The range-parent correction is essential: a generated equation lemma may be compiled in a later module than its underlying source definition.

## Evidence and limitations

THEOREM_STATEMENTS.txt combines actual compiler outputs. Proof bodies are suppressed; project definitions and the inherited foundations are printed. EXAMPLE.txt is a smaller exact concrete extract. AXIOMS.txt contains actual per-root axiom reports. DEPENDENCIES.json records the full graph with type/value edge labels; nodes retain both defining module and recovered source module. TRUST.json and VALIDATION.txt record checks, including the reviewed classical-theorem name-search hits.

SOURCE_SIZE.csv and CODE_COUNTS.csv use different metrics; see METRICS.md. SOURCE_COVERAGE.csv is based on the compiled module inventory. Missing external source spans do not remove nodes from the dependency graph. All Atlas principal spans are recoverable. No provenance-based handwritten/generated split is claimed. The 18 entries are catalogue entries, not mutually disjoint isomorphism classes: low-rank family coincidences remain possible.

This is a current incremental build plus fresh compiled-declaration audit. Loading imported proof terms is not the same as independently kernel-rechecking each term or rebuilding mathlib from scratch. Historical comparator and extension reports were inspected as discovery evidence but not all rerun. No claim of verified kernel/software/hardware implementation is made.

MANIFEST.sha256 binds the final delivered artifacts. Reproduction can change build-log messages and times; mathematical counts, statement coverage, source hashes, and dependency closure are the relevant reproducibility checks. Large raw outputs are retained locally and can also be stored compressed without changing their meaning.

For economical local Git preservation, files over one megabyte have deterministic `.gz` copies; the uncompressed files remain present in this workspace. After obtaining a Git-only copy, restore them inside the audit directory with:

```sh
for file in verification/status-audit/2026-09-14/*.gz; do gzip -dk "$file"; done
```

A complete reproduction generates the raw evidence directly. After validation, `ruby verification/status-audit/2026-09-14/package.rb` refreshes compressed copies and the artifact manifest. No original mathematical file is compressed, deleted, or changed.
