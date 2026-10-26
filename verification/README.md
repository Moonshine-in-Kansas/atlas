# Verification

Begin with [the audit summary](../AUDIT.md), [compiled principal statements](../THEOREM_STATEMENTS.md),
[independent-checker reproduction](INDEPENDENT_CHECKERS.md) and
[release maintenance](MAINTENANCE.md).

The [26 October audit](2026-10-26-cache-audit/RESULT.json) freshly elaborated both
root imports and inspected all 1,207 selected declarations and 99,886 complete
type/proof dependency nodes using a source-bound, unchanged cache. It is not a
fresh whole-project rebuild or independent replay.

The dated [24 October Nanoda](nanoda/2026-10-24-draft/README.md) and
[25 October Comparator](existence/RESULTS.md) records retain their exact scopes.
They do not automatically certify a different filtered export.
Recorded full audits include all type, instance and proof dependencies;
declaration-only inspection is identified separately.

The [registry](../catalogue/catalogue.json) and
[realization data](../catalogue/realizations.json) link the relevant construction
and property evidence. Large text artifacts are compressed according to
[this index](compressed-evidence.json), with their original hashes preserved.

## Reading the evidence archive

The dated directories preserve the exact certificates, compiled statements,
dependency graphs and reproduction inputs behind the results. Their historical
counts describe their own snapshots; use the current catalogue and audit summary
above for the present inventory. Two original links refer to omitted development
documents: use the [symplectic catalogue entry](../CATALOGUE.md#family-c) for
`SYMPLECTIC_COMPLETION.md`, and the [current checker guide](INDEPENDENT_CHECKERS.md)
for the old `existence/chevalley/README.md` link. The sealed originals remain unchanged.

Most of the repository's size is compressed dependency evidence. Repeated inputs
keep individual checker bundles self-contained and preserve their recorded hashes;
Git stores identical file contents once. Lean sources, verification evidence,
proof diagrams, mathematical documentation and build/licensing metadata are retained.
Construction-job notes, local build caches and temporary compilation files are excluded.
