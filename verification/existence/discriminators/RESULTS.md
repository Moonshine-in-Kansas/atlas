# Same-order groups: strengthened existence checks

[Reference statements](Challenge.lean) · [Solution proofs and imports](Solution.lean) · [Reproduction instructions](README.md)

Each statement asserts finiteness, exact order, simplicity, noncommutativity and
the displayed invariant **for the same existentially quantified group**.
The reference depends only on mathlib and explicitly defines the conjugacy-class
count; it does not import ATLAS or prescribe a group construction.

| Contract | Additional invariant |
|---|---|
| Bₙ(q) | For odd q, k₂(G) = n |
| Cₙ(q) | For odd q, k₂(G) = floor(n/2) + 1 |
| A₈ ≅ A₃(2), order 20,160 | Every Sylow-2 subgroup has center of order 2 |
| A₂(4) = PSL₃(4), order 20,160 | Every Sylow-2 subgroup has center of order 4 |

Here k₂ counts conjugacy classes of elements of order exactly two, excluding the
identity. For odd q and n≥3, the B/C counts differ. For the order-20,160 pair,
Sylow conjugacy and invariance of center order under isomorphism distinguish the
two witnesses. These checks distinguish these same-order pairs; they do not
claim a general recognition or uniqueness theorem for every group of that order.
The B/C contracts retain their original all-characteristic admissible ranges,
with the additional class-count clause conditional on odd characteristic.

Updated 2026-09-28T23:09:10Z. **4 / 4 passed.**

| Entry | Result | Elapsed | Peak combined worker RSS | Lean files |
|---|---|---:|---:|---|
| [Bₙ(q)](2026-09-29/typeB/RESULT.json) | Passed | 107 s | 4.92 GiB | [Reference](2026-09-29/typeB/Challenge.lean) · [Solution](2026-09-29/typeB/Solution.lean) |
| [Cₙ(q)](2026-09-29/typeC/RESULT.json) | Passed | 74 s | 4.77 GiB | [Reference](2026-09-29/typeC/Challenge.lean) · [Solution](2026-09-29/typeC/Solution.lean) |
| [A₈ ≅ A₃(2)](2026-09-29/alternating8/RESULT.json) | Passed | 95 s | 5.19 GiB | [Reference](2026-09-29/alternating8/Challenge.lean) · [Solution](2026-09-29/alternating8/Solution.lean) |
| [A₂(4) = PSL₃(4)](2026-09-29/psl3Four/RESULT.json) | Passed | 73 s | 5.14 GiB | [Reference](2026-09-29/psl3Four/Challenge.lean) · [Solution](2026-09-29/psl3Four/Solution.lean) |

Each passed record includes statement comparison, allowed-axiom checking and
standard Lean kernel replay by the real sandboxed Comparator. This is not a
Nanoda run. The source snapshot, tool revisions, input hashes, complete compressed
log and time report accompany the result. Runtime Lake setup files are recreated
by the preparation script; their original hashes remain in RESULT.json.

The [original 23 existence checks](../RESULTS.md) are preserved separately and
are not retrospectively relabeled as having checked these stronger statements.
