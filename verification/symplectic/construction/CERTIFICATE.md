# Final symplectic construction certificate

**Complete: JOB_SYMPLECTIC_FAMILY.md, C0–C6.**

The primary models are the actual mathlib symplectic matrix carrier and its quotient
by its center. Uniform matrix/projective orders, scalar center, generation, natural
actions, all perfectness branches, positive simplicity, exact nonsimplicity exceptions,
noncommutativity, structural comparisons and actual prime-power existence are proved.
No target group or desired order/simplicity is supplied as an extra hypothesis.

Mathematical source commit: f07f142 (full hash in the bound structure snapshot).
Pinned Lean v4.34.0-rc2 and mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0 are unchanged.
[The completion report](../../../SYMPLECTIC_COMPLETION.md) explains the mathematics.

The independently sealed runs in RUNS.json pass:
- Order: 57 roots/20488 nodes, independent generation/simplicity boundary and stricter center boundary.
- Positive simplicity: 108 roots/26470 nodes, with separate generation/geometry/perfectness gates.
- Exceptions: 65 roots/29823 nodes, actual normal subgroup of order 360 and exact full-range theorem.
- Structural/public package: 331 roots/32030 nodes, including all required regressions.

The normal root and aggregate audit build pass 5259 jobs. Only propext,
Classical.choice and Quot.sound occur. source-scan.log and policy-tests.log record
zero forbidden source markers and successful positive/eight-negative policy checks.
No new independent Comparator run is claimed.

Earlier coverage is preserved: principal-constructions/20260914T065411-646 passes
36 roots/61270 nodes with exactly matching historical names, modules, kinds and all
statement/proof dependency edges. Its snapshot also binds the additive root imports.
All earlier catalogue entries, auxiliary scopes, historical evidence records and
pre-existing mathematical proof files/pins are preserved; see preservation.log.

Catalogue refresh and final check pass 634 references, with four completed families,
fifteen completed sporadics, 26 planned entries and ten auxiliary groups. The current
check is verification/runs/catalogue/20260914T070326-8. All fourteen negative catalogue
tests pass, including the retained seven original tests and new parameter, exception,
role, missing-entry and root-extension/evidence corruption tests.

MANIFEST.sha256 binds the separate run references, maintained inventory and verbatim
compiled statement extraction. The loader checks actual source hashes and policies
rather than treating these descriptions as proof. No old audit graph or dependency
pin was changed. FINAL_SHA256SUMS also binds this final report and checking logs.

No required mathematical obligation remains. The optional PSp→PSL adapter and larger
classical-group interfaces were not undertaken. Work remains in the existing master
checkout, with local commits only and unrelated owner drafts retained.
