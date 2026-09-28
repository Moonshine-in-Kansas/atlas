# Per-entry Comparator results

These checks concern the [existence contracts](Challenge.lean): a single finite
group witness with the stated order, simplicity and commutativity/noncommutativity.
They do not establish recognition or uniqueness of isomorphism types.

- [Reference statements](Challenge.lean): what must be proved, using only mathlib.
- [Solution file](Solution.lean): the ATLAS imports, chosen groups and existing proofs supplying the witnesses.
- [How to reproduce the checks](README.md#running-the-sequential-queue): setup, scripts and sandbox command.

For each passed entry, the last column links its actual individual reference and
solution files. Those solution files use only the imports needed for that entry.
Each passed entry records a real sandboxed Comparator run, statement comparison,
permitted-axiom checking and standard Lean kernel replay. This is not a new Nanoda
run. All runs use the pinned tools in [the reproduction guide](../INDEPENDENT_CHECKERS.md).

Updated 2026-09-28T17:13:00Z. **18 / 23 passed.**

| Entry | Result | Elapsed | Peak combined worker RSS | Lean files |
|---|---|---:|---:|---|
| [cyclic](2026-09-29/cyclic/RESULT.json) | Passed | 28 s | 3.23 GiB | [Reference](2026-09-29/cyclic/Challenge.lean) · [Solution](2026-09-29/cyclic/Solution.lean) |
| [alternating](2026-09-29/alternating/RESULT.json) | Passed | 36 s | 3.98 GiB | [Reference](2026-09-29/alternating/Challenge.lean) · [Solution](2026-09-29/alternating/Solution.lean) |
| [typeA](2026-09-29/typeA/RESULT.json) | Passed | 67 s | 4.62 GiB | [Reference](2026-09-29/typeA/Challenge.lean) · [Solution](2026-09-29/typeA/Solution.lean) |
| [typeB](2026-09-29/typeB/RESULT.json) | Passed | 99 s | 5.37 GiB | [Reference](2026-09-29/typeB/Challenge.lean) · [Solution](2026-09-29/typeB/Solution.lean) |
| [typeC](2026-09-29/typeC/RESULT.json) | Passed | 64 s | 4.17 GiB | [Reference](2026-09-29/typeC/Challenge.lean) · [Solution](2026-09-29/typeC/Solution.lean) |
| [typeD](2026-09-29/typeD/RESULT.json) | Passed | 75 s | 4.61 GiB | [Reference](2026-09-29/typeD/Challenge.lean) · [Solution](2026-09-29/typeD/Solution.lean) |
| [G2](2026-09-29/G2/RESULT.json) | Passed | 64 s | 4.91 GiB | [Reference](2026-09-29/G2/Challenge.lean) · [Solution](2026-09-29/G2/Solution.lean) |
| [ReeG2](2026-09-29/ReeG2/RESULT.json) | Passed | 87 s | 5.17 GiB | [Reference](2026-09-29/ReeG2/Challenge.lean) · [Solution](2026-09-29/ReeG2/Solution.lean) |
| [M11](2026-09-29/M11/RESULT.json) | Passed | 61 s | 4.56 GiB | [Reference](2026-09-29/M11/Challenge.lean) · [Solution](2026-09-29/M11/Solution.lean) |
| [M12](2026-09-29/M12/RESULT.json) | Passed | 60 s | 4.60 GiB | [Reference](2026-09-29/M12/Challenge.lean) · [Solution](2026-09-29/M12/Solution.lean) |
| [M22](2026-09-29/M22/RESULT.json) | Passed | 62 s | 4.51 GiB | [Reference](2026-09-29/M22/Challenge.lean) · [Solution](2026-09-29/M22/Solution.lean) |
| [M23](2026-09-29/M23/RESULT.json) | Passed | 57 s | 4.46 GiB | [Reference](2026-09-29/M23/Challenge.lean) · [Solution](2026-09-29/M23/Solution.lean) |
| [M24](2026-09-29/M24/RESULT.json) | Passed | 56 s | 5.19 GiB | [Reference](2026-09-29/M24/Challenge.lean) · [Solution](2026-09-29/M24/Solution.lean) |
| [Co1](2026-09-29/Co1/RESULT.json) | Passed | 129 s | 4.65 GiB | [Reference](2026-09-29/Co1/Challenge.lean) · [Solution](2026-09-29/Co1/Solution.lean) |
| [Co2](2026-09-29/Co2/RESULT.json) | Passed | 147 s | 5.02 GiB | [Reference](2026-09-29/Co2/Challenge.lean) · [Solution](2026-09-29/Co2/Solution.lean) |
| [Co3](2026-09-29/Co3/RESULT.json) | Passed | 139 s | 5.27 GiB | [Reference](2026-09-29/Co3/Challenge.lean) · [Solution](2026-09-29/Co3/Solution.lean) |
| [McL](2026-09-29/McL/RESULT.json) | Passed | 139 s | 5.36 GiB | [Reference](2026-09-29/McL/Challenge.lean) · [Solution](2026-09-29/McL/Solution.lean) |
| [HS](2026-09-29/HS/RESULT.json) | Passed | 131 s | 4.98 GiB | [Reference](2026-09-29/HS/Challenge.lean) · [Solution](2026-09-29/HS/Solution.lean) |
| Suz | Pending | — | — | [Reference](Challenge.lean) · [Solution](Solution.lean) |
| J2 | Pending | — | — | [Reference](Challenge.lean) · [Solution](Solution.lean) |
| Fi22 | Pending | — | — | [Reference](Challenge.lean) · [Solution](Solution.lean) |
| Fi23 | Pending | — | — | [Reference](Challenge.lean) · [Solution](Solution.lean) |
| Fi24Prime | Pending | — | — | [Reference](Challenge.lean) · [Solution](Solution.lean) |

Passed entries include their actual Challenge and Solution modules, configuration,
unaltered result record, GNU time output and complete compressed Comparator log.
The shared source snapshot covers the release mathematics and pins. Per-run hashes
of runtime Lake setup files are retained in RESULT.json; those machine-local setup
files are recreated by the preparation script and are not bundled. The result
records are execution evidence, not cryptographically signed attestations.
