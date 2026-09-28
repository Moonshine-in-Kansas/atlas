# Per-entry Comparator results

These checks concern the [existence contracts](Challenge.lean): a single finite
group witness with the stated order, simplicity and commutativity/noncommutativity.
They do not establish recognition or uniqueness of isomorphism types.
Each passed entry records a real sandboxed Comparator run, statement comparison,
permitted-axiom checking and standard Lean kernel replay. This is not a new Nanoda
run. All runs use the pinned tools in [the reproduction guide](../INDEPENDENT_CHECKERS.md).

Updated 2026-09-28T16:50:22Z. **13 / 23 passed.**

| Entry | Result | Elapsed | Peak combined worker RSS |
|---|---|---:|---:|
| [cyclic](2026-09-29/cyclic/RESULT.json) | Passed | 28 s | 3.23 GiB |
| [alternating](2026-09-29/alternating/RESULT.json) | Passed | 36 s | 3.98 GiB |
| [typeA](2026-09-29/typeA/RESULT.json) | Passed | 67 s | 4.62 GiB |
| [typeB](2026-09-29/typeB/RESULT.json) | Passed | 99 s | 5.37 GiB |
| [typeC](2026-09-29/typeC/RESULT.json) | Passed | 64 s | 4.17 GiB |
| [typeD](2026-09-29/typeD/RESULT.json) | Passed | 75 s | 4.61 GiB |
| [G2](2026-09-29/G2/RESULT.json) | Passed | 64 s | 4.91 GiB |
| [ReeG2](2026-09-29/ReeG2/RESULT.json) | Passed | 87 s | 5.17 GiB |
| [M11](2026-09-29/M11/RESULT.json) | Passed | 61 s | 4.56 GiB |
| [M12](2026-09-29/M12/RESULT.json) | Passed | 60 s | 4.60 GiB |
| [M22](2026-09-29/M22/RESULT.json) | Passed | 62 s | 4.51 GiB |
| [M23](2026-09-29/M23/RESULT.json) | Passed | 57 s | 4.46 GiB |
| [M24](2026-09-29/M24/RESULT.json) | Passed | 56 s | 5.19 GiB |
| Co1 | Pending | — | — |
| Co2 | Pending | — | — |
| Co3 | Pending | — | — |
| McL | Pending | — | — |
| HS | Pending | — | — |
| Suz | Pending | — | — |
| J2 | Pending | — | — |
| Fi22 | Pending | — | — |
| Fi23 | Pending | — | — |
| Fi24Prime | Pending | — | — |

Passed entries include their actual Challenge and Solution modules, configuration,
unaltered result record, GNU time output and complete compressed Comparator log.
The shared source snapshot covers the release mathematics and pins. Per-run hashes
of runtime Lake setup files are retained in RESULT.json; those machine-local setup
files are recreated by the preparation script and are not bundled. The result
records are execution evidence, not cryptographically signed attestations.

The earlier combined attempt stopped at a memory reserve and is not counted as a
pass. A successful single-target check covers that target and its required proof
dependencies; it does not replace every older structural/catalogue audit target.
