# Constructive ATLAS

Read the [**research note (PDF)**](atlas_research_note.pdf) — mathematical background, constructions and project overview.

A Lean library constructing explicit finite simple groups and proving their orders,
simplicity and structural properties. The selected scope comprises eight families
and fifteen sporadic entries; parameter restrictions and small exceptions are part
of the statements. This is not a proof of classification exhaustiveness (CFSG),
and does not claim constructions of the Monster or all remaining groups.

See [the catalogue](CATALOGUE.md) for actual models and theorem names, and
[the audit instructions](AUDIT.md) for verification scope and limitations.
The stable entry point is `import Atlas`; namespaces and source paths are preserved.
The small Ree family starts at q=27.

## Finding the mathematics

The [principal theorem statements](THEOREM_STATEMENTS.md) show the compiled order
and simplicity signatures, including implicit parameters and assumptions, without proofs.

| Directory | Contents |
|---|---|
| `Atlas/Families/` | Cyclic and alternating family interfaces |
| `Atlas/LinearGroups/` | Classical families, split G₂ and small Ree constructions |
| `Atlas/Sporadic/` | Public sporadic models and construction interfaces |
| `Atlas/Codes/`, `Atlas/Mathieu/` | Golay/hexacode infrastructure and Mathieu groups |
| `Atlas/Lattices/`, `Atlas/Conway/` | Lattice constructions and the Conway-related developments |
| `Atlas/Fischer/` | Fischer constructions and proofs |
| `Atlas/Comparisons/` | Proved isomorphisms and nonisomorphisms |
| Other `Atlas/` subject directories | Shared algebra, geometry and group-theoretic infrastructure |
| `catalogue/` | Machine-readable interfaces and measured proof-line counts |
| `verification/` | Checking tools and recorded verification evidence |

[Independent-checker reproduction](verification/INDEPENDENT_CHECKERS.md) explains
how to repeat the Nanoda and Comparator checks separately from the ordinary Lean build.

## Build


Install Lean's elan toolchain manager, Git and (for audit scripts) Ruby. Then:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build
LEAN_NUM_THREADS=2 ruby verification/check.rb
```

The toolchain and all dependency revisions are pinned in `lean-toolchain` and
`lake-manifest.json`. The first command obtains public mathlib dependency caches;
ATLAS source is compiled locally. The default targets are `Atlas` and `Atlas.Audit`.
Use one build/audit driver at a time. A fresh project build can take substantial time
and memory on a laptop; no full mathlib source rebuild is required.

No CI, scheduled verification or website is configured. See [AUDIT.md](AUDIT.md) for the current source-bound checks and [release maintenance](verification/MAINTENANCE.md) for the automatic metadata gate.

## Citation and license

Author: Gerald Höhn. See [CITATION.cff](CITATION.cff) and the existing
[ATLAS Research and Attribution License 1.0](LICENSE). Commercial use and AI training
require written permission; scholarly use requires attribution and citation.
Distributed derivative works must include the license and preserve its conditions.
No arXiv identifier has yet been assigned here.
