# A constructive ATLAS of finite simple groups in Lean

**Version 1.2 review candidate — branch `v1.2-review`.** The public default remains the preserved
[Version 1.0](https://github.com/Moonshine-in-Kansas/atlas/releases/tag/v1.0)
until the owner has reviewed this candidate and the release requirements are met.
Uploading this review branch does not change `main`, publish a final v1.2 release
or deploy the website. The source-bound compiled audit
covers all 1,207 selected declarations; three Comparator targets remain open.
See [verification status](AUDIT.md).

ATLAS constructs explicit finite groups and proves their orders, simplicity and
structural properties. This candidate contains **16 completed families,
16 sporadic constructions and the Tits group**, with their full parameter ranges
and exceptions. The stable entry point is `import Atlas`.

Read the [catalogue](CATALOGUE.md), the
[construction and identification guide](catalogue/REALIZATIONS.md), and the
[research note (PDF)](atlas_research_note.pdf) ([TeX](atlas_research_note.tex)).
The guide distinguishes models of the same group, isomorphisms between families,
and the order or invariant certificates separating all other pairs in the
[comparison theorem's scope](COMPARISON.md#scope-and-definitions).
The research note is the unchanged, dated 25 October development account:
its broader local source inventory is distinguished from this filtered export.
It is not a claim that every local draft module is included or release-accepted.

A, B, C, D, F₄ and G₂ each retain both their original model and a Chevalley
root-operator model. The catalogue displays both constructions. A/B/C/D have
explicit audited equivalences with linked Lean proof definitions and compiled
types. The G₂ and F₄ comparisons retain their separately stated scopes.

This is a construction library, not a proof of classification exhaustiveness.
Equality of orders is not used as a substitute for an isomorphism. The typed
comparison theorem covers its stated 13 families and 17 individual groups;
the three E-series families have separate construction and simplicity results.

## Build and check

Install Lean's elan toolchain manager, Git and Ruby, then run:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build
ruby catalogue/manage.rb check
LEAN_NUM_THREADS=2 ruby verification/check.rb
```

Lean and all dependency revisions remain pinned. Run one build or audit driver
at a time. `verification/check.rb` builds the source and audits the selected
compiled statements and complete proof/type dependencies. Independent Nanoda
and Comparator replay are separate checks; see the
[reproduction guide](verification/INDEPENDENT_CHECKERS.md).

## Source guide

| Path | Contents |
|---|---|
| `Atlas/Families/`, `Atlas/LinearGroups/` | Family models, uniform orders, simplicity and transport |
| `Atlas/Sporadic/`, `Atlas/Mathieu/`, `Atlas/Conway/`, `Atlas/Fischer/` | Sporadic constructions and public interfaces |
| `Atlas/Codes/`, `Atlas/Lattices/`, `Atlas/Algebra/` | Codes, lattices and algebraic constructions |
| `Atlas/Comparisons/`, `Atlas/OrderArithmetic/` | Isomorphisms, nonisomorphisms and order arithmetic |
| `catalogue/` | Mathematical interfaces and proof-dependency measurements |
| `verification/` | Reproduction tools and dated verification records |

Partial Lean foundations for other groups remain explicitly outside the
completed catalogue. Construction-job documents and internal progress notes
are not part of this export.

## Citation and license

Author: Gerald Höhn. Please cite *A constructive ATLAS of finite simple groups in
Lean*, [arXiv:2609.35847](https://arxiv.org/abs/2609.35847).
See [CITATION.cff](CITATION.cff), the approved
[ATLAS Research and Attribution License 1.0](LICENSE) and
[licensing scope](LICENSING.md). Dependencies retain their own licenses.
