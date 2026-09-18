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

No CI, scheduled verification or website is configured. Verified source release: `v0.1.0`. See [AUDIT.md](AUDIT.md) for the recorded checks.

## Citation and license

Author: Gerald Höhn. See [CITATION.cff](CITATION.cff) and the existing
[Apache-2.0 license](LICENSE). Source headers preserve mathematical attribution.
No arXiv identifier has yet been assigned here.
