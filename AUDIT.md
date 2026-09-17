# Verification of the source export

Status: isolated project-source build and all 911 selected declaration audits passed.
The dependency graph contains 70266 nodes; allowed axioms found: Classical.choice, Quot.sound, propext.
Recorded evidence is under `verification/release/`. The fresh source-build log is retained
separately from the audit runner's subsequent incremental build log.

The source selection is the compiler-resolved complete transitive module closure
of `Atlas` and `Atlas.Audit`. All 2,296 selected project modules and the pinned
build configuration are preserved byte-for-byte. Default `lake build` covers them.
The project uses Lean v4.34.0-rc2 and mathlib commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0`; all package pins are in lake-manifest.json.

`verification/roots.json` explicitly lists 911 catalogue and comparison references.
`verification/check.rb` builds the project, extracts elaborated signatures with all
implicit parameters visible and proof bodies suppressed, traverses type and proof
constant dependencies, and checks the allowed axiom list. Model definitions remain
in their canonical source modules. Read their hypotheses together with the theorem
statements: an axiom list by itself is insufficient evidence of mathematical scope.

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build
LEAN_NUM_THREADS=2 ruby verification/check.rb
```

The audit writes `verification/results/RESULT.json`, full statements, a transitive
dependency graph, source hashes and compressed logs. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Placeholders and native-reduction
trust axioms are rejected transitively. The Ruby scripts orchestrate extraction and
policy checks; the mathematical proof checker is Lean's kernel.

The isolated build starts without ATLAS compiled artifacts. Only clean pinned public
dependency source and cache copies are reused. This is not an independent Comparator
run, nor a source rebuild of Lean or all mathlib. Earlier development checks are not
substituted for the export build. No automatic verification service is configured.

Compilation can emit existing style, unused-tactic and unused-simplification warnings.
These are preserved in the build transcript; proof sources are not edited to silence
them. A successful build and the separate transitive trust audit are both required.
