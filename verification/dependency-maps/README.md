# Sporadic proof dependency diagrams

Each self-contained HTML file offers **Graph**, **Tree**, and **Files** views, with order/simplicity filters, a declaration inspector, theorem counts, search, and embedded downloadable data. No network or companion HTML files are needed to display it. Repository source and cross-group links require the adjacent checkout/pages.

| Group | Expanded source files | Named source theorems in those files | Collapsed prerequisites |
|---|---:|---:|---|
| [M24](m24/M24.html) | 77 | 581 | M23 |
| [M23](m23/M23.html) | 5 | 34 | M24; Shared Golay / M24 geometry; Shared Golay / hexacode |
| [M22](m22/M22.html) | 20 | 67 | M23; M24; Shared Golay / M24 geometry; Shared Golay / hexacode |
| [M12](m12/M12.html) | 18 | 89 | M11; M24; Shared Golay / M24 geometry; Shared Golay / hexacode |
| [M11](m11/M11.html) | 5 | 40 | M12; Shared Golay / M24 geometry; Shared Golay / hexacode |
| [Co1](co1/Co1.html) | 148 | 766 | M22; M23; M24; Shared Golay / M24 geometry; Shared Golay / hexacode |
| [Co2](co2/Co2.html) | 40 | 167 | Co0 / Leech isometries; Co1; M22; M23; M24; Shared Golay / M24 geometry; Shared Golay / hexacode; Shared Leech lattice |
| [Co3](co3/Co3.html) | 85 | 341 | Co0 / Leech isometries; Co2; M12; M22; M23; M24; Shared Golay / M24 geometry; Shared Golay / hexacode; Shared Leech lattice |
| [McL](mcl/McL.html) | 50 | 173 | Co0 / Leech isometries; Co2; Co3; M22; M23; M24; Shared Golay / M24 geometry; Shared Golay / hexacode; Shared Leech lattice |
| [HS](hs/HS.html) | 31 | 146 | Co0 / Leech isometries; Co2; Co3; M12; M22; M23; Shared Golay / M24 geometry; Shared Golay / hexacode; Shared Leech lattice |
| [Suz](suz/Suz.html) | 212 | 963 | M11; M12; Shared Golay / M24 geometry; Shared Golay / hexacode; Shared Leech lattice |
| [J2](j2/J2.html) | 187 | 837 | Shared Golay / hexacode |
| [Fi22](fi22/Fi22.html) | 37 | 124 | M22; M23; Shared Fischer tensor / ray construction; Shared Golay / M24 geometry; Shared Golay / hexacode; Suz |
| [Fi23](fi23/Fi23.html) | 37 | 124 | M22; M23; Shared Fischer tensor / ray construction; Shared Golay / M24 geometry; Shared Golay / hexacode; Suz |
| [Fi24Prime](fi24prime/Fi24Prime.html) | 642 | 2532 | Co0 / Leech isometries; M22; M23; M24; Shared Golay / M24 geometry; Shared Golay / hexacode; Shared Leech lattice; Suz |

Arrows point from a dependent file to a prerequisite. Cross-group nodes list the **exact declarations reused**, rather than implying reliance on another group's entire order-and-simplicity package. For example, M12 simplicity uses M11 simplicity; M11 uses M12 structure/order/action, not M12 simplicity. These are acyclic declaration dependencies even though informal group-level names can appear in both directions.

## Scope and counts

The data comes from the actual compiled type/value dependency graph in [the passed 2026-09-17 audit](../../verification/release/RESULT.json), not imports. Every ATLAS source file in each complete closure is checked against the current evidence hashes. The historical dependency extraction predates the release licence-header update: exact comparison after that one header substitution verifies the correspondence; mathematical source is unchanged. Generation is a report, **not a new Lean proof recheck**. Lean/mathlib dependencies are omitted.

The public catalogue links open rendered diagrams on GitHub Pages. The HTML files can also be downloaded and opened locally; GitHub’s repository file viewer itself displays their source.

Named source theorem counts cover all named `theorem`/`lemma` commands in the file, including private ones, after removing comments and strings. “Used compiled” counts include generated proof helpers; definitions and instances are traversed but not counted as theorems. Whole-file totals may include unused or other-group statements in mixed files. Counts overlap between groups and are not additive. Boundary files/theorems are excluded from local totals; exact consumed declarations remain visible in the inspector.

Presentation boundaries are explicit in the generator. Named public sporadic modules, Mathieu/Co2/Co3/McL/HS modules, norm-six geometry, and Eisenstein/icosian models identify their respective constructions. Dodecad modules belong to M12. M24 expands its Golay/hexacode foundation; Co1 expands the Leech lattice and Co0 isometries; Fi24Prime expands the shared Fischer tensor/ray construction. Other pages collapse these packages and show their exact consumed declarations. Co0 is kept distinct from its simple quotient Co1; shared Fischer construction is not labeled as Fi24Prime simplicity. Fi22/Fi23 keep their common parameterized residue proofs visible. Generic lemmas and target-specific support stay expanded. These are presentation boundaries, not mathematical assumptions or a claim that every statement in a mixed source file concerns just one group.

The default graph removes transitive shortcut arrows while preserving reachability (checked separately for order, simplicity, and both). “All arrows” restores every recorded file edge. Shared tree branches link to their existing node.

## Regeneration

From the repository root:

```sh
ruby verification/dependency-maps/sporadic/generate.rb
```

The maintained inputs are `sporadic/generate.rb`, `sporadic/viewer.html.erb`, the repository sources, and the existing immutable audit. The fifteen HTML pages and this README are generated outputs. Redundant former standalone tree/graph files, intermediate JSON/CSV/DOT/Mermaid exports, and superseded M24-only generators have been removed. CSV/JSON can instead be downloaded from each page.
