# Mathieu proof dependency diagrams

Each self-contained HTML file offers **Graph**, **Tree**, and **Files** views, with order/simplicity filters, a declaration inspector, theorem counts, search, and embedded downloadable data. No network or companion HTML files are needed to display it. Repository source and cross-group links require the adjacent checkout/pages.

| Group | Expanded source files | Named source theorems in those files | Collapsed prerequisites |
|---|---:|---:|---|
| [M24](m24/M24.html) | 77 | 581 | M23 |
| [M23](m23/M23.html) | 5 | 34 | M24; Shared Golay / M24 geometry; Shared Golay / hexacode |
| [M22](m22/M22.html) | 20 | 67 | M23; M24; Shared Golay / M24 geometry; Shared Golay / hexacode |
| [M12](m12/M12.html) | 18 | 89 | M11; M24; Shared Golay / M24 geometry; Shared Golay / hexacode |
| [M11](m11/M11.html) | 5 | 40 | M12; Shared Golay / M24 geometry; Shared Golay / hexacode |

Arrows point from a dependent file to a prerequisite. Cross-group nodes list the **exact declarations reused**, rather than implying reliance on another group's entire order-and-simplicity package. For example, M12 simplicity uses M11 simplicity; M11 uses M12 structure/order/action, not M12 simplicity. These are acyclic declaration dependencies even though informal group-level names can appear in both directions.

## Scope and counts

The data comes from the actual compiled type/value dependency graph in [the passed 2026-09-17 audit](../../verification/release/RESULT.json), not imports. Every ATLAS source file in each complete closure is checked against the current evidence hashes. The historical dependency extraction predates the release licence-header update: exact comparison after that one header substitution verifies the correspondence; mathematical source is unchanged. Generation is a report, **not a new Lean proof recheck**. Lean/mathlib dependencies are omitted.

GitHub displays HTML source rather than running it. Download a linked HTML file and open it in a browser to use the interactive diagram. GitHub Pages is not required.

Named source theorem counts cover all named `theorem`/`lemma` commands in the file, including private ones, after removing comments and strings. “Used compiled” counts include generated proof helpers; definitions and instances are traversed but not counted as theorems. Whole-file totals may include unused or other-group statements in mixed files. Counts overlap between groups and are not additive. Boundary files/theorems are excluded from local totals; exact consumed declarations remain visible in the inspector.

Presentation boundaries are explicit: named Mathieu11/12/22/23/24 modules belong to that group; Dodecad modules belong to M12. Codes modules are shared Golay/hexacode foundations; other construction geometry reused from M24's closure is shared Golay/M24 geometry. M24 expands its shared construction; descendants collapse it. Generic group-theory lemmas and target-specific supporting files stay expanded. These are diagram organization rules, not new mathematical assumptions. M21 auxiliary lemmas within the M22 argument stay expanded.

The default graph removes transitive shortcut arrows while preserving reachability (checked separately for order, simplicity, and both). “All arrows” restores every recorded file edge. Shared tree branches link to their existing node.

## Regeneration

From the repository root:

```sh
ruby verification/dependency-maps/mathieu/generate.rb
```

The maintained inputs are `mathieu/generate.rb`, `mathieu/viewer.html.erb`, the repository sources, and the existing immutable audit. The five HTML pages and this README are generated outputs. Redundant former standalone tree/graph files, intermediate JSON/CSV/DOT/Mermaid exports, and superseded M24-only generators have been removed. CSV/JSON can instead be downloaded from each page.
