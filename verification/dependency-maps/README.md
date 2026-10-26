# Proof-dependency diagrams

The 33 current diagrams are linked from the [catalogue](../../CATALOGUE.md).
Each contains its actual order/simplicity roots, source hashes and dated audit
provenance. The [packaging binding](../release-candidate/DIAGRAM_BINDING.json)
records the approved licence-comment substitution; it is not a new proof check.

`ruby catalogue/manage.rb check` verifies the diagram roots and sources.
Every current diagram labels the construction whose proof graph is shown and
links all available models and proved Lean identification certificates. The
navigation is generated from the same inventory as the catalogue. Its separate
[presentation binding](../../catalogue/model-presentation.json) preserves the
original graph data, source hashes, roots and counts byte for byte.
`ruby verification/dependency-maps/build_site.rb EMPTY_OUTPUT_DIRECTORY` stages
the website after the source repository has its preserved `v1.0` tag. It verifies
that tag against the original public commit before reading the old diagrams.

Existing unversioned diagram URLs continue to show Version 1.0. The new root
index selects the Version 1.2 view, and both `v1.0/` and `v1.2/` remain available.
The workflow runs the strict release gate before any deployment.
