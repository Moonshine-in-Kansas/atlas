# Maintaining Version 1.2 metadata

This is a prepared candidate with pending publication acceptance. All 33
catalogue defaults, six additional model contracts, four strengthened contracts
and two aggregate comparison contracts are indexed. The three deferred targets
remain open; preparation does not retry them or count them as passed.

## Local preparation

```sh
ruby verification/release_metadata.rb refresh
ruby verification/release_metadata.rb check-preparation
```

Refresh generates the catalogue pages, 66 primary and eight additional-model
order/simplicity statements, two uniform-range supplements, four compiled construction-isomorphism certificates,
Comparator result table and YAML result index, AUDIT.md and complete manifests.
The read-only preparation check verifies exact source and pin hashes, all 1,207
audit roots across the catalogue and realization/comparison registries,
immutable checker bundles, 33 diagram measurements, reader links and every
distributed file. It accepts explicitly pending verification as a preparation
state. It launches no proof checker and grants no publication acceptance.

`RELEASE_MANIFEST.json` covers every distributed file except the three manifests
themselves. `SHA256SUMS` additionally covers that JSON manifest;
`verification/release-candidate/PACKAGE_SHA256SUMS` additionally covers
`SHA256SUMS`. Only the final package checksum file excludes itself. Ignored local
Git metadata, Lake caches and `verification/results/` outputs are not distributed.

## Publication gate

```sh
ruby verification/release_metadata.rb check
git config core.hooksPath verification/hooks
```

`check` repeats preparation validation and refuses outstanding acceptance.
The owner has separately authorized uploading the candidate to `v1.2-review`
while keeping `main` at Version 1.0 for review. Only that review branch uses
`check-preparation` in the pre-push hook. Main, version tags and every other
branch still require `check`. Every pushed commit must match the checked HEAD,
and the checkout must be clean. Mixed pushes containing a main/tag update use
the strict gate for the whole push. The Pages workflow always uses the strict
gate and deploys automatically only for main. A review upload creates no final
release tag and does not change the default branch or deploy Pages.

Local hooks are safeguards, not a server policy. Owner review and completion of
acceptance remain prerequisites for promoting Version 1.2 to main.
These commands never push, enable Pages or change repository visibility.

`current.json` separates the supplemental cache audit and dated checker records
from current-export acceptance. The cache audit is a successful fresh root
elaboration and full compiled dependency inspection. It is not a fresh rebuild
of every project proof or an independent kernel replay. Its two false scope flags
are checked, and its success cannot fill an independent-checker acceptance slot.

Before promotion, the exact export still needs accepted project proof rechecking,
a complete dependency audit, Nanoda and interface Comparator evidence. The three
deferred mathematical contracts must also be resolved under a later assignment.
Existing 42/45 outcomes stay immutable. New acceptance uses separate dated
evidence, exact source/pin and root maps, a hashed bundle, original process
receipts and an explicit `ACCEPTANCE.json`; old results must not be relabelled.
An accepted receipt declares its check kind, allowed axioms, unchanged inputs
and actual proof-rebuild/replay scope. The gate validates applicability and
process outcomes. Human review of the real logs and mathematical scope remains
necessary; a JSON receipt and its hashes are not execution attestations.

## Contracts and reproduction

The format-2 [registry](existence/registry.json) binds every actual model to its
reviewed reference, solution and configuration in the original dated bundle.
Albert F₄ and Chevalley F₄ are distinct witnesses. Every contract uses its
registered construction. Missing or substituted defaults are rejected.

To prepare a portable harness without running a checker:

```sh
ruby verification/existence/prepare-queue.rb /absolute/path/to/new-queue AtlasExistence.cyclic
```

With no target arguments this prepares the 42 previously passed targets.
It refuses the three owner-deferred targets and existing output directories.
Only local Lake paths and package metadata are adapted; reviewed Lean/config
bytes are copied exactly. Follow [the checker guide](INDEPENDENT_CHECKERS.md)
for an actual replay. No previous pass is promoted by harness preparation.

Run lightweight regression checks with an output directory outside the candidate:

```sh
ruby verification/test_metadata.rb /absolute/path/to/new-test-output
```

These deliberately alter in-memory test inputs and isolated scratch files.
They do not edit mathematical sources, dated evidence or original receipts.

## Reader documents and website

Edit catalogue data and use `ruby catalogue/manage.rb refresh`, then `check`.
Do not hand-edit generated catalogue or theorem-statement pages. Measurements
are dated declaration-span counts, with exact roots, sources and diagrams bound
by `catalogue/measurement.json`; they are not a new recount or proof check.

The research-note TeX/PDF reports the dated 25 October development account,
with editorial clarifications dated 26 October; README records its broader local scope. Construction jobs and internal progress
notes are excluded. Version 1.0's immutable release and original public history
must be rechecked before any promotion. The prepared Pages workflow preserves
old unversioned URLs and separate `v1.0/` and `v1.2/` views; the root becomes the
Version 1.2 view only after the strict gate and publication succeed.
