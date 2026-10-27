# Maintaining Version 1.2

Version 1.2 is the editable version on `main`. The owner authorized this working
publication on 27 October 2026 with the outstanding checks disclosed. Version 1.0
remains an immutable release. A frozen Version 1.2 release requires the separate
acceptance checks below; updating `main` does not freeze the version.

All 33 catalogue defaults, six additional model contracts, four strengthened
contracts and two aggregate comparison contracts are indexed. Albert-model F₄
and the two aggregate Comparator targets remain open after memory stops.
Publication does not retry these targets or count them as passed.

## Metadata and editable publication

```sh
ruby verification/release_metadata.rb refresh
ruby verification/release_metadata.rb check-preparation
ruby verification/release_metadata.rb check-working
git config core.hooksPath verification/hooks
```

Refresh generates the catalogue pages, 66 primary and eight additional-model
order/simplicity statements, two uniform-range supplements, four compiled
construction-isomorphism certificates, Comparator results, the YAML index,
AUDIT.md and complete manifests. Preparation validation checks source and pin
hashes, all 1,207 audit roots, immutable checker bundles, 33 diagram measurements,
reader links and every distributed file. These commands run no proof checker.

`check-working` also validates the owner-authorized publication scope in
`verification/current.json`: Version 1.2 on `main`, the exact mathematical source,
target and evidence bindings, and the explicitly allowed outstanding checks.
Documentation can be revised without changing those mathematical bindings.
A changed proof source, dependency pin, target selection or evidence bundle
requires updated applicable verification and publication metadata. No new failure
or unlisted open contract is implicitly authorized by the working-version policy.

The pre-push hook requires `check-working` for `main`. The retained `v1.2-review`
branch uses preparation validation; tags and every other branch use strict
acceptance. A mixed push uses the strictest gate. Every pushed commit must match
the checked HEAD, the checkout must be clean, and ref deletions are refused.
The Pages workflow validates the working-publication scope before deployment.
Local hooks are safeguards, not a server policy; recorded authorization and
hashes are not mathematical verification or cryptographic attestations of consent.

`RELEASE_MANIFEST.json` covers every distributed file except the three manifests
themselves. `SHA256SUMS` additionally covers that JSON manifest;
`verification/release-candidate/PACKAGE_SHA256SUMS` additionally covers
`SHA256SUMS`. Only the final package checksum file excludes itself. Local Git
metadata, Lake caches and `verification/results/` outputs are not distributed.
These metadata commands never push or change repository visibility.

## Acceptance before a frozen release

```sh
ruby verification/release_metadata.rb check
```

`check` repeats all metadata validation and refuses outstanding acceptance.
The exact export still needs accepted project proof rechecking with a complete
dependency audit, Nanoda replay and interface Comparator evidence. The three
deferred mathematical contracts must also be resolved under a later assignment.
The working-publication authorization does not satisfy these requirements.

`current.json` separates the supplemental cache audit and dated checker records
from current-export acceptance. The cache audit freshly elaborates the root
imports and inspects complete compiled dependencies. It is not a fresh rebuild
of every project proof or an independent kernel replay. Its two false scope flags
are checked; its success cannot fill an independent-checker acceptance slot.

Existing 42/45 outcomes remain immutable. New acceptance uses separate dated
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

Run lightweight regression checks with an output directory outside the export:

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
with editorial changes dated 27 October; README records its broader local scope.
Construction jobs and internal progress notes are excluded. Preserve Version 1.0's
immutable tag, release assets and original public history through every update.
The website root selects Version 1.2. Separate `v1.0/` and `v1.2/` views coexist;
old unversioned diagram URLs continue to show Version 1.0.
