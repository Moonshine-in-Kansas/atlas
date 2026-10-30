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
order/simplicity statements, two uniform-range supplements, six compiled
construction-isomorphism certificates, supplementary mathematical checkpoints,
Comparator results, the YAML index, AUDIT.md and complete manifests. Preparation
validation checks source and pin hashes, all 1,313 public audit roots,
immutable checker bundles, 33 diagram measurements,
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

## Source-bound mathematical additions

A source update retains the 33 catalogue defaults, all 45 dated existence and
comparison contracts (42 passes, three open), the original checker bundles and
the immutable Version 1.0 baseline. The dated research note is historical;
when registered, current supplementary results have a separate generated index
at `catalogue/CHECKPOINTS.md`.
Checkpoint completion does not assert completion of its containing family.

The optional `completed_checkpoints` field in `verification/current.json` names
`catalogue/checkpoints.json`. Its registry uses `schema_version: 1`,
`kind: supplementary-mathematical-results`, a bound `as_of` date, entries and an
evidence map. Entries have an id, title, classification, `status: verified-checkpoint`,
parameter domain, proved scope, unproved conclusions and `selected_refs` with
concrete declaration/source/module/kind/evidence references. Pending proposals
are not accepted as verified entries. Evidence binds the actual full result,
manifest, source map and compiled statement output, with independent replay
explicitly separate and unclaimed for this update.
The public references join the audit roots; `catalogue/manage.rb` links each
checkpoint to its verbatim compiled type, normal proof receipts and full policy audits.
Detailed helper targets and policies belong under `verification/`.

`source_update` identifies byte-preserved copies of the published `d2dca87`
current index and release manifest, the owner's update instruction and a separately
bound `proof_evidence` bundle. `ADDITIONS.json` in that bundle selects original
normal proof records covering every new Lean file and full audit scopes covering
every new public reference. Each scope retains its original checkpoint, result,
process receipt, log, declarations and full type/value dependency graph. Missing,
stopped, stale, mismatched or incomplete evidence is refused. The unchanged
historical results are never rewritten to refer to new sources.

An additions bundle also binds a complete required-policy inventory. Every
successor policy and every original source-transported policy must be applied
separately with its original target selection and manifest hash. Per-scope
policy outcomes must cover that inventory exactly. Full extractions can be
individual or shared batches: the latter print the complete union of types and
definitions once, with scoped receipts linking the original common process and
an exact dependency-closure slice. The gate recomputes each slice and all policy
outcomes; shared execution cannot drop an original scope or broaden its roots.
Graphs are loaded one extraction at a time. A missing required-policy entry
cannot be inferred from a graph: the parent must freeze the complete inventory
from the canonical lane handoffs before forming batches.

The four-step supplemental cache-audit schema remains supported for a single
whole-root run. For a source update its before/after source maps, exact cache
source map, portable before/after cache artifact inventories and original process
logs are required. Alternatively a format-2 supplemental pointer selects
`CACHE_AUDIT.json` with the same cache and two import-root checks followed by a
complete union of full audit scopes. Every public root must be covered; overlapping
graphs are counted as node occurrences, not unique dependency nodes. Both routes
retain `fresh_project_rebuild: false` and `independent_replay: false` and leave all
strict frozen-release requirements in force. The additions bundle is required
with either route. The publication bindings also cover all three registries,
the optional checkpoint index, the previous index/manifest and the additions bundle.

For a portable full checkpoint replay, first prepare and validate the pinned
compiled cache and retain the separate normal source proof receipts. The runner
requires the coordinator's **existing shared lease**; every verification driver
on the host must use that same lease. Then, from the candidate root:

```sh
ATLAS_VERIFICATION_LEASE=/absolute/path/to/existing/shared-lease \
  LEAN_NUM_THREADS=2 LAKE=lake \
  ruby verification/replay_checkpoint.rb \
  verification/checkpoints/CHECKPOINT.json /absolute/path/to/NEW_OUTPUT_DIRECTORY
```

The runner uses the existing extractor with full mode and definition bodies,
the supplied canonical targets and all boundary policies. It checks pinned Lean
and package revisions, requires local nonsymlinked project cache files, records
original process/log and before/after input bindings, and preserves failed attempts.
It does not build missing sources, download dependencies, replace normal source
checks or create independent replay acceptance. Its Linux memory guard enforces
8704 MiB Lean allocation, 9 GiB aggregate RSS, combined owned RSS plus swap below
two-thirds of physical RAM, at least 1 GiB actual available RAM and at most four
compute processes. The serial lease is mandatory, not an optional optimization.

The source-only implementation and its synthetic tests do not themselves certify
the runner on this host. Actual coordinator runs, logs, memory behavior and
mathematical scope require review before any new evidence is accepted. Evidence
hashes establish applicability, not execution or authorization attestations.
