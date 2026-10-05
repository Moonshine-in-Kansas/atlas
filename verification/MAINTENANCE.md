# Maintaining release metadata

`catalogue/` contains machine-readable catalogue and line-count data. The root
README, catalogue, research PDF, audit summary, licensing and Lean configuration
are the reader's entry points. Detailed verification material belongs here.

After cloning, install the local publication gate once:

```sh
git config core.hooksPath verification/hooks
```

For documentation-only changes (including a new research PDF), run:

```sh
ruby verification/release_metadata.rb refresh
ruby verification/release_metadata.rb check
```

The refresh regenerates AUDIT.md, THEOREM_STATEMENTS.md and both manifests.
The statement document is rendered from the hashed compiled-statement log in the
current evidence snapshot. New snapshots must include that log and its hash.
The check is read-only.
The pre-push hook requires a passing check and a clean committed checkout.
Git hooks are local safeguards, not a server policy; clones must install them,
and a user can deliberately bypass them. No push or visibility change is automated.

For changed mathematics, toolchain pins, catalogue targets or measured source
lines, old success records cannot be reused: the metadata gate fails. Run the
required build/dependency audit and checker runs, retain their evidence in a new
dated directory, and update `current.json` only after reviewing successful results.
Its source map must cover exactly the current Atlas sources and three pin/build
files; its roots must match the current catalogue and verification target list.
Recompute line counts and update `catalogue/measurement.json`. Never modify an
old successful run to make it appear to cover new mathematics.

The current evidence summaries are historical records, not signed execution
attestations. Source hashes bind their applicability; they do not prove the
checks actually ran. A later independent rerun remains possible.

The mathematical review of new catalogue descriptions, changes to licensing,
and explicit permission before public visibility remain human decisions.

## Formalization metadata and Comparator contracts

The single root `formalization.yaml` holds the project-wide description. Its
`status.main_results` and verification report counts are generated from
`verification/existence/registry.json`. Each registry entry supplies the display
name, declaration, scope, solution imports and immutable successful evidence path.
Every family/sporadic catalogue entry must have an existence-contract entry;
an uncovered new group blocks publication.

The reviewed mathematical specifications remain in
`verification/existence/{Challenge,Solution}.lean` and
`verification/existence/discriminators/{Challenge,Solution}.lean`.
Edit these deliberately when adding or changing results. The tooling does not
invent a mathematical specification from an implementation theorem.
The shared renderer generates each individual Challenge, Solution and Comparator
configuration when preparing a queue. The same renderer checks that the recorded
successful inputs match the current contracts exactly.

For a new release:

1. Update the reviewed contracts and registry for new or changed results. Preserve
   the project-wide YAML description; update its prose when the scope changes.
2. Use the existing preparation and sequential runner instructions to check both
   required scopes. Run one checker at a time with the documented memory limits.
3. Collect successful evidence with
   `ruby verification/existence/collect-results.rb QUEUE_DIRECTORY YYYY-MM-DD`
   and the corresponding `discriminators/collect-results.rb` command. A date is
   optional and defaults to the current UTC date. Collectors refuse to overwrite
   different historical records and update registry evidence pointers only for
   validated passes. Use a new evidence directory for changed runs.
4. Run `ruby verification/release_metadata.rb refresh`, then `check`.
   This automatically synchronizes and validates the root YAML, combined Comparator
   configurations and target index, as well as release checksums. The pre-push
   hook repeats the check. Changed contracts, changed source snapshots, missing
   results, corrupted logs or incomplete catalogue coverage block publication.

No historical proof result is promoted to cover changed sources. A metadata
refresh runs no Lean proofs and grants no new verification status. Project-wide
YAML prose and mathematical specifications still require deliberate maintenance.
The private release-preparation script uses this same gate; uploads remain explicit.

Run `ruby verification/existence/test-sync.rb` for lightweight regression checks
of these safeguards, without launching Lean or accessing the network.

## Proof dependency diagrams

Catalogue entries optionally carry a `proof_dependencies` HTML path.
The metadata gate generates/checks the single Lean files / theorems column and
checks each diagram’s theorem roots and source hashes. Regenerate all twenty-three
published group/family pages with `ruby verification/dependency-maps/sporadic/generate.rb`
after changes to the diagram generator or template, then run the usual metadata
refresh/check. Changed mathematical sources require new verification evidence;
the generator accepts only the recorded release licence-header substitution
against the historical dependency graph. The private release-preparation script
copies the maintained viewer tools and regenerates against release sources.
GitHub Pages was enabled with owner authorization on 5 October 2026.
The catalogue’s `proof_dependencies_site` selects the rendered website URL.
The Pages workflow checks metadata and source bindings, then publishes only the
linked diagrams and an index. Repository source/audit links stay on github.com.
Changes to diagrams, catalogue data or the workflow redeploy automatically.
Local release preparation never enables Pages or pushes without authorization.
