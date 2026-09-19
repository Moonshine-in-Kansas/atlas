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

The refresh regenerates AUDIT.md and both manifests. The check is read-only.
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
