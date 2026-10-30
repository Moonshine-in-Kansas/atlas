# Independent-checker reproduction

[Nanoda on 24 October](nanoda/2026-10-24-draft/README.md) passed 139,617 declarations
with zero typechecker errors and a pretty-printer warning. Its excluded incomplete
modules and 45 generated partial implementations are explicit in the bundle.
[Comparator on 25 October](existence/RESULTS.md) passed 42 of 45 targets; three
stopped at the memory cap. Neither result is a fresh check of this filtered export.

## Pinned tools

| Tool | Repository | Revision |
|---|---|---|
| Nanoda | https://github.com/ammkrn/nanoda_lib | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` |
| lean4export | https://github.com/leanprover/lean4export | `cacf989bd75f608700820f6afc595f32e7a99a4d` |
| Comparator | https://github.com/leanprover/comparator | `2312244ac716564a61cc0bf4e107d9abf1757a61` |
| Landrun | https://github.com/Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Build these pinned revisions using the repository's Lean toolchain and the
corresponding Rust/Go build tools. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. Keep complete logs and original exit statuses.

## Comparator

Start with a successful ordinary ATLAS build. Prepare a reviewed target using:

```sh
ruby verification/existence/prepare-queue.rb /absolute/path/to/new-queue AtlasExistence.cyclic
```

The preparer copies the exact reference, solution and Comparator configuration,
and writes local Lake paths with the same toolchain. It performs no build or
checker run. Without a target argument it prepares the 42 previously passed
targets. It refuses existing output directories and the three owner-deferred
targets. Keep a new source/configuration hash record and preserve all original
artifacts. The archived original harnesses retain their historical absolute paths.

Resolve the harness with `lake update`, verify the dependency revisions against
ATLAS's manifest, and put the pinned real Landrun and lean4export binaries in
`PATH`. From the harness directory, run:

```sh
LEAN_NUM_THREADS=1 lake env /absolute/path/to/comparator comparator.json
```

Use Comparator's real Linux sandbox. Require successful statement comparison,
permitted-axiom inspection, default Lean-kernel replay, quotient post-check and
final solution acceptance. One driver runs at a time; retain the recorded
9 GiB owned RSS-plus-swap ceiling and the host's memory reserve.
The exact [recorded driver](existence/2026-10-25-draft/driver.rb) and
[monitor](existence/2026-10-25-draft/monitor.rb) document the original invocation.

The separate frozen-interface comparison must cover all 1,313 current audit roots.
Its new reference/solution wrappers and target map require review against a
successful current-export build before replay. The old Version 1.0 harness covers
an older selection and cannot serve as Version 1.2 acceptance. No new interface
Comparator result is claimed by this package.

## Nanoda

The [scope and export inventory](nanoda/2026-10-24-draft/README.md) identify the
declarations checked in the broader local snapshot. The original scripts,
filtering rule, configuration and reviewed kernel receipt are retained there.
Do not silently treat excluded modules or generated partial implementations as
checked. A fresh clean-export run needs its own inventory and source hashes.

The retained `run_nanoda.rb` exports the selected `verification/roots.json`
interface closure, a smaller and different scope from that broad local replay:

```sh
export LEAN4EXPORT=/absolute/path/to/lean4export
export NANODA=/absolute/path/to/nanoda_bin
ruby verification/run_nanoda.rb
```

Preserve new results separately. Update release evidence only after all required
checks pass and the [metadata gate](MAINTENANCE.md) accepts their exact sources,
pins, roots and contracts. Reproduction can require substantial memory and disk.
