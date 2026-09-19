# Reproducing the independent checks

Start in the release checkout, with its pinned Lean toolchain, dependency caches
and ATLAS build available. Run one checker at a time. These instructions reproduce
the recorded checks; they do not promote new results into the release evidence.
They require Linux for the Comparator sandbox. Build tools outside the repository.

## Tool versions

Use the following source revisions from the recorded run:

| Tool | Source | Revision | Build command in that checkout |
|---|---|---|---|
| Nanoda | https://github.com/ammkrn/nanoda_lib | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` | `cargo build --release --locked -j 1` |
| lean4export | https://github.com/leanprover/lean4export | `cacf989bd75f608700820f6afc595f32e7a99a4d` | `LEAN_NUM_THREADS=2 lake build lean4export` |
| Comparator | https://github.com/leanprover/comparator | `2312244ac716564a61cc0bf4e107d9abf1757a61` | `LEAN_NUM_THREADS=2 lake build comparator` |
| Landrun | https://github.com/Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` | `go build -o landrun ./cmd/landrun` |

Clone each tool repository and check out the revision above. Build the Lean tools
using the ATLAS `lean-toolchain` version. Tool compilation needs the corresponding
Rust, Go or Lean development tools. Consult the README at each pinned revision for
its platform requirements. No tool binaries or external proof exports are bundled.

## Nanoda

Set absolute paths to the binaries built above, then run from the ATLAS root:

```sh
export LEAN4EXPORT=/absolute/path/to/lean4export/.lake/build/bin/lean4export
export NANODA=/absolute/path/to/nanoda_lib/target/release/nanoda_bin
ruby verification/release_metadata.rb check
ruby verification/run_nanoda.rb
```

The driver exports every selected root in `verification/roots.json` and its proof
and type dependencies, then runs Nanoda with one thread and only `propext`,
`Classical.choice` and `Quot.sound` permitted. It records binary hashes, source
hashes, timings, output and a result under `verification/results/nanoda-TIMESTAMP/`.
A successful result requires exit status zero, Nanoda's success marker and unchanged
source hashes. Verify your tool checkout revisions: the driver records binary
hashes but cannot infer their source revision from an arbitrary executable.

The previous run exported about 936 MB, checked 70,891 declarations and took
31 minutes in Nanoda, using about 5.1 GiB peak resident memory. These are historical
measurements, not performance guarantees. GNU `/usr/bin/time` is required.

## Comparator

Prepare the same-reference comparison harness:

```sh
ruby verification/prepare_comparator.rb
```

In the printed output directory, run `lake update` to resolve the local ATLAS
package. Check that its dependency revisions still equal the release pins. Put
the real Landrun and pinned lean4export binaries in `PATH`, alongside Comparator.
Then run, from that harness directory:

```sh
systemd-run --user --wait --pipe \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$PWD" -E PATH="$PATH" -E LEAN_NUM_THREADS=2 \
  -- lake env comparator config.json
```

Use the real Landrun sandbox, not Comparator's development fake-landrun script.
The address-family restriction follows the pinned Comparator's documented sandbox
invocation. It requires a working user systemd manager and a supported Linux sandbox.
Keep the complete output and exit status; look for successful statement comparison,
axiom checking, standard Lean kernel replay and the final solution-accepted verdict.
The earlier run took 41 minutes 36 seconds. Nanoda is a separate run above.

The frozen harness compares 869 theorem targets and 42 definition equality wrappers,
with no definition holes. Challenge and Solution both import the same ATLAS
snapshot. This checks the frozen formal interfaces and their proofs; it is **not**
a comparison against an independently authored mathematical specification.

## Evidence preservation

Current results are under `2026-09-18/` and summarized in `../AUDIT.md`.
Keep new output in ignored `results/`. Do not overwrite old successful records or
edit their hashes to make them appear to cover changed mathematics. Reproduction
also depends on the host, kernel, compiler and pinned dependency artifacts.
The portable drivers are packaging adaptations of the recorded commands; adding
these instructions did not itself repeat the full Nanoda or Comparator runs.
