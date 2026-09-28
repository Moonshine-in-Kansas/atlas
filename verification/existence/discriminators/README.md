# Existence with invariants distinguishing same-order groups

The [reference](Challenge.lean) and [solution](Solution.lean) contain four complete
existence statements with additional invariants attached to the same group witness.
See [the results](RESULTS.md) for the mathematics and completed Comparator evidence.

The reference uses only mathlib imports. Its explicit `k2` definition counts
conjugacy classes containing an element of order exactly two. It has no definition
holes. As in the original contracts, only the reference goals have deliberate
unproved placeholders; the solution never imports the reference and contains none.
The allowed proof axioms are `propext`, `Quot.sound` and `Classical.choice`.
The [precheck](PRECHECK.json) records compiled statement and axiom checks, separately
from the full Comparator evidence.

The solution reuses the actual public B/C models and their proved class counts.
For the order-20,160 pair it uses the alternating group on eight letters and
PSL₃ over mathlib's Galois field of four elements. The counts are proved for every
Sylow-2 subgroup, using the previously constructed subgroups and Sylow conjugacy.
The old mathematical sources and dependency pins have not changed.

## Reproduction

From the release root:

```sh
ruby verification/existence/discriminators/check.rb
ruby verification/existence/discriminators/prepare.rb /absolute/path/to/prepared-parent-harness
```

A parent harness is made using [the main preparation instructions](../README.md).
The second command creates four single-target harnesses, each with specific ATLAS
imports, and prints a queue directory. Run the shared `run-queue.rb` with that
directory, the pinned tool source paths and the real systemd/Landrun sandbox,
exactly as described in [the main runner instructions](../README.md#running-the-sequential-queue).
Only one checker runs at a time, with a 9 GiB combined RSS ceiling and a 256 MiB
available-memory reserve. Old result files are never overwritten.

`collect-results.rb QUEUE_DIRECTORY` copies only completed passing records after
checking the input, log and current-source hashes. Successful records are source-
bound execution evidence, not signed attestations. No push is performed by any script.
