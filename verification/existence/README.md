# Independent mathematical contracts

[Current dated results](RESULTS.md) contain 39 concrete-model existence targets,
four strengthened discriminator targets and two aggregate comparison targets:
42 passed and three remain open after memory stops. The owner has deferred
Albert-model F₄ and the two aggregate targets. No new retry is implied.

All 33 completed catalogue defaults are covered, with six additional
realizations. Each exact reference, solution and original receipt is linked in
the results table and indexed in the format-2 [registry](registry.json).
References may contain deliberate theorem placeholders; these are specification
inputs, never solution dependencies. Existence and discriminator references
import only mathlib. Aggregate references share the actual concrete model
registry and label-normalization definitions.

Use [the checker guide](../INDEPENDENT_CHECKERS.md) to reproduce a selected
contract. `prepare-queue.rb` copies the reviewed inputs to a fresh local harness
and refuses the three deferred targets. It performs no build or checker run.
`sync.rb refresh` regenerates result metadata from the immutable original
receipts; `sync.rb check` checks consistency without editing files.

Preserve each witness and its full parameter range. The Chevalley F₄ contract
does not replace the Albert-model contract. A successful existence check
establishes its formal statement, not an external recognition theorem.
Exact-export acceptance for a frozen release remains separate; see [maintenance](../MAINTENANCE.md).
