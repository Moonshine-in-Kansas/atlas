# Existence contracts for the published ATLAS

[Challenge.lean](Challenge.lean) is the fixed mathematical specification. It imports only
mathlib: no ATLAS definitions, theorem aliases, or construction assumptions.
There are 23 targets: eight families and fifteen sporadic entries in the current
release. Each existential quantifier binds **one** group, with finiteness, order,
simplicity and noncommutativity asserted for that same group. The cyclic target
asserts commutativity instead. Family formulas and admissibility conditions are
written out explicitly; q means the cardinality of the quantified finite field.

[Solution.lean](Solution.lean) proves these statements by supplying the existing ATLAS groups.
It does not import Challenge. The comparator configuration permits only
`propext`, `Quot.sound`, and `Classical.choice`, and has no definition holes.

The deliberate `sorry` proofs in Challenge are specification placeholders, as
required for unproved Comparator reference theorems. They are not mathematical
results, are not root-imported, and must never enter solution dependencies.
The solution has no placeholders or additional axioms. Challenge and Solution
must be built as separate modules; importing both would duplicate target names.

[Current per-entry results](RESULTS.md) contain only completed successful runs.

## Meaning and limits

The labels M24, Fi22, and so on are navigation labels for existential statements
with explicit numeric orders. These contracts **do not claim identification or
uniqueness of an isomorphism type**. In particular B and C have equal displayed
order formulas, so the original existence statements alone cannot distinguish them.
The [strengthened invariant contracts](discriminators/README.md) additionally
attach involution-class counts for B/C and Sylow-center orders for the order-20,160
pair to the same group witnesses; their [results](discriminators/RESULTS.md) are
recorded separately. The original contracts do not specify group constructions
or actions. The supplementary invariants distinguish the stated same-order pairs;
full construction and comparison theorems remain separate ATLAS results.

Excluded family parameters are omitted from the positive existence claims.
This does not assert that no other simple group can have an excluded order.
The construction-specific exact-exception theorems remain in ATLAS.

These are new reference statements prepared for review, not an independently
peer-reviewed specification. They replace the proposed shared-import contract
from the interrupted preparation; the historical September 18 evidence is
untouched. Its 911-target run does not certify these new 23 targets.

## Preparation and later Comparator run

From the release root:

```sh
ruby verification/existence/prepare.rb
```

This validates the target lists and writes a small standalone Lake harness under
ignored `verification/results/`. It does not run Comparator. In the printed
directory run `lake update`, then use the pinned tools and real sandbox documented
in `../INDEPENDENT_CHECKERS.md`, passing `comparator.json`. Do not use the old
`verification/prepare_comparator.rb`: it reproduces the historical self-comparison.
Use one Lean/checker process at a time on this laptop.

The preparatory check is reproducible with
`ruby verification/existence/check.rb` from the release root.
[PRECHECK.json](PRECHECK.json) records the successful compiled statement comparison
and solution axiom check. It does not record a Comparator run.

A successful syntax/build check is not a successful Comparator run. New results
must record actual exit status, complete logs and hashes of the reference,
solution, configuration, source tree and tool versions. Do not relabel old runs.

## Sequential per-entry checks

To reduce peak memory, use `prepare-split.rb PATH_TO_PREPARED_HARNESS` after
preparing and resolving the combined harness above. It writes 23 isolated
single-target harnesses and `QUEUE.json` under ignored results. Each solution
imports the relevant construction modules, not the ATLAS root. The theorem
statements and proof bodies are retained from the checked combined files.
Run these harnesses sequentially with the same real sandboxed Comparator.
Each target has its own log, time report, source hashes and result.

The first combined attempt stopped at the available-memory safety reserve;
it did not return a proof rejection or successful Comparator verdict.
The local sequential runner uses a 9 GiB combined worker RSS ceiling and a
256 MiB emergency available-memory reserve, stopping the queue on a memory
limit while retaining completed results. RSS is monitored, not a hard cgroup
allocation limit. Splitting repeats shared proof dependencies and may increase
total runtime; an individual large proof can still reach the memory limit.

## Running the sequential queue

Build the pinned tools from the reproduction guide. Set `COMPARATOR_ROOT`,
`EXPORTER_ROOT` and `LANDRUN_ROOT` to their source checkouts, with built binaries
at the documented locations. `LAKE` optionally selects the Lake executable.
After preparing the split harnesses, run from the release root:

```sh
systemd-run --user --wait --pipe \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$PWD" -E PATH="$PATH" \
  -E COMPARATOR_ROOT -E EXPORTER_ROOT -E LANDRUN_ROOT \
  -- ruby verification/existence/run-queue.rb /absolute/path/to/split-harnesses
```

The driver verifies tool source revisions and binary hashes, records current source
hashes, and refuses to overwrite previous run records. It uses the real Landrun
sandbox and retains each result separately. `run-entry.rb HARNESS` runs one entry
under the same outer systemd restriction. The supplied `collect-results.rb QUEUE`
collects only passing results whose logs, inputs and current source hashes match.
The recorded run used equivalent local operational drivers; portable copies here
have configurable paths and have not themselves been used for a fresh full rerun.
