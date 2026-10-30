# Completed mathematical checkpoints

These are completed statements in continuing projects. They do not add completed
simple-group catalogue entries or independent Comparator passes. Each statement links to its Lean source, exact compiled signature and full
dependency audit. The complete signatures remain in the linked evidence.

<a id="twisted-e6-order-and-fixed-projection"></a>

## Simply connected twisted E₆ order and fixed projection

Parameters: For the group order and fixed projection: finite fields F and K, [Field F], [Field K], [Finite F], [Finite K], [Algebra F K], Module.finrank F K = 2, and q=|F|>=2. The separate weighted Weyl-sum identity holds for every natural number q, without field hypotheses.

Proved scope:

- The actual simply connected graph–Frobenius fixed subgroup H has order q^36(q^12−1)(q^9+1)(q^8−1)(q^6−1)(q^5+1)(q^2−1), including q=2. The actual weighted Bruhat Weyl sum is evaluated.
- The actual fixed projection onto the adjoint fixed subgroup is surjective. Quotienting H by that projection kernel gives the adjoint fixed subgroup.

Unproved conclusions:

- The kernel is not asserted to be the entire center. Full center, order of the quotient by the full center, and simplicity remain open; no completed twisted-E₆ simple-family entry follows.

### Closed order of H

[Atlas.Chevalley.TwistedE6.ClosedOrder.companionFixedSubgroup_card](../Atlas/LinearGroups/Chevalley/TwistedE6/E6ClosedOrder.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-009-twisted-e6/original/scopes/scope-b8afd86081637eefd6f355e0/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-009-twisted-e6/original/scopes/scope-b8afd86081637eefd6f355e0/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.Chevalley.TwistedE6.E6ClosedOrder](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.Chevalley.TwistedE6.E6ClosedOrder/PROCESS.json)

### Exact weighted Weyl sum

[Atlas.Chevalley.TwistedE6.ClosedOrder.diagramFixedWeylSum](../Atlas/LinearGroups/Chevalley/TwistedE6/E6ClosedOrder.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-009-twisted-e6/original/scopes/scope-b8afd86081637eefd6f355e0/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-009-twisted-e6/original/scopes/scope-b8afd86081637eefd6f355e0/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.Chevalley.TwistedE6.E6ClosedOrder](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.Chevalley.TwistedE6.E6ClosedOrder/PROCESS.json)

### companionFixedProjection surjective

[Atlas.Chevalley.TwistedE6.companionFixedProjection_surjective](../Atlas/LinearGroups/Chevalley/TwistedE6/FixedProjection.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-012-twisted-e6/original/scopes/scope-8f532b62e7f84236d0886312/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-012-twisted-e6/original/scopes/scope-8f532b62e7f84236d0886312/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.Chevalley.TwistedE6.FixedProjection](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.Chevalley.TwistedE6.FixedProjection/PROCESS.json)

### companionFixedQuotientEquiv

[Atlas.Chevalley.TwistedE6.companionFixedQuotientEquiv](../Atlas/LinearGroups/Chevalley/TwistedE6/FixedProjection.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-012-twisted-e6/original/scopes/scope-8f532b62e7f84236d0886312/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-012-twisted-e6/original/scopes/scope-8f532b62e7f84236d0886312/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.Chevalley.TwistedE6.FixedProjection](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.Chevalley.TwistedE6.FixedProjection/PROCESS.json)

<a id="twisted-e6-centralizer-recovery"></a>

## Quadratic-field matrix and minuscule centralizer recovery

Parameters: Finite fields F,K with [Field F], [Field K], [Finite F], [Finite K], [Algebra F K] and Module.finrank F K = 2, including |F|=2. Matrix recovery allows every finite decidable index type n and arbitrary matrices g,A,B; its hypothesis quantifies over every u in K. Minuscule recovery uses any Strings I Ω with finite decidable Ω, any i,j:I, nonzero integers ε,δ, any matrix g, and commutation with every ordered quadratic-conjugate root product. No invertibility of g or commutation of the two steps is assumed.

Proved scope:

- For arbitrary finite matrices, commutation with every quadratic-conjugate affine pair recovers commutation with both component matrices.
- For the existing marked minuscule root matrices, commutation with every twisted paired root product recovers commutation with both individual root families.

Unproved conclusions:

- These are matrix/blockwise conclusions, not a full fixed-group center theorem. Faithfulness of a minuscule projection and an affine formula for the quadratic adjoint block are not claimed.

### Separate root commutation

[Atlas.Chevalley.Integral.Minuscule.Strings.commute_roots_of_quadratic_pair](../Atlas/LinearGroups/Chevalley/TwistedE6/MinusculeCentralizerRecovery.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-013-twisted-e6/original/scopes/scope-365919178c959cefab852a56/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-013-twisted-e6/original/scopes/scope-365919178c959cefab852a56/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery/PROCESS.json)

### commute pair of quadratic extension

[Atlas.LinearAlgebra.MatrixCentralizer.commute_pair_of_quadratic_extension](../Atlas/LinearGroups/Chevalley/TwistedE6/MinusculeCentralizerRecovery.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-013-twisted-e6/original/scopes/scope-365919178c959cefab852a56/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-013-twisted-e6/original/scopes/scope-365919178c959cefab852a56/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.Chevalley.TwistedE6.MinusculeCentralizerRecovery/PROCESS.json)

<a id="ree-f4-order-generation"></a>

## Large Ree ²F₄ full order and generation

Parameters: Let F be any finite field of characteristic 2, let m be a natural number (m ≥ 0), and assume hcard: |F| = 2^(2m+1). Write q = |F| and G = Atlas.ReeF4.Model F m. No positivity assumption on m is imposed. Perfectness alone additionally requires 1 ≤ m. The named binary order theorem fixes m = 0 and assumes |F| = 2.

Proved scope:

- For q = 2^(2m+1), the actual intrinsic large Ree model has order q^12(q^6+1)(q^4−1)(q^3+1)(q−1) and is generated by the specified actual root, torus and Weyl operators. These conclusions include q = 2, whose full group order is 35,942,400. The full model is perfect for m ≥ 1 (q ≥ 8).

Unproved conclusions:

- Simplicity, field transport and the remaining incidence geometry are open.
- Perfectness requires m>=1; no perfectness of the full binary group is claimed. No binary-derived index, order, simplicity or identification with the retained Tits model follows.

### full group order

[Atlas.ReeF4.card_Model](../Atlas/LinearGroups/ReeF4/Order.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-6289916cfe7df6b9b1a7d0cd/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-6289916cfe7df6b9b1a7d0cd/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.Order](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.Order/PROCESS.json)

### binary full group order

[Atlas.ReeF4.card_Model_binary](../Atlas/LinearGroups/ReeF4/Order.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-6289916cfe7df6b9b1a7d0cd/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-6289916cfe7df6b9b1a7d0cd/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.Order](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.Order/PROCESS.json)

### full group generation

[Atlas.ReeF4.elementarySubgroup_eq_top](../Atlas/LinearGroups/ReeF4/Generation.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-cc703c5e023a900c672927f0/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-cc703c5e023a900c672927f0/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.Generation](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.Generation/PROCESS.json)

### full group perfectness

[Atlas.ReeF4.model_isPerfect](../Atlas/LinearGroups/ReeF4/Generation.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-cc703c5e023a900c672927f0/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-cc703c5e023a900c672927f0/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.Generation](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.Generation/PROCESS.json)

<a id="ree-f4-parabolics-and-binary-action"></a>

## Large Ree ²F₄ parabolics and binary action

Parameters: Let F be any finite field of characteristic 2, let m be a natural number (m ≥ 0), and assume hcard: |F| = 2^(2m+1). Write q = |F| and G = Atlas.ReeF4.Model F m. No positivity assumption on m is imposed. All parabolic, tail and full line-kernel statements include m = 0. The faithfulness and permutation-kernel endpoints fix F = ZMod 2, m = 0; the separate cardinality endpoints at q = 2 allow any finite field of order two.

Proved scope:

- The full first-point stabilizer is explicitly the image of R ⋊ (Sz(q) × Fˣ), with |R| = q^10 and |P| = q^12(q²+1)(q−1)². The full marked-line stabilizer is explicitly the image of K ⋊ GL₂(F), where the full pointwise kernel K lies in U, has eleven-field-parameter coordinates, is solvable, and has order q^11; |Q| = q^12(q−1)²(q+1). Both equivalences multiply the normal factor first and include q = 2. Over ZMod 2, the full model and its literal commutator subgroup act faithfully on the actual 1,755-point set.

Unproved conclusions:

- The eleven-parameter kernel coordinate equivalence is a bijection of types, not an assertion that the kernel is an additive vector group.
- Explicit radical filtrations, maximal normal 2-subgroup recognition, Borel/intersection and residue identifications, and full generalized-octagon geometry remain open.
- Faithfulness endpoints use the literal field ZMod 2; separate transport of this action to every two-element presentation is not asserted. Faithfulness does not establish derived index/order, transitivity, perfectness, simplicity or a Tits identification.

### binary literal derived faithful action

[Atlas.ReeF4.binaryDerived_specialPoints_faithful](../Atlas/LinearGroups/ReeF4/BinaryDerivedPointFaithfulness.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.BinaryDerivedPointFaithfulness](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.BinaryDerivedPointFaithfulness/PROCESS.json)

### binary literal derived restriction identity

[Atlas.ReeF4.binaryDerived_specialPoints_toPermHom_eq_restrict](../Atlas/LinearGroups/ReeF4/BinaryDerivedPointFaithfulness.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.BinaryDerivedPointFaithfulness](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.BinaryDerivedPointFaithfulness/PROCESS.json)

### binary literal derived permutation kernel

[Atlas.ReeF4.binaryDerived_specialPoints_toPermHom_ker_eq_bot](../Atlas/LinearGroups/ReeF4/BinaryDerivedPointFaithfulness.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.BinaryDerivedPointFaithfulness](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.BinaryDerivedPointFaithfulness/PROCESS.json)

### binary full group faithful action

[Atlas.ReeF4.binarySpecialPoints_faithfulSMul](../Atlas/LinearGroups/ReeF4/BinarySpecialPointFaithfulness.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.BinarySpecialPointFaithfulness](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.BinarySpecialPointFaithfulness/PROCESS.json)

### Faithful full binary action

[Atlas.ReeF4.binarySpecialPoints_toPermHom_injective](../Atlas/LinearGroups/ReeF4/BinarySpecialPointFaithfulness.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.BinarySpecialPointFaithfulness](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.BinarySpecialPointFaithfulness/PROCESS.json)

### binary full group permutation kernel

[Atlas.ReeF4.binarySpecialPoints_toPermHom_ker_eq_bot](../Atlas/LinearGroups/ReeF4/BinarySpecialPointFaithfulness.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-0c3bca893e766f15b73f63e7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.BinarySpecialPointFaithfulness](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.BinarySpecialPointFaithfulness/PROCESS.json)

### point parabolic order

[Atlas.ReeF4.card_firstPointParabolic](../Atlas/LinearGroups/ReeF4/PointParabolicSemidirect.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.PointParabolicSemidirect](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.PointParabolicSemidirect/PROCESS.json)

### binary point parabolic order

[Atlas.ReeF4.card_firstPointParabolic_binary](../Atlas/LinearGroups/ReeF4/PointParabolicSemidirect.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.PointParabolicSemidirect](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.PointParabolicSemidirect/PROCESS.json)

### full line kernel order

[Atlas.ReeF4.card_markedLineRestrictionKernel](../Atlas/LinearGroups/ReeF4/MarkedLineKernelRecognition.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-2a5d6783c2e0c9222216e742/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-2a5d6783c2e0c9222216e742/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition/PROCESS.json)

### binary line parabolic order

[Atlas.ReeF4.card_markedLineStabilizer_binary](../Atlas/LinearGroups/ReeF4/LineParabolicOrder.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-9f4dcc761bf209768b3b3400/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-9f4dcc761bf209768b3b3400/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.LineParabolicOrder](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.LineParabolicOrder/PROCESS.json)

### line parabolic order

[Atlas.ReeF4.card_markedLineStabilizer_project_form](../Atlas/LinearGroups/ReeF4/LineParabolicOrder.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-9f4dcc761bf209768b3b3400/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-9f4dcc761bf209768b3b3400/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.LineParabolicOrder](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.LineParabolicOrder/PROCESS.json)

### point tail order

[Atlas.ReeF4.card_positiveRootTailSubgroup](../Atlas/LinearGroups/ReeF4/PositiveRootTail.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-e3e9909cf90026ac066ca8c7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-e3e9909cf90026ac066ca8c7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.PositiveRootTail](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.PositiveRootTail/PROCESS.json)

### binary action degree

[Atlas.ReeF4.card_specialPoints_binary](../Atlas/LinearGroups/ReeF4/SpecialPointCount.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-caa8c58f4d2b1ffa878cff4f/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-caa8c58f4d2b1ffa878cff4f/CHECKPOINT.json).

### line parabolic semidirect equivalence

[Atlas.ReeF4.lineParabolicSemidirectEquiv](../Atlas/LinearGroups/ReeF4/LineParabolicSemidirect.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-8ca87fa5bf6a99563b6e491d/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-8ca87fa5bf6a99563b6e491d/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.LineParabolicSemidirect](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.LineParabolicSemidirect/PROCESS.json)

### line parabolic actual operator map

[Atlas.ReeF4.lineParabolicSemidirectEquiv_val](../Atlas/LinearGroups/ReeF4/LineParabolicSemidirect.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-8ca87fa5bf6a99563b6e491d/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-8ca87fa5bf6a99563b6e491d/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.LineParabolicSemidirect](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.LineParabolicSemidirect/PROCESS.json)

### full line kernel coordinates

[Atlas.ReeF4.markedLineKernelParameters](../Atlas/LinearGroups/ReeF4/MarkedLineKernelRecognition.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-2a5d6783c2e0c9222216e742/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-2a5d6783c2e0c9222216e742/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition/PROCESS.json)

### full line kernel solvability

[Atlas.ReeF4.markedLineRestrictionKernel_isSolvable](../Atlas/LinearGroups/ReeF4/MarkedLineKernelRecognition.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-2a5d6783c2e0c9222216e742/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-2a5d6783c2e0c9222216e742/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition/PROCESS.json)

### full line kernel recognition

[Atlas.ReeF4.markedLineRestrictionKernel_mem_positiveRootSubgroup](../Atlas/LinearGroups/ReeF4/MarkedLineKernelRecognition.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-2a5d6783c2e0c9222216e742/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-2a5d6783c2e0c9222216e742/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.MarkedLineKernelRecognition/PROCESS.json)

### point parabolic semidirect equivalence

[Atlas.ReeF4.pointParabolicSemidirectEquiv](../Atlas/LinearGroups/ReeF4/PointParabolicSemidirect.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.PointParabolicSemidirect](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.PointParabolicSemidirect/PROCESS.json)

### point parabolic actual operator map

[Atlas.ReeF4.pointParabolicSemidirectEquiv_apply](../Atlas/LinearGroups/ReeF4/PointParabolicSemidirect.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.PointParabolicSemidirect](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.PointParabolicSemidirect/PROCESS.json)

### point tail solvability

[Atlas.ReeF4.positiveRootTailSubgroup_isSolvable](../Atlas/LinearGroups/ReeF4/PositiveRootTail.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-e3e9909cf90026ac066ca8c7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-e3e9909cf90026ac066ca8c7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.PositiveRootTail](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.PositiveRootTail/PROCESS.json)

### point tail normality

[Atlas.ReeF4.positiveRootTail_normal_in_firstPointParabolic](../Atlas/LinearGroups/ReeF4/PointParabolicSemidirect.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-011-large-ree/original/scopes/scope-defd132c6d1a6708bd4253f7/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeF4.PointParabolicSemidirect](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeF4.PointParabolicSemidirect/PROCESS.json)

<a id="j1-local-subgroup-and-whitelaw-orbit"></a>

## J₁ local subgroup and the 1,596-point orbit

Parameters: The fixed original octonion construction over ZMod 11 with its retained generators P,Q,R,S, subgroup H=<P,Q,R>, seven-dimensional trace-zero projective space and ten specified seed points.

Proved scope:

- The actual sign subgroup has order 8 and the P,Q subgroup has order 21. The unique sign–P–Q normal form gives |H|=168.
- The ten disjoint H-orbits have sizes 84,168,...,168. Their 1,596-point union is invariant under the actual generated group, equals its orbit of the marked point, and carries a transitive action.

Unproved conclusions:

- The full point stabilizer, full-action faithfulness/primitivity, sextic geometry, full J₁ order and simplicity remain open. The number 1,596 is an orbit cardinality, not the group order.

### H normal form

[Atlas.Janko1.H_normal_form](../Atlas/Sporadic/Janko1/Local168.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-010-j1/original/scopes/scope-3d4b3e40b5459f501f4877c8/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-010-j1/original/scopes/scope-3d4b3e40b5459f501f4877c8/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.Local168](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.Local168/PROCESS.json)

### card H

[Atlas.Janko1.card_H](../Atlas/Sporadic/Janko1/Local168.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-010-j1/original/scopes/scope-3d4b3e40b5459f501f4877c8/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-010-j1/original/scopes/scope-3d4b3e40b5459f501f4877c8/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.Local168](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.Local168/PROCESS.json)

### card generatedWhitelawOrbit

[Atlas.Janko1.card_generatedWhitelawOrbit](../Atlas/Sporadic/Janko1/WhitelawSInvariant.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-7abe0a428bc97224d785350a/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-7abe0a428bc97224d785350a/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.WhitelawSInvariant](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.WhitelawSInvariant/PROCESS.json)

### card pqSubgroup

[Atlas.Janko1.card_pqSubgroup](../Atlas/Sporadic/Janko1/PQComplement.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-bf5283c6176b8b06a33ac0e6/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-bf5283c6176b8b06a33ac0e6/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.PQComplement](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.PQComplement/PROCESS.json)

### card signSubgroup

[Atlas.Janko1.card_signSubgroup](../Atlas/Sporadic/Janko1/SignGroup.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-010-j1/original/scopes/scope-d88a43afbebd69bce66857d0/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-010-j1/original/scopes/scope-d88a43afbebd69bce66857d0/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.SignGroup](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.SignGroup/PROCESS.json)

### card whitelawOrbit

[Atlas.Janko1.card_whitelawOrbit](../Atlas/Sporadic/Janko1/WhitelawExactCount.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-2c7c26b2d26e2a6b28f87ec1/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-2c7c26b2d26e2a6b28f87ec1/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.WhitelawExactCount](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.WhitelawExactCount/PROCESS.json)

### Exact Whitelaw point count

[Atlas.Janko1.card_whitelawPoints](../Atlas/Sporadic/Janko1/WhitelawExactCount.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-2c7c26b2d26e2a6b28f87ec1/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-2c7c26b2d26e2a6b28f87ec1/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.WhitelawExactCount](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.WhitelawExactCount/PROCESS.json)

### generated smul mem whitelawSet iff

[Atlas.Janko1.generated_smul_mem_whitelawSet_iff](../Atlas/Sporadic/Janko1/WhitelawSInvariant.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-7abe0a428bc97224d785350a/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-7abe0a428bc97224d785350a/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.WhitelawSInvariant](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.WhitelawSInvariant/PROCESS.json)

### whitelawOrbitDecomposition

[Atlas.Janko1.whitelawOrbitDecomposition](../Atlas/Sporadic/Janko1/WhitelawExactCount.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-2c7c26b2d26e2a6b28f87ec1/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-2c7c26b2d26e2a6b28f87ec1/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.WhitelawExactCount](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.WhitelawExactCount/PROCESS.json)

### whitelawPoints transitive

[Atlas.Janko1.whitelawPoints_transitive](../Atlas/Sporadic/Janko1/WhitelawSInvariant.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-7abe0a428bc97224d785350a/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-7abe0a428bc97224d785350a/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.WhitelawSInvariant](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.WhitelawSInvariant/PROCESS.json)

### whitelawSet eq generatedOrbit

[Atlas.Janko1.whitelawSet_eq_generatedOrbit](../Atlas/Sporadic/Janko1/WhitelawSInvariant.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-7abe0a428bc97224d785350a/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-005-j1/original/scopes/scope-7abe0a428bc97224d785350a/CHECKPOINT.json).

[Normal proof Atlas.Sporadic.Janko1.WhitelawSInvariant](../verification/2026-10-30-additions/normal/Atlas.Sporadic.Janko1.WhitelawSInvariant/PROCESS.json)

<a id="g2-binary-derived-and-split-extension"></a>

## Binary G₂ derived subgroup and split extension

Parameters: Derived-subgroup statements: arbitrary F with [Field F], [Finite F] and |F|=2. The sign-kernel and split-extension statements fix F=ZMod 2; they are not asserted for every presentation by a new transport theorem.

Proved scope:

- The literal binary derived subgroup is the long-root normal closure, has order 6,048 and index 2, and is perfect and nonabelian simple. In the fixed binary presentation it is the kernel of the actual line-sign map.
- The short-root involution supplies the actual complement C={1,rootF(1)}. Its sign map identifies C with the sign group; multiplication gives the internal semidirect equivalence H ⋊ C ≃ G with the inherited conjugation action.

Unproved conclusions:

- No equivalence to PSU₃(3), matching of the outside action with the F₉/F₃ involution, or full-group extension comparison is supplied.

### binarySplitExtension

[Atlas.G2.BinaryException.binarySplitExtension](../Atlas/Comparisons/Exceptional/G2Binary/SplitExtension.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6b0c3825afe391643204b792/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6b0c3825afe391643204b792/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.SplitExtension](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.SplitExtension/PROCESS.json)

### commutator eq lineSign kernel

[Atlas.G2.BinaryException.commutator_eq_lineSign_kernel](../Atlas/Comparisons/Exceptional/G2Binary/Derived.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-2bb4de5f0e13ec57c3faaf5d/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-2bb4de5f0e13ec57c3faaf5d/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.Derived](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.Derived/PROCESS.json)

### shortRootComplement

[Atlas.G2.BinaryException.shortRootComplement](../Atlas/Comparisons/Exceptional/G2Binary/SplitExtension.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6b0c3825afe391643204b792/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6b0c3825afe391643204b792/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.SplitExtension](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.SplitExtension/PROCESS.json)

### shortRootComplementEquivSigns

[Atlas.G2.BinaryException.shortRootComplementEquivSigns](../Atlas/Comparisons/Exceptional/G2Binary/SplitExtension.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6b0c3825afe391643204b792/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6b0c3825afe391643204b792/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.SplitExtension](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.SplitExtension/PROCESS.json)

### commutator card binary

[Atlas.G2.commutator_card_binary](../Atlas/Comparisons/Exceptional/G2Binary/FieldTransport.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.FieldTransport](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.FieldTransport/PROCESS.json)

### commutator eq longRootNormalClosure binary

[Atlas.G2.commutator_eq_longRootNormalClosure_binary](../Atlas/Comparisons/Exceptional/G2Binary/FieldTransport.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.FieldTransport](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.FieldTransport/PROCESS.json)

### commutator index binary

[Atlas.G2.commutator_index_binary](../Atlas/Comparisons/Exceptional/G2Binary/FieldTransport.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.FieldTransport](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.FieldTransport/PROCESS.json)

### commutator perfect binary

[Atlas.G2.commutator_perfect_binary](../Atlas/Comparisons/Exceptional/G2Binary/FieldTransport.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.FieldTransport](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.FieldTransport/PROCESS.json)

### commutator simple binary

[Atlas.G2.commutator_simple_binary](../Atlas/Comparisons/Exceptional/G2Binary/FieldTransport.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-6c31e1bd137ea8572f9f5132/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.FieldTransport](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.FieldTransport/PROCESS.json)

<a id="comparison-6048-marked-inputs"></a>

## Order-6,048 marked unitary and octonion inputs

Parameters: Unitary side: BaseThree=ZMod 3, FieldNine=QuadraticAlgebra BaseThree (-1) 0, extension degree 2, dimension 3 and conjugation x↦x³. Binary side: K=ZMod 2 and the actual long-root subgroup.

Proved scope:

- The 28 marked line transvections generate the actual special unitary group and their images generate the full-center projective quotient.
- The projective unitary group and binary long-root subgroup have separately faithful numbered 28-point actions. The actual octonion words and the independent PSU order 6,048 specialization are retained.

Unproved conclusions:

- The two numberings and equal orders do not identify or conjugate the two permutation images. Actual generator matching, an isomorphism and the full outside-action comparison remain open. The Final6048 namespace on the order lemma does not make it a final bridge.

### card fieldNine psu

[Atlas.Comparisons.G2Binary.Final6048.card_fieldNine_psu](../Atlas/Comparisons/Exceptional/G2Binary/FieldNineOrder.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-5362251ca60ccecd7792528b/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-5362251ca60ccecd7792528b/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.FieldNineOrder](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.FieldNineOrder/PROCESS.json)

### word4 apply

[Atlas.Comparisons.G2Binary.Matching6048.word4_apply](../Atlas/Comparisons/Exceptional/G2Binary/OctonionWords.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-1346c0116b1e8889be8fdec3/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-1346c0116b1e8889be8fdec3/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.OctonionWords](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.OctonionWords/PROCESS.json)

### word4 mem

[Atlas.Comparisons.G2Binary.Matching6048.word4_mem](../Atlas/Comparisons/Exceptional/G2Binary/OctonionWords.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-1346c0116b1e8889be8fdec3/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-1346c0116b1e8889be8fdec3/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.OctonionWords](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.OctonionWords/PROCESS.json)

### binaryRepresentation injective

[Atlas.Comparisons.G2Binary.Source6048.binaryRepresentation_injective](../Atlas/Comparisons/Exceptional/G2Binary/MarkedUnitaryGeneration.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-ca64423e2cdc9cece585edee/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-ca64423e2cdc9cece585edee/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration/PROCESS.json)

### projectiveRoots generate

[Atlas.Comparisons.G2Binary.Source6048.projectiveRoots_generate](../Atlas/Comparisons/Exceptional/G2Binary/MarkedUnitaryGeneration.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-ca64423e2cdc9cece585edee/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-ca64423e2cdc9cece585edee/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration/PROCESS.json)

### specialRoots generate

[Atlas.Comparisons.G2Binary.Source6048.specialRoots_generate](../Atlas/Comparisons/Exceptional/G2Binary/MarkedUnitaryGeneration.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-ca64423e2cdc9cece585edee/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-ca64423e2cdc9cece585edee/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration/PROCESS.json)

### unitaryRepresentation injective

[Atlas.Comparisons.G2Binary.Source6048.unitaryRepresentation_injective](../Atlas/Comparisons/Exceptional/G2Binary/MarkedUnitaryGeneration.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-ca64423e2cdc9cece585edee/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-006-g2-binary/original/scopes/scope-ca64423e2cdc9cece585edee/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.G2Binary.MarkedUnitaryGeneration/PROCESS.json)

<a id="ree-three-source-and-coordinate-action"></a>

## Small Ree parameter 3: source structure and coordinate action

Parameters: F : Type*, [Field F], [Finite F], [CharP F 3], hF : Nat.card F = 3; m=0. The coordinate set is Option (F × F × F).

Proved scope:

- The original seven-dimensional Ree source has order 1,512, Borel order 54, and a faithful preprimitive action on 28 points.
- Four actual source elements generate the model. Its explicit coordinate action is faithful and agrees with the retained inverse-matrix action convention.

Unproved conclusions:

- The characteristic-three source and characteristic-two semilinear target are distinct constructions. No source-to-target homomorphism/isomorphism or source-derived order 504, simplicity or PSL₂(8) identification is supplied.

### coordinateAction

[Atlas.Comparisons.ReeThree.Boundary.coordinateAction](../Atlas/Comparisons/Exceptional/ReeThree/BoundaryAction.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction/PROCESS.json)

### coordinateAction coherence

[Atlas.Comparisons.ReeThree.Boundary.coordinateAction_coherence](../Atlas/Comparisons/Exceptional/ReeThree/BoundaryAction.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction/PROCESS.json)

### coordinateAction injective

[Atlas.Comparisons.ReeThree.Boundary.coordinateAction_injective](../Atlas/Comparisons/Exceptional/ReeThree/BoundaryAction.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction/PROCESS.json)

### coordinates card

[Atlas.Comparisons.ReeThree.Boundary.coordinates_card](../Atlas/Comparisons/Exceptional/ReeThree/BoundaryAction.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction/PROCESS.json)

### model generated by four

[Atlas.Comparisons.ReeThree.Boundary.model_generated_by_four](../Atlas/Comparisons/Exceptional/ReeThree/BoundaryAction.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-af2f68290d13070581390cc2/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.BoundaryAction/PROCESS.json)

### smallParameter borel order

[Atlas.ReeG2.smallParameter_borel_order](../Atlas/LinearGroups/ReeG2/SmallParameter.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeG2.SmallParameter](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeG2.SmallParameter/PROCESS.json)

### smallParameter faithful

[Atlas.ReeG2.smallParameter_faithful](../Atlas/LinearGroups/ReeG2/SmallParameter.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeG2.SmallParameter](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeG2.SmallParameter/PROCESS.json)

### smallParameter order

[Atlas.ReeG2.smallParameter_order](../Atlas/LinearGroups/ReeG2/SmallParameter.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeG2.SmallParameter](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeG2.SmallParameter/PROCESS.json)

### smallParameter point count

[Atlas.ReeG2.smallParameter_point_count](../Atlas/LinearGroups/ReeG2/SmallParameter.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeG2.SmallParameter](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeG2.SmallParameter/PROCESS.json)

### smallParameter primitive

[Atlas.ReeG2.smallParameter_primitive](../Atlas/LinearGroups/ReeG2/SmallParameter.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-799a6919488aa095af5982c6/CHECKPOINT.json).

[Normal proof Atlas.LinearGroups.ReeG2.SmallParameter](../verification/2026-10-30-additions/normal/Atlas.LinearGroups.ReeG2.SmallParameter/PROCESS.json)

<a id="ree-three-independent-semilinear-target"></a>

## Order-504 comparison: independent semilinear target

Parameters: Finite fields F,K with [Algebra F K], |F|=2 and Module.finrank F K=3, so |K|=8.

Proved scope:

- The independent target PSL₂(K) ⋊ Gal(K/F) has order 1,512. Its literal derived subgroup is the included PSL₂(K) factor, of order 504 and simple. Coefficient-field automorphisms act faithfully on that factor.

Unproved conclusions:

- The internal equivalence from PSL₂(K) to the target derived subgroup does not compare this target to the characteristic-three Ree source. The source-to-target and source-derived identifications remain open.

### fieldAction injective

[Atlas.Comparisons.ReeThree.fieldAction_injective](../Atlas/Comparisons/Exceptional/ReeThree/FieldActionFaithful.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.FieldActionFaithful](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.FieldActionFaithful/PROCESS.json)

### linearFactorEquivDerived

[Atlas.Comparisons.ReeThree.linearFactorEquivDerived](../Atlas/Comparisons/Exceptional/ReeThree/SemilinearTarget.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget/PROCESS.json)

### semilinear card

[Atlas.Comparisons.ReeThree.semilinear_card](../Atlas/Comparisons/Exceptional/ReeThree/SemilinearTarget.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget/PROCESS.json)

### semilinear commutator

[Atlas.Comparisons.ReeThree.semilinear_commutator](../Atlas/Comparisons/Exceptional/ReeThree/SemilinearTarget.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget/PROCESS.json)

### semilinear derived card

[Atlas.Comparisons.ReeThree.semilinear_derived_card](../Atlas/Comparisons/Exceptional/ReeThree/SemilinearTarget.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget/PROCESS.json)

### semilinear derived simple

[Atlas.Comparisons.ReeThree.semilinear_derived_simple](../Atlas/Comparisons/Exceptional/ReeThree/SemilinearTarget.lean) · [Compiled evidence](../verification/2026-10-30-cache-audit/full-dependency-extraction.log.gz) · [Full audit](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/RESULT.json) · [Policy manifest](../verification/2026-10-30-additions/batches/batch-007-ree-three/original/scopes/scope-1f4861a11ad406dd965fc9c8/CHECKPOINT.json).

[Normal proof Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget](../verification/2026-10-30-additions/normal/Atlas.Comparisons.Exceptional.ReeThree.SemilinearTarget/PROCESS.json)

