# Comparison of the constructed ATLAS groups

The main interface is [Atlas/Comparisons.lean](Atlas/Comparisons.lean), included
by the normal `import Atlas` entry point. It proves:

**Two groups in the typed comparison registry are isomorphic if and only if
their normalized labels agree.** Consequently, different normalized labels give nonisomorphic
groups, including the cases where their orders agree.

The declaration is
`Atlas.Comparisons.Catalogue.isomorphic_iff_normalized_label_eq`.
Its arguments are two values of `Atlas.Comparisons.Catalogue.Entry`. It has no assumed order
formula, recognition theorem or comparison certificate. The corollary is
`Atlas.Comparisons.Catalogue.not_isomorphic_of_normalized_label_ne`.

## Scope and definitions

[CatalogueModels.lean](Atlas/Comparisons/CatalogueModels.lean) defines the
entries and their actual group carriers. It covers thirteen constructed
families: cyclic prime-order groups, alternating groups, PSL, PSU, B, C,
split D, minus D, G₂, F₄, triality ³D₄, Suzuki ²B₂ and small Ree ²G₂.
It also covers M₁₁, M₁₂, M₂₂, M₂₃, M₂₄, Co₁, Co₂, Co₃, McL, HS, Suz, J₂,
Fi₂₂, Fi₂₃, Fi₂₄′, Ru and Tits.

This typed registry is unchanged by the [E₆, E₇ and E₈ catalogue
integration](catalogue/REALIZATIONS.md). It has no constructors for those
new root-operator carriers, so they are outside the comparison theorem above.
Their separate construction, order and simplicity proofs do not assert an
isomorphism with another realization.

The family entries use the canonical simple parameter ranges and retain the
actual finite fields and field extensions. Different presentations of fields
of the same cardinality are compared by proved transport isomorphisms. The
Mathieu entries use the standard or explicit coordinate markings.
Lower-rank alternative presentations retain their separate existing comparison
interfaces; they are not extra constructors in this registry. Planned groups
and unfinished derived-group identifications are outside this theorem.

The exact registry ranges are:

| Family | Parameters |
|---|---|
| Cyclic, alternating | prime order p; degree n≥5, respectively |
| PSL_d(q) | d≥2, excluding (d,q)=(2,2),(2,3) |
| PSU_d(q) | d≥3, excluding (d,q)=(3,2) |
| B_r(q), C_r(q) | r≥2, excluding (r,q)=(2,2) |
| D_r⁺(q), D_r⁻(q) | r≥4 |
| G₂(q) | q≥3 |
| F₄(q), ³D₄(q) | q≥2 |
| ²B₂(q) | q=2^(2m+1), m≥1 |
| ²G₂(q) | q=3^(2m+1), m≥1 |

Here q is a finite-field cardinality. Unitary and minus entries retain a
quadratic extension, and triality entries retain a cubic extension.

Normalization identifies only proved isomorphisms:

Every row below is restricted to the admissible simple parameters above.

| Presentations | Common normalized label |
|---|---|
| PSL₂(4), PSL₂(5), A₅ | A₅ |
| PSL₃(2), PSL₂(7) | PSL₂(7) |
| PSL₂(9), A₆ | A₆ |
| PSL₄(2), A₈ | A₈ |
| PSU₄(2), PSp₄(3) | C₂(3) |
| B₂(q), C₂(q) | C₂(q) |
| Bᵣ(q), Cᵣ(q), even q and r≥3 | Cᵣ(q) |

## Comparisons between construction models

The root-operator Chevalley constructions coexist with the earlier matrix and
algebra models. The marked type-A comparison identifies its selected companion
with SL and its adjoint model with PSL. The
[completed type-C comparison](catalogue/REALIZATIONS.md)
similarly identifies the actual companion with Sp and the adjoint model with PSp,
through their full centers. Both signs of the simple-root generators are marked.
The type-C result holds over every finite field at rank r≥2, without a simplicity
assumption, including the binary rank-two case.

The [completed type-D comparison](catalogue/REALIZATIONS.md)
identifies the adjoint model with the existing projective split quadratic-form
group at every rank r≥4 over every finite field, including characteristics two
and three. The natural representation gives the actual marked map. The full
projective kernel and the scalar-character vector kernel are distinguished.

The [completed type-B comparison](catalogue/REALIZATIONS.md)
identifies the adjoint and existing odd quadratic models at every rank r≥2
over every finite field, including B₂(2). The actual spin-vector map is onto,
its kernel is the full center, and the simple-root markings are preserved.
Neither old nor new simplicity is used.

These are additional concrete equivalences; they do not replace the existing
registry carriers or extend the normalized-label theorem. The four A/B/C/D
realizations and their marked maps are now [registered and separately audited](catalogue/REALIZATIONS.md).
G₂ and F₄ model comparisons remain outside this completed upload checkpoint.

## Proof architecture

[CatalogueOrders.lean](Atlas/Comparisons/CatalogueOrders.lean) connects the
existing order theorems for the actual models to the independently developed
order arithmetic. [CatalogueCardinality.lean](Atlas/Comparisons/CatalogueCardinality.lean)
provides the uniform bridge for every entry.

[CatalogueNormalization.lean](Atlas/Comparisons/CatalogueNormalization.lean)
composes the existing explicit exceptional isomorphisms.
[CatalogueSameLabel.lean](Atlas/Comparisons/CatalogueSameLabel.lean) and
[SameFieldSize.lean](Atlas/Comparisons/SameFieldSize.lean) handle field transport.
Equal normalized labels therefore give actual multiplicative equivalences.

In the other direction, an isomorphism preserves cardinality. The proved
arithmetic classification leaves equal normalized labels or two exceptional
equal-order patterns. [CatalogueObstructions.lean](Atlas/Comparisons/CatalogueObstructions.lean)
excludes A₈ versus PSL₃(4) using the existing Sylow-subgroup obstruction, and
Bᵣ(q) versus Cᵣ(q), odd q and r≥3, using the proved involution-class discriminator.
Thus neither exceptional numerical collision becomes an identification.

## Comparator Reference/Solution

- [Reference.lean](verification/comparisons/Reference.lean) states the two requested propositions.
- [Solution.lean](verification/comparisons/Solution.lean) proves those propositions using the main interface.
- [comparator.json](verification/comparisons/comparator.json) selects both declarations and the three permitted foundational axioms.
- [Reproduction instructions](verification/INDEPENDENT_CHECKERS.md) describe preparation and independent replay.

This is a concrete-model contract. Its reference imports the model registry and
normalization definitions, not the final comparison theorem. Those shared
definitions and their transitive imports form the reference boundary; this is
not a mathlib-only existence contract. Reference proof holes are specification
placeholders, never solution dependencies. There are no definition holes or
reflexive comparisons of a theorem name with itself.

## Verification

The normal `Atlas` root build passed on 12 October 2026 (7,706 Lake jobs;
incremental build, including cached dependencies). The full audit manifest is
[comparison-catalogue-isomorphism.json](verification/checkpoints/comparison-catalogue-isomorphism.json).
The [dated audit result](verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019/RESULT.json)
passed for **58 declarations and 79,697 transitive dependency nodes**, including
type, instance and proof dependencies. Only `propext`, `Classical.choice` and
`Quot.sound` occurred as axioms; the audit found no forbidden proof dependencies.
The [source snapshot](verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019/SNAPSHOT.json)
records exact working-source hashes and pinned dependencies.

[Compiled signatures](verification/comparisons/THEOREM_STATEMENTS.txt) are extracted
verbatim from that audit, with implicit parameters and instances visible.
The contract Solution compiled separately. Contract consistency checks passed.
An incremental build and a transitive dependency audit are distinct from
independent Comparator replay.

The **latest attempt, 25 October 2026**, also remains incomplete: both
`AtlasComparison.main` and `AtlasComparison.nonisomorphic` stopped at the
9 GiB owned RSS-plus-swap cap. The [dated receipt](verification/existence/2026-10-25-draft/Catalogue-isomorphism/RESULT.json)
and [complete log](verification/existence/2026-10-25-draft/Catalogue-isomorphism/comparator-check.log.gz)
preserve this outcome and its exact inputs. It is neither a proof rejection nor a pass.
The [42 successful targets from that queue](verification/existence/RESULTS.md)
are the separate existence and strengthened contracts; they do not certify this aggregate replay.
