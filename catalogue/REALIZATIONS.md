# Constructions and identification certificates

This page distinguishes three questions and links the Lean proofs answering
them. Every identification is an actual group isomorphism between the stated
models. The full construction inventory follows the comparison guide.

| Question | Where to look |
|---|---|
| Do two constructions of the same group agree? | [Models of the same group](#same-group) |
| Which different family labels describe isomorphic groups? | [Isomorphisms between families](#between-families) |
| How are all remaining pairs distinguished? | [One general certificate, orders and invariants](#remaining-pairs) |

**Coverage:** the general comparison theorem covers 13 families, all 16
completed sporadic groups and Tits, on its exact simple parameter ranges.
The catalogue also contains E₆/E₇/E₈ and additional construction models;
the [scope section](#comparison-scope) records which are outside that theorem.

<a id="same-group"></a>

## 1. Different models of the same group

| Group or family | Models | Domain | Identification certificate |
|---|---|---|---|
| [Aₙ(q)](#family-psl) | Matrix · Chevalley | rank n ≥ 1; every finite field | [Lean certificate](ISOMORPHISMS.md#chevalley-a-to-legacy-v1) |
| [Bₙ(q)](#family-b) | Quadratic · Chevalley | rank n ≥ 2; every finite field | [Lean certificate](ISOMORPHISMS.md#chevalley-b-to-legacy-v1) |
| [Cₙ(q)](#family-c) | Symplectic · Chevalley | rank n ≥ 2; every finite field | [Lean certificate](ISOMORPHISMS.md#chevalley-c-to-legacy-v1) |
| [Dₙ(q)](#family-d) | Quadratic · Chevalley | rank n ≥ 4; every finite field | [Lean certificate](ISOMORPHISMS.md#chevalley-d-to-legacy-v1) |
| [G₂(q)](#family-g2) | Octonion · Chevalley | Comparison scope recorded separately | [Local proof / export boundary](#comparison-scope) |
| [F₄(q)](#family-f4) | Albert · Chevalley | Comparison unfinished | [Open comparison](#comparison-scope) |

The four included A/B/C/D certificates apply even at nonsimple parameters
in their domains. They allow results about the original models to be
transported to the Chevalley models by composing the actual maps.

Different finite fields of the same size, and different presentations of
the required field extensions, are identified by
[a uniform field-transport certificate](../Atlas/Comparisons/CatalogueSameLabel.lean#L14)
for the models in the comparison registry. The
[individual transport interfaces](COMPARISONS.md#field-transport) retain
their precise field and extension hypotheses.

Each of the 16 sporadic entries currently advertises one construction in
this catalogue. The aggregate comparison theorem uses the specified Mathieu
coordinate markings. It does not assert a comparison with an additional
independently constructed permutation, lattice or other sporadic model.

<a id="between-families"></a>

## 2. Isomorphisms between different families

Here q is the base-field size, Bₙ/Cₙ/Dₙ use Lie rank, and the subscript in
PSL_d or PSU_d is the vector-space dimension. A_m without a field parameter
denotes an alternating group. The classical families use their actual
projective models.
These maps have the stated domains even when an endpoint is not simple;
they do not silently replace a full group by its derived subgroup.

### Uniform and low-rank identifications

| Identification | Parameters | Lean certificates |
|---|---|---|
| B₁(q) ≃ C₁(q) ≃ PSU₂(q) ≃ PSL₂(q) | Every finite q; the unitary scalar field has size q² | [B₁](../Atlas/Comparisons/Classical/Orthogonal.lean#L20) · [C₁](../Atlas/Comparisons/LowRank/Symplectic.lean#L9) · [PSU₂](../Atlas/Comparisons/LowRank/Unitary.lean#L10) |
| B₂(q) ≃ C₂(q) | Every finite q | [certificate](../Atlas/Comparisons/Classical/Orthogonal.lean#L29) |
| Bₙ(q) ≃ Cₙ(q) | Even q, n ≥ 1 | [certificate](../Atlas/Comparisons/Classical/Orthogonal.lean#L24) |
| D₂⁺(q) ≃ PSL₂(q) × PSL₂(q) | Every finite q; a product, outside the simple D-family range | [certificate](../Atlas/Comparisons/Classical/Orthogonal.lean#L37) |
| D₃⁺(q) ≃ PSL₄(q) | Every finite q | [certificate](../Atlas/Comparisons/Classical/Orthogonal.lean#L43) |
| ²D₂(q) ≃ PSL₂(q²) | Every finite q; PSL is over the quadratic extension | [certificate](../Atlas/Comparisons/LowRank/MinusOrthogonal.lean#L8) |
| ²D₃(q) ≃ PSU₄(q) | Every finite q; common quadratic extension | [certificate](../Atlas/Comparisons/LowRank/MinusOrthogonal.lean#L13) |

### Exceptional identifications at small parameters

| Order | Isomorphic groups | Lean certificates |
|---:|---|---|
| 60 | PSL₂(4) ≃ PSL₂(5) ≃ A₅ | [q = 4](../Atlas/Comparisons/Exceptional/Order60Four.lean#L21) · [q = 5](../Atlas/Comparisons/Exceptional/Order60Five.lean#L15) |
| 168 | PSL₃(2) ≃ PSL₂(7) | [certificate](../Atlas/Comparisons/Exceptional/Order168.lean#L38) |
| 360 | PSL₂(9) ≃ A₆ ≃ C₂(2)′ ≃ B₂(2)′ | [PSL₂/A₆](../Atlas/Comparisons/Exceptional/Order360.lean#L47) · [derived C₂](../Atlas/Comparisons/Exceptional/BinaryDerived.lean#L21) · [derived B₂](../Atlas/Comparisons/Exceptional/BinaryDerived.lean#L15) |
| 20,160 | PSL₄(2) ≃ D₃⁺(2) ≃ A₈ | [PSL₄/A₈](../Atlas/Comparisons/Exceptional/Order20160A8.lean#L88) · [D₃/A₈](../Atlas/Comparisons/Exceptional/Order20160A8.lean#L81) |
| 25,920 | PSU₄(2) ≃ ²D₃(2) ≃ C₂(3) ≃ B₂(3) | [PSU₄/C₂](../Atlas/Comparisons/Exceptional/Order25920.lean#L29) · [²D₃/C₂](../Atlas/Comparisons/Exceptional/Order25920.lean#L38) · [PSU₄/B₂](../Atlas/Comparisons/Exceptional/Order25920.lean#L45) |

At the excluded binary parameter the **full** groups B₂(2) and C₂(2)
are isomorphic to S₆, of order 720
([B₂ certificate](../Atlas/Comparisons/Small/BinarySymplectic.lean#L37),
[C₂ certificate](../Atlas/Comparisons/Small/BinarySymplectic.lean#L33)). Their derived subgroups
are the order-360 groups above. PSL₃(4), although also of order 20,160,
is separated from A₈ below.

The [complete interface index](COMPARISONS.md#between-families) includes
the compositions, arbitrary-field versions and canonical-field wrappers.

<a id="remaining-pairs"></a>

## 3. All remaining pairs: one certificate, orders and invariants

**Within the comparison theorem's stated scope, different normalized labels
imply nonisomorphic groups.** A normalized label records the family and
parameters after the proved identifications above have been applied.
The single certificate covering all such pairs is
[not_isomorphic_of_normalized_label_ne](../Atlas/Comparisons.lean#L59).
Its parent theorem,
[isomorphic_iff_normalized_label_eq](../Atlas/Comparisons.lean#L52),
proves both directions: isomorphism holds exactly when normalized labels agree.

The certificate combines the following two ways of separating groups.

### Different orders

The group-order bridge
[card](../Atlas/Comparisons/CatalogueCardinality.lean#L29)
proves the exact order of every model in the comparison registry. The
arithmetic theorem
[catalogue_orders_distinct](../Atlas/OrderArithmetic/Classification.lean#L55)
proves unequal orders whenever normalized labels differ and the pair is
outside the two exceptional patterns below. This is uniform in the
admissible ranks and field sizes, not a bounded numerical search.

[not_isomorphic_of_card_ne](../Atlas/Comparisons/Cardinality.lean#L9)
converts unequal orders into nonisomorphism; the combined registry-level
certificate is
[not_isomorphic_of_not_collision](../Atlas/Comparisons/CatalogueCardinality.lean#L50).
The [complete order-collision theorem](../Atlas/OrderArithmetic/Classification.lean)
proves that no further equal-order patterns occur in this scope.

In particular, the 16 completed sporadic groups and Tits have pairwise
different orders, and their orders differ from all admissible values of
the 13 families in this comparison registry. They are therefore covered
by the same order and nonisomorphism certificates.

### Equal orders, separated by one invariant

| Nonisomorphic groups | Domain and common order | Separating invariant | Lean certificates |
|---|---|---|---|
| Bₙ(q), Cₙ(q) | Odd q, n ≥ 3; their proved order formulas agree | Number of conjugacy classes of involutions: n versus ⌊n/2⌋ + 1 | [equal order](../Atlas/Comparisons/Classical/OrthogonalOrder.lean#L10) · [counts](../Atlas/Comparisons/Classical/OrthogonalInvolutions.lean#L15) · [nonisomorphism](../Atlas/Comparisons/Classical/OrthogonalInvolutions.lean#L21) |
| A₈ ≃ PSL₄(2), PSL₃(4) | Both order 20,160 | Center of a Sylow-2 subgroup: order 2 versus order 4 | [equal order](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L31) · [PSL certificate](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L13) · [A₈ certificate](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L22) |

The invariants are themselves preserved by isomorphism:
[involution-class invariance](../Atlas/GroupTheory/InvolutionClasses.lean#L45)
and [Sylow-center invariance](../Atlas/GroupTheory/SylowCenterInvariant.lean#L19).
[One combined obstruction certificate](../Atlas/Comparisons/CatalogueObstructions.lean#L60)
handles both exceptional patterns, including field transport and reversal
of the two endpoints. Rank two and even-characteristic B/C pairs belong
to the isomorphism table, not this obstruction table.

<a id="comparison-scope"></a>

## Scope, remaining gaps and verification

The aggregate theorem covers Cₚ, A_m, PSL, PSU, B, C, D⁺, D⁻, G₂, F₄,
³D₄, ²B₂ and ²G₂, together with all 16 completed sporadic groups and Tits.
Its [exact simple parameter ranges and model definitions](../COMPARISON.md#scope-and-definitions)
remain part of the statement. The low-rank and derived-group maps above
are additional interfaces; they are not additional registry constructors.

| Outside the aggregate theorem or exported comparison certificates | Present status |
|---|---|
| E₆, E₇, E₈ | Their actual models have separate Lean order and simplicity proofs, but the comparison registry and its exhaustive order-collision theorem do not include them. No blanket nonisomorphism result involving these families is asserted here. |
| Chevalley G₂ versus Octonion G₂ | A marked equivalence has ten passed local audit scopes; its final preservation/registration and source export are outside this review snapshot. The exported comparison theorem uses the Octonion model. |
| Chevalley F₄ versus Albert F₄ | The identification is unfinished. The exported comparison theorem uses the Albert model. |
| G₂(2)′ versus PSU₃(3), order 6,048 | The derived-group bridge is unfinished; equality of orders is not a certificate of isomorphism. |
| ²G₂(3)′ versus PSL₂(8), order 504 | The derived-group bridge is unfinished; the full small-parameter group must remain distinct from its derived subgroup. |

E₆/E₇/E₈ order formulas can be used with the general unequal-cardinality
lemma once a particular inequality has been proved. Having the formulas
alone does not extend the exhaustive comparison theorem to these families.

The aggregate theorem has a passed
[full dependency audit](../verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019/RESULT.json)
and [verbatim compiled statements](../verification/comparisons/THEOREM_STATEMENTS.txt).
Its two independent Comparator replays remain memory-stopped, as recorded
in the [dated receipt](../verification/existence/2026-10-25-draft/Catalogue-isomorphism/RESULT.json).
The [four invariant contracts](../verification/existence/RESULTS.md) passed
separately. Their success does not turn the aggregate replay into a pass.

<a id="construction-inventory"></a>

## Construction inventory

The 33 completed entries retain all 39 displayed models, including the six
additional Chevalley constructions. Open a group name for its model definitions,
orders, simplicity domains and construction-identification certificates.

| Entry | Models |
|---|---|
| [Cₚ](#family-cyclic) | [Residues](../CATALOGUE.md#family-cyclic-legacy) |
| [Aₙ](#family-alternating) | [Permutation](../CATALOGUE.md#family-alternating-legacy) |
| [Aₙ(q)](#family-psl) | [Matrix](../CATALOGUE.md#family-psl-matrix) · [Chevalley](../CATALOGUE.md#family-psl-chevalley) |
| [²Aₙ(q)](#family-psu) | [Hermitian](../CATALOGUE.md#family-psu-legacy) |
| [Bₙ(q)](#family-b) | [Quadratic](../CATALOGUE.md#family-b-quadratic) · [Chevalley](../CATALOGUE.md#family-b-chevalley) |
| [²B₂(q)](#family-suzuki) | [Matrix](../CATALOGUE.md#family-suzuki-legacy) |
| [Cₙ(q)](#family-c) | [Symplectic](../CATALOGUE.md#family-c-symplectic) · [Chevalley](../CATALOGUE.md#family-c-chevalley) |
| [Dₙ(q)](#family-d) | [Quadratic](../CATALOGUE.md#family-d-quadratic) · [Chevalley](../CATALOGUE.md#family-d-chevalley) |
| [²Dₙ(q)](#family-2d) | [Quadratic](../CATALOGUE.md#family-2d-legacy) |
| [³D₄(q)](#family-3d4) | [Triality](../CATALOGUE.md#family-3d4-legacy) |
| [E₆(q)](#family-e6) | [Chevalley](../CATALOGUE.md#family-e6-chevalley) |
| [E₇(q)](#family-e7) | [Chevalley](../CATALOGUE.md#family-e7-chevalley) |
| [E₈(q)](#family-e8) | [Chevalley](../CATALOGUE.md#family-e8-chevalley) |
| [F₄(q)](#family-f4) | [Albert](../CATALOGUE.md#family-f4-albert) · [Chevalley](../CATALOGUE.md#family-f4-chevalley) |
| [²F₄(2)′ (Tits)](#exceptional-tits) | [Lattice](../CATALOGUE.md#exceptional-tits-legacy) |
| [G₂(q)](#family-g2) | [Octonion](../CATALOGUE.md#family-g2-octonion) · [Chevalley](../CATALOGUE.md#family-g2-chevalley) |
| [²G₂(q)](#family-reeg2) | [Matrix](../CATALOGUE.md#family-reeg2-legacy) |
| [M₁₁](#sporadic-m11) | [Golay](../CATALOGUE.md#sporadic-m11-legacy) |
| [M₁₂](#sporadic-m12) | [Golay](../CATALOGUE.md#sporadic-m12-legacy) |
| [M₂₂](#sporadic-m22) | [Golay](../CATALOGUE.md#sporadic-m22-legacy) |
| [M₂₃](#sporadic-m23) | [Golay](../CATALOGUE.md#sporadic-m23-legacy) |
| [M₂₄](#sporadic-m24) | [Golay](../CATALOGUE.md#sporadic-m24-legacy) |
| [Co₁](#sporadic-co1) | [Leech](../CATALOGUE.md#sporadic-co1-legacy) |
| [Co₂](#sporadic-co2) | [Leech](../CATALOGUE.md#sporadic-co2-legacy) |
| [Co₃](#sporadic-co3) | [Leech](../CATALOGUE.md#sporadic-co3-legacy) |
| [McL](#sporadic-mcl) | [Leech](../CATALOGUE.md#sporadic-mcl-legacy) |
| [HS](#sporadic-hs) | [Leech](../CATALOGUE.md#sporadic-hs-legacy) |
| [Suz](#sporadic-suz) | [Eisenstein](../CATALOGUE.md#sporadic-suz-legacy) |
| [J₂](#sporadic-j2) | [Icosian](../CATALOGUE.md#sporadic-j2-legacy) |
| [Fi₂₂](#sporadic-fi22) | [Rays](../CATALOGUE.md#sporadic-fi22-legacy) |
| [Fi₂₃](#sporadic-fi23) | [Rays](../CATALOGUE.md#sporadic-fi23-legacy) |
| [Fi₂₄′](#sporadic-fi24prime) | [Rays](../CATALOGUE.md#sporadic-fi24prime-legacy) |
| [Ru](#sporadic-ru) | [Lattice](../CATALOGUE.md#sporadic-ru-legacy) |

<a id="family-cyclic"></a>

## Cₚ

<a id="family-cyclic-legacy"></a>

### Original concrete model

Multiplicative (ZMod p)

Parameters: p prime; card theorem m>0; simple iff m prime

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Families.Cyclic.Model`](../Atlas/Families/Cyclic/Basic.lean#L7) |
| finite | [`Atlas.Families.Cyclic.finite`](../Atlas/Families/Cyclic/Basic.lean#L12) |
| order | [`Atlas.Families.Cyclic.card`](../Atlas/Families/Cyclic/Basic.lean#L16) |
| simple | [`Atlas.Families.Cyclic.isSimpleGroup`](../Atlas/Families/Cyclic/Basic.lean#L40) |
| commutative | [`Atlas.Families.Cyclic.commutative`](../Atlas/Families/Cyclic/Basic.lean#L20) |

No general recognition theorem claimed by this entry


<a id="family-alternating"></a>

## Aₙ

<a id="family-alternating-legacy"></a>

### Original concrete model

alternatingGroup (Fin n)

Parameters: n>=5 for nonabelian simplicity; A3 cyclic simple; A4 not simple; n<=2 trivial

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Families.Alternating.Model`](../Atlas/Families/Alternating/Basic.lean#L7) |
| finite | [`Atlas.Families.Alternating.finite`](../Atlas/Families/Alternating/Basic.lean#L11) |
| order | [`Atlas.Families.Alternating.card_factorial`](../Atlas/Families/Alternating/Basic.lean#L23) |
| simple | [`Atlas.Families.Alternating.isSimpleGroup`](../Atlas/Families/Alternating/Basic.lean#L39) |

No general recognition theorem claimed by this entry


<a id="family-psl"></a>

## Aₙ(q)

<a id="family-psl-matrix"></a>

### Projective special-linear matrix model

SL_n(F)/center(SL_n(F))

Parameters: F arbitrary finite field; n>=2; simple iff (n,|F|) not (2,2),(2,3); prime-power existence p prime f>=1

| Interface | Lean declaration and source |
|---|---|
| model | [`Matrix.ProjectiveSpecialLinearGroup`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean) |
| finite | [`Atlas.finite_psl`](../Atlas/LinearGroups/ProjectiveSpecialLinear.lean#L143) |
| order | [`Atlas.card_psl_factor`](../Atlas/LinearGroups/ProjectiveSpecialLinear.lean#L190) |
| simple | [`Atlas.psl_simple_iff`](../Atlas/LinearGroups/PSLFamily.lean#L27) |

<a id="family-psl-chevalley"></a>

### Chevalley root-operator model

The actual root-generated elementary adjoint group, with inherited operations and faithful adjoint action. The selected simply connected companion is a distinct cover; no replacement occurs at nonsimple parameters.

Parameters: K an arbitrary finite field; q = Nat.card K; r >= 1; every finite characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Catalogue.A`](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean#L13) |
| finite | [`Atlas.Chevalley.Catalogue.A_finite`](../Atlas/LinearGroups/Chevalley/Catalogue/ACFinite.lean#L7) |
| order | [`Atlas.Chevalley.Catalogue.A_order`](../Atlas/LinearGroups/Chevalley/Catalogue/ACOrder.lean#L9) |
| center | [`Atlas.Chevalley.Catalogue.A_center`](../Atlas/LinearGroups/Chevalley/Catalogue/ACCenter.lean#L8) |
| simple | [`Atlas.Chevalley.Catalogue.A_simple`](../Atlas/LinearGroups/Chevalley/Catalogue/ACSimple.lean#L14) |
| exceptions | [`Atlas.Chevalley.Catalogue.A_exceptions`](../Atlas/LinearGroups/Chevalley/Catalogue/ACExceptions.lean#L9) |

Simplicity range: K an arbitrary finite field; q = Nat.card K; r >= 1; every finite characteristic; excluding (r,q)=(1,2),(1,3) for simplicity.

Separate property audits: [finite](../verification/runs/chevalley-catalogue-a-finite/20261018T160128-105) · [order](../verification/runs/chevalley-catalogue-a-order/20261018T160235-105) · [center](../verification/runs/chevalley-catalogue-a-center/20261018T160348-105) · [simple](../verification/runs/chevalley-catalogue-a-simple/20261018T160458-105) · [exceptions](../verification/runs/chevalley-catalogue-a-exceptions/20261018T160714-105).

Dated concrete-model contract: [AtlasExistenceChevalley.A](../verification/existence/2026-10-25-draft/Chevalley-A/Solution.lean) · [exact specification](../verification/existence/2026-10-25-draft/Chevalley-A/Challenge.lean) · [checker receipt](../verification/existence/2026-10-25-draft/Chevalley-A/RESULT.json).

### Isomorphism between these constructions

[`Atlas.Chevalley.Catalogue.A_identification`](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L24) is the actual multiplicative equivalence.

Domain: K an arbitrary finite field; q = Nat.card K; r >= 1; every finite characteristic.

[Lean isomorphism certificate](../catalogue/ISOMORPHISMS.md#chevalley-a-to-legacy-v1) gives the verbatim compiled type, both carriers, the parameter map and [full dependency audit](../verification/runs/chevalley-a-to-legacy-v1/20261018T160827-105).

The existing order/simplicity dependency diagram and line counts describe the projective special-linear matrix model. They are not counts for both constructions combined.

No general recognition theorem claimed by this entry


<a id="family-psu"></a>

## ²Aₙ(q)

<a id="family-psu-legacy"></a>

### Original concrete model

Actual standard Hermitian SU_n(K/F), quotiented by its proved full norm-one scalar center

Parameters: F finite with q=|F|, K/F an actual quadratic extension; n is matrix dimension; stable catalogue: n>=3 and (n,q)!=(3,2)

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Unitary.PSU`](../Atlas/LinearGroups/Unitary/Basic.lean#L41) |
| finite | [`Atlas.Unitary.finite_psu`](../Atlas/LinearGroups/Unitary/Basic.lean#L48) |
| order | [`Atlas.Unitary.card_psu_factor`](../Atlas/LinearGroups/Unitary/ProjectiveOrder.lean#L40) |
| simple | [`Atlas.Unitary.simple_of_good`](../Atlas/LinearGroups/Unitary/Family.lean#L13) |

Direct finite Hermitian matrix construction, with actual field transport and SL graph-field fixed-subgroup identification; no order recognition, CFSG or projective fixed-point assertion


<a id="family-b"></a>

## Bₙ(q)

<a id="family-b-quadratic"></a>

### Quadratic-form model

Actual scalar quotient of the Siegel-generated subgroup of the quadratic form Q(x,y,z)=sum x_i*y_i+z^2; identified with the determinant/spinor kernel in odd characteristic and the full orthogonal group in characteristic two

Parameters: n is Lie rank, natural dimension 2*n+1; F arbitrary finite field, q=|F|; n>=1, every characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Orthogonal.B`](../Atlas/LinearGroups/Orthogonal/BFamily.lean#L9) |
| finite | [`Atlas.Orthogonal.B_finite`](../Atlas/LinearGroups/Orthogonal/BFamily.lean#L27) |
| order | [`Atlas.Orthogonal.B_card_all_rank`](../Atlas/LinearGroups/Orthogonal/BAllRanks.lean#L28) |
| simple | [`Atlas.Orthogonal.B_simple_all_rank`](../Atlas/LinearGroups/Orthogonal/BAllRanksConstruction.lean#L34) |

<a id="family-b-chevalley"></a>

### Chevalley root-operator model

The actual root-generated elementary adjoint group, with inherited operations and faithful adjoint action; the carrier is unchanged at B2(F2). The selected simply connected companion is a distinct cover.

Parameters: K an arbitrary finite field; q = Nat.card K; n : Nat, rank r = n+1 >= 2; every finite characteristic, including B2(F2)

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Catalogue.B`](../Atlas/LinearGroups/Chevalley/Catalogue/BConstruction.lean#L10) |
| finite | [`Atlas.Chevalley.Catalogue.B_finite`](../Atlas/LinearGroups/Chevalley/Catalogue/BFinite.lean#L7) |
| order | [`Atlas.Chevalley.Catalogue.B_order`](../Atlas/LinearGroups/Chevalley/Catalogue/BOrder.lean#L8) |
| center | [`Atlas.Chevalley.Catalogue.B_center`](../Atlas/LinearGroups/Chevalley/Catalogue/BCenter.lean#L8) |
| simple | [`Atlas.Chevalley.Catalogue.B_simple`](../Atlas/LinearGroups/Chevalley/Catalogue/BSimple.lean#L12) |
| exceptions | [`Atlas.Chevalley.Catalogue.B_exceptions`](../Atlas/LinearGroups/Chevalley/Catalogue/BExceptions.lean#L8) |

Simplicity range: K an arbitrary finite field; q = Nat.card K; n : Nat, rank r = n+1 >= 2; every finite characteristic; excluding (r,q)=(2,2) for simplicity (RootType.Good).

Separate property audits: [finite](../verification/runs/chevalley-catalogue-b-finite/20261018T164023-105) · [order](../verification/runs/chevalley-catalogue-b-order/20261018T164216-105) · [center](../verification/runs/chevalley-catalogue-b-center/20261018T164427-105) · [simple](../verification/runs/chevalley-catalogue-b-simple/20261018T164645-105) · [exceptions](../verification/runs/chevalley-catalogue-b-exceptions/20261018T165018-105).

Dated concrete-model contract: [AtlasExistenceChevalley.B](../verification/existence/2026-10-25-draft/Chevalley-B/Solution.lean) · [exact specification](../verification/existence/2026-10-25-draft/Chevalley-B/Challenge.lean) · [checker receipt](../verification/existence/2026-10-25-draft/Chevalley-B/RESULT.json).

### Isomorphism between these constructions

[`Atlas.Chevalley.Catalogue.B_identification`](../Atlas/LinearGroups/Chevalley/Catalogue/BIdentification.lean#L16) is the actual multiplicative equivalence.

Domain: K an arbitrary finite field; q = Nat.card K; n : Nat, rank r = n+1 >= 2; every finite characteristic, including B2(F2).

[Lean isomorphism certificate](../catalogue/ISOMORPHISMS.md#chevalley-b-to-legacy-v1) gives the verbatim compiled type, both carriers, the parameter map and [full dependency audit](../verification/runs/chevalley-b-to-legacy-v1/20261018T165216-105).

The existing order/simplicity dependency diagram and line counts describe the quadratic-form model. They are not counts for both constructions combined.

No general recognition theorem or classification of family coincidences is claimed


<a id="family-suzuki"></a>

## ²B₂(q)

<a id="family-suzuki-legacy"></a>

### Original concrete model

Actual subgroup of Sp4(F) generated by the explicit Tits-twisted root, torus and Weyl matrices

Parameters: F finite of characteristic 2, q=|F|=2^(2m+1); simple family m>=1, hence q>=8

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.SuzukiFamily.Group`](../Atlas/LinearGroups/SuzukiFamily/Model.lean#L35) |
| finite | [`Atlas.SuzukiFamily.finite_group`](../Atlas/LinearGroups/SuzukiFamily/Model.lean#L50) |
| order | [`Atlas.SuzukiFamily.card_group`](../Atlas/LinearGroups/SuzukiFamily/Order.lean#L9) |
| simple | [`Atlas.SuzukiFamily.simple_of_large`](../Atlas/LinearGroups/SuzukiFamily/Simplicity.lean#L19) |

Direct standard Suzuki matrix construction and faithful ovoid action; no abstract Chevalley theorem, CFSG or order recognition. Exceptional graph-field fixed-point characterization is not asserted


<a id="family-c"></a>

## Cₙ(q)

<a id="family-c-symplectic"></a>

### Symplectic matrix model

Carrier of Matrix.symplecticGroup (Fin n) F, quotiented by its actual center

Parameters: n is symplectic rank, dimension 2*n; F arbitrary finite field, q=|F|; simple exactly when (n=1 and q>3) or (n>=2 and (n,q)!=(2,2))

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Symplectic.PSp`](../Atlas/LinearGroups/Symplectic/Basic.lean#L16) |
| finite | [`Atlas.Symplectic.finite_psp`](../Atlas/LinearGroups/Symplectic/Basic.lean#L26) |
| order | [`Atlas.Symplectic.card_psp`](../Atlas/LinearGroups/Symplectic/ProjectiveOrder.lean#L19) |
| simple | [`Atlas.Symplectic.simple_of_good`](../Atlas/LinearGroups/Symplectic/Simplicity.lean#L14) |

<a id="family-c-chevalley"></a>

### Chevalley root-operator model

The actual root-generated elementary adjoint group, with inherited operations and faithful adjoint action. The selected simply connected companion is a distinct cover; no replacement occurs at nonsimple parameters.

Parameters: K an arbitrary finite field; q = Nat.card K; r >= 2; every finite characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Catalogue.C`](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean#L18) |
| finite | [`Atlas.Chevalley.Catalogue.C_finite`](../Atlas/LinearGroups/Chevalley/Catalogue/ACFinite.lean#L12) |
| order | [`Atlas.Chevalley.Catalogue.C_order`](../Atlas/LinearGroups/Chevalley/Catalogue/ACOrder.lean#L18) |
| center | [`Atlas.Chevalley.Catalogue.C_center`](../Atlas/LinearGroups/Chevalley/Catalogue/ACCenter.lean#L13) |
| simple | [`Atlas.Chevalley.Catalogue.C_simple`](../Atlas/LinearGroups/Chevalley/Catalogue/ACSimple.lean#L21) |
| exceptions | [`Atlas.Chevalley.Catalogue.C_exceptions`](../Atlas/LinearGroups/Chevalley/Catalogue/ACExceptions.lean#L15) |

Simplicity range: K an arbitrary finite field; q = Nat.card K; r >= 2; every finite characteristic; excluding (r,q)=(2,2) for simplicity.

Separate property audits: [finite](../verification/runs/chevalley-catalogue-c-finite/20261018T161215-105) · [order](../verification/runs/chevalley-catalogue-c-order/20261018T161342-105) · [center](../verification/runs/chevalley-catalogue-c-center/20261018T161519-105) · [simple](../verification/runs/chevalley-catalogue-c-simple/20261018T161656-105) · [exceptions](../verification/runs/chevalley-catalogue-c-exceptions/20261018T162002-105).

Dated concrete-model contract: [AtlasExistenceChevalley.C](../verification/existence/2026-10-25-draft/Chevalley-C/Solution.lean) · [exact specification](../verification/existence/2026-10-25-draft/Chevalley-C/Challenge.lean) · [checker receipt](../verification/existence/2026-10-25-draft/Chevalley-C/RESULT.json).

### Isomorphism between these constructions

[`Atlas.Chevalley.Catalogue.C_identification`](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L31) is the actual multiplicative equivalence.

Domain: K an arbitrary finite field; q = Nat.card K; r >= 2; every finite characteristic.

[Lean isomorphism certificate](../catalogue/ISOMORPHISMS.md#chevalley-c-to-legacy-v1) gives the verbatim compiled type, both carriers, the parameter map and [full dependency audit](../verification/runs/chevalley-c-to-legacy-v1/20261018T162154-105).

The existing order/simplicity dependency diagram and line counts describe the symplectic matrix model. They are not counts for both constructions combined.

Constructed symplectic family with its natural alternating form and actions; no CFSG or external recognition theorem assumed


<a id="family-d"></a>

## Dₙ(q)

<a id="family-d-quadratic"></a>

### Quadratic-form model

Actual scalar quotient of the Siegel-generated subgroup of the split quadratic form Q(x,y)=sum x_i*y_i; identified with the determinant/spinor kernel in odd characteristic and Dickson kernel in characteristic two

Parameters: n is Lie rank, natural dimension 2*n; F arbitrary finite field, q=|F|; n>=4, every characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Orthogonal.DPlus`](../Atlas/LinearGroups/Orthogonal/DFamily.lean#L13) |
| finite | [`Atlas.Orthogonal.DPlus_finite`](../Atlas/LinearGroups/Orthogonal/DFamily.lean#L42) |
| order | [`Atlas.Orthogonal.DPlus_card`](../Atlas/LinearGroups/Orthogonal/DFamily.lean#L56) |
| simple | [`Atlas.Orthogonal.DPlus_simple`](../Atlas/LinearGroups/Orthogonal/DConstruction.lean#L17) |

<a id="family-d-chevalley"></a>

### Chevalley root-operator model

The actual root-generated elementary adjoint group, with inherited operations and faithful adjoint action. The selected simply connected companion is a distinct cover, not this registered realization.

Parameters: K an arbitrary finite field; q = Nat.card K; r >= 4; every finite characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Catalogue.D`](../Atlas/LinearGroups/Chevalley/Catalogue/DConstruction.lean#L10) |
| finite | [`Atlas.Chevalley.Catalogue.D_finite`](../Atlas/LinearGroups/Chevalley/Catalogue/DFinite.lean#L7) |
| order | [`Atlas.Chevalley.Catalogue.D_order`](../Atlas/LinearGroups/Chevalley/Catalogue/DOrder.lean#L8) |
| center | [`Atlas.Chevalley.Catalogue.D_center`](../Atlas/LinearGroups/Chevalley/Catalogue/DCenter.lean#L8) |
| simple | [`Atlas.Chevalley.Catalogue.D_simple`](../Atlas/LinearGroups/Chevalley/Catalogue/DSimple.lean#L12) |
| exceptions | [`Atlas.Chevalley.Catalogue.D_exceptions`](../Atlas/LinearGroups/Chevalley/Catalogue/DExceptions.lean#L8) |

Simplicity range: K an arbitrary finite field; q = Nat.card K; r >= 4; every finite characteristic; RootType.Good holds (automatic for D over a finite field).

Separate property audits: [finite](../verification/runs/chevalley-catalogue-d-finite/20261018T162701-105) · [order](../verification/runs/chevalley-catalogue-d-order/20261018T162810-105) · [center](../verification/runs/chevalley-catalogue-d-center/20261018T162944-105) · [simple](../verification/runs/chevalley-catalogue-d-simple/20261018T163112-105) · [exceptions](../verification/runs/chevalley-catalogue-d-exceptions/20261018T163340-105).

Dated concrete-model contract: [AtlasExistenceChevalley.D](../verification/existence/2026-10-25-draft/Chevalley-D/Solution.lean) · [exact specification](../verification/existence/2026-10-25-draft/Chevalley-D/Challenge.lean) · [checker receipt](../verification/existence/2026-10-25-draft/Chevalley-D/RESULT.json).

### Isomorphism between these constructions

[`Atlas.Chevalley.Catalogue.D_identification`](../Atlas/LinearGroups/Chevalley/Catalogue/DIdentification.lean#L16) is the actual multiplicative equivalence.

Domain: K an arbitrary finite field; q = Nat.card K; r >= 4; every finite characteristic.

[Lean isomorphism certificate](../catalogue/ISOMORPHISMS.md#chevalley-d-to-legacy-v1) gives the verbatim compiled type, both carriers, the parameter map and [full dependency audit](../verification/runs/chevalley-d-to-legacy-v1/20261018T163507-105).

The existing order/simplicity dependency diagram and line counts describe the quadratic-form model. They are not counts for both constructions combined.

No general recognition theorem or classification of family coincidences is claimed


<a id="family-2d"></a>

## ²Dₙ(q)

<a id="family-2d-legacy"></a>

### Original concrete model

Actual hyperbolic planes plus quadratic-extension norm plane; intrinsic Omega equals Siegel-generated isometries, quotiented by its full scalar center

Parameters: F arbitrary finite field, q=|F|; K/F actual quadratic extension; n is half-dimension/Lie rank; stable simple family n>=4, every characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Orthogonal.DMinus`](../Atlas/LinearGroups/Orthogonal/Minus/Family.lean#L11) |
| finite | [`Atlas.Orthogonal.Minus.family_finite`](../Atlas/LinearGroups/Orthogonal/Minus/Family.lean#L15) |
| order | [`Atlas.Orthogonal.Minus.family_order`](../Atlas/LinearGroups/Orthogonal/Minus/Family.lean#L35) |
| simple | [`Atlas.Orthogonal.Minus.family_simple`](../Atlas/LinearGroups/Orthogonal/Minus/Family.lean#L21) |

Concrete quadratic-form model and kernel identification; no order recognition or graph-field fixed-point assertion


<a id="family-3d4"></a>

## ³D₄(q)

<a id="family-3d4-legacy"></a>

### Original concrete model

Actual subgroup of the split eight-dimensional orthogonal group over a cubic extension K/F, generated by four literal triality-folded root families

Parameters: F and K finite fields, Algebra F K, [K:F]=3; q=|F|, |K|=q^3; every prime power q>=2

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Triality.Group`](../Atlas/LinearGroups/Triality/FoldedGenerators.lean#L31) |
| finite | [`Atlas.Triality.finite_group`](../Atlas/LinearGroups/Triality/FoldedGenerators.lean#L58) |
| order | [`Atlas.Triality.card_group`](../Atlas/LinearGroups/Triality/Order.lean#L15) |
| simple | [`Atlas.Triality.simple`](../Atlas/LinearGroups/Triality/Simplicity.lean#L37) |

Direct pinned triality-folded matrix construction; no recognition from order. Full related-triple graph-field fixed-point comparison and generalized-hexagon axioms are not claimed


<a id="family-e6"></a>

## E₆(q)

<a id="family-e6-chevalley"></a>

### Chevalley root-operator model

The root-generated elementary adjoint subgroup of matrix units from the integral Geck root operators, with its inherited group operations and faithful adjoint action. The simply connected group is a separate cover, not this carrier.

Parameters: K an arbitrary finite field; q = Nat.card K; rank = 6; every finite characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Catalogue.E6`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean#L14) |
| finite | [`Atlas.Chevalley.Catalogue.E6_finite`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesFinite.lean#L7) |
| order | [`Atlas.Chevalley.Catalogue.E6_order`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesOrder.lean#L10) |
| simple | [`Atlas.Chevalley.Catalogue.E6_simple`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesSimple.lean#L8) |

First completed anchor of this family; the historical intrinsic realization remains planned and no identification with it is asserted


<a id="family-e7"></a>

## E₇(q)

<a id="family-e7-chevalley"></a>

### Chevalley root-operator model

The root-generated elementary adjoint subgroup of matrix units from the integral Geck root operators, with its inherited group operations and faithful adjoint action. The simply connected group is a separate cover, not this carrier.

Parameters: K an arbitrary finite field; q = Nat.card K; rank = 7; every finite characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Catalogue.E7`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean#L29) |
| finite | [`Atlas.Chevalley.Catalogue.E7_finite`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesFinite.lean#L12) |
| order | [`Atlas.Chevalley.Catalogue.E7_order`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesOrder.lean#L18) |
| simple | [`Atlas.Chevalley.Catalogue.E7_simple`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesSimple.lean#L14) |

First completed anchor of this family; the historical intrinsic realization remains planned and no identification with it is asserted


<a id="family-e8"></a>

## E₈(q)

<a id="family-e8-chevalley"></a>

### Chevalley root-operator model

The root-generated elementary adjoint subgroup of matrix units from the integral Geck root operators, with its inherited group operations and faithful adjoint action. The simply connected group is a separate cover, not this carrier.

Parameters: K an arbitrary finite field; q = Nat.card K; rank = 8; every finite characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Catalogue.E8`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean#L44) |
| finite | [`Atlas.Chevalley.Catalogue.E8_finite`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesFinite.lean#L17) |
| order | [`Atlas.Chevalley.Catalogue.E8_order`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesOrder.lean#L26) |
| simple | [`Atlas.Chevalley.Catalogue.E8_simple`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesSimple.lean#L20) |

First completed anchor of this family; the historical intrinsic realization remains planned and no identification with it is asserted


<a id="family-f4"></a>

## F₄(q)

<a id="family-f4-albert"></a>

### Split-Albert model

Full stabilizer of the integral cubic polynomial and distinguished unit in the marked 27-dimensional split Albert space

Parameters: F is an arbitrary finite field, q=|F|; every prime power q>=2, including characteristics 2 and 3

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.F4.Model`](../Atlas/LinearGroups/F4/Basic.lean#L8) |
| finite | [`Atlas.F4.finite_model`](../Atlas/LinearGroups/F4/Basic.lean#L19) |
| order | [`Atlas.F4.card_Model`](../Atlas/LinearGroups/F4/Order.lean#L25) |
| simple | [`Atlas.F4.isSimple`](../Atlas/LinearGroups/F4/Simplicity.lean#L12) |

<a id="family-f4-chevalley"></a>

### Chevalley root-operator model

Root-generated adjoint operator group; same carrier at nonsimple parameters. The simply connected group is a separate related cover, not this realization.

Parameters: K an arbitrary finite field; q = Nat.card K; rank = 4; every finite characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Model .F4`](../Atlas/LinearGroups/Chevalley/Models.lean) |
| order | [`Atlas.Chevalley.model_F4_card`](../Atlas/LinearGroups/Chevalley/ModelF4Order.lean#L24) |
| simple | [`Atlas.Chevalley.model_isSimpleGroup_of_good`](../Atlas/LinearGroups/Chevalley/ModelSimplicityGood.lean#L47) |

Dated concrete-model contract: [AtlasExistenceChevalley.F4](../verification/existence/2026-10-25-draft/Chevalley-F4/Solution.lean) · [exact specification](../verification/existence/2026-10-25-draft/Chevalley-F4/Challenge.lean) · [checker receipt](../verification/existence/2026-10-25-draft/Chevalley-F4/RESULT.json).

This contract proves order and simplicity of this explicit witness for every finite field, q ≥ 2. The realization registry still records its separate catalogue registration as pending.

### Isomorphism between these constructions

The isomorphism between the Chevalley and full split-Albert models remains unfinished. No certificate identifying them is claimed.

The existing order/simplicity dependency diagram and line counts describe the split-albert model. They are not counts for both constructions combined.

Concrete split-Albert/Dickson–Wilson construction; no abstract Chevalley theorem, CFSG, target-order recognition or assumed BN-pair


<a id="exceptional-tits"></a>

## ²F₄(2)′ (Tits)

<a id="exceptional-tits-legacy"></a>

### Original concrete model

Actual derived subgroup of the distinguished-cross stabilizer in the constructed projective Conway–Wales lattice group

Parameters: Fixed exceptional derived-Ree/Tits group ²F₄(2)′, constructed as the commutator subgroup of the inherited cross stabilizer

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Tits.Model`](../Atlas/Tits/LocalGroups.lean#L92) |
| finite | [`Atlas.Tits.finite`](../Atlas/Tits/Construction.lean#L11) |
| order | [`Atlas.Tits.card`](../Atlas/Tits/Order.lean#L20) |
| simple | [`Atlas.Tits.isSimpleGroup`](../Atlas/Tits/Simplicity.lean#L12) |

Direct inherited lattice-stabilizer construction; no comparison with an independently constructed Ree matrix group or recognition from order is asserted


<a id="family-g2"></a>

## G₂(q)

<a id="family-g2-octonion"></a>

### Split-octonion model

Full group of linear multiplication-preserving automorphisms of the uniform eight-coordinate split octonion algebra

Parameters: F is an arbitrary finite field, q=|F|, including characteristics 2 and 3; simple exactly when q>2

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.G2.Model`](../Atlas/LinearGroups/G2/Basic.lean#L8) |
| finite | [`Atlas.G2.finite_model`](../Atlas/LinearGroups/G2/Basic.lean#L24) |
| order | [`Atlas.G2.card_Model`](../Atlas/LinearGroups/G2/Order.lean#L18) |
| simple | [`Atlas.G2.isSimple`](../Atlas/LinearGroups/G2/Simplicity.lean#L9) |

<a id="family-g2-chevalley"></a>

### Chevalley root-operator model

Root-generated adjoint operator group; same carrier at nonsimple parameters. The simply connected group is a separate related cover, not this realization.

Parameters: K an arbitrary finite field; q = Nat.card K; rank = 2; every finite characteristic

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Chevalley.Model .G2`](../Atlas/LinearGroups/Chevalley/Models.lean) |
| order | [`Atlas.Chevalley.model_G2_card`](../Atlas/LinearGroups/Chevalley/ModelG2Order.lean#L22) |
| simple | [`Atlas.Chevalley.model_isSimpleGroup_of_good`](../Atlas/LinearGroups/Chevalley/ModelSimplicityGood.lean#L47) |

Dated concrete-model contract: [AtlasExistenceChevalley.G2](../verification/existence/2026-10-25-draft/Chevalley-G2/Solution.lean) · [exact specification](../verification/existence/2026-10-25-draft/Chevalley-G2/Challenge.lean) · [checker receipt](../verification/existence/2026-10-25-draft/Chevalley-G2/RESULT.json).

This contract proves order and simplicity of this explicit witness for q > 2 for simplicity (the same model exists at q = 2). The realization registry still records its separate catalogue registration as pending.

### Isomorphism between these constructions

The research note records a marked Chevalley–octonion equivalence with ten passed local audit scopes, but its final preservation/registration and source export are outside this review snapshot. This review therefore supplies both model contracts, without claiming that their isomorphism certificate is included.

The existing order/simplicity dependency diagram and line counts describe the split-octonion model. They are not counts for both constructions combined.

Concrete Dickson/Wilson octonion construction; no general Chevalley, CFSG, order-recognition or PSU3(3) comparison theorem assumed


<a id="family-reeg2"></a>

## ²G₂(q)

<a id="family-reeg2-legacy"></a>

### Original concrete model

Actual subgroup of GL7(F) generated by the explicit Tits-twisted alpha, beta, gamma, torus and Weyl matrices

Parameters: F finite of characteristic 3, q=|F|=3^(2m+1), m>=1; the public family starts at q=27

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.ReeG2.Model`](../Atlas/LinearGroups/ReeG2/Generators.lean#L134) |
| finite | [`Atlas.ReeG2.finite_model`](../Atlas/LinearGroups/TypeReeG2.lean#L27) |
| order | [`Atlas.ReeG2.order`](../Atlas/LinearGroups/ReeG2/Order.lean#L25) |
| simple | [`Atlas.ReeG2.simple`](../Atlas/LinearGroups/ReeG2/Simplicity.lean#L13) |

Direct standard Ree matrix construction and explicit injective map into the existing split-octonion G2 model; no CFSG, abstract Chevalley/Ree theorem or order recognition


<a id="sporadic-m11"></a>

## M₁₁

<a id="sporadic-m11-legacy"></a>

### Original concrete model

point stabilizer in full Golay dodecad stabilizer

Parameters: any constructed Golay dodecad D and a point of D; canonical standard choices also provided

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Mathieu11.Model`](../Atlas/Sporadic/Mathieu11.lean#L10) |
| finite | [`Atlas.Sporadic.Mathieu11.finite`](../Atlas/Sporadic/Mathieu11.lean#L15) |
| order | [`Atlas.Sporadic.Mathieu11.card`](../Atlas/Sporadic/Mathieu11.lean#L16) |
| simple | [`Atlas.Sporadic.Mathieu11.isSimpleGroup`](../Atlas/Sporadic/Mathieu11.lean#L19) |

No general recognition theorem claimed by this entry


<a id="sporadic-m12"></a>

## M₁₂

<a id="sporadic-m12-legacy"></a>

### Original concrete model

full Golay dodecad stabilizer

Parameters: any constructed Golay dodecad D; canonical standard choice provided

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Mathieu12.Model`](../Atlas/Sporadic/Mathieu12.lean#L10) |
| finite | [`Atlas.Sporadic.Mathieu12.finite`](../Atlas/Sporadic/Mathieu12.lean#L16) |
| order | [`Atlas.Sporadic.Mathieu12.card`](../Atlas/Sporadic/Mathieu12.lean#L17) |
| simple | [`Atlas.Sporadic.Mathieu12.isSimpleGroup`](../Atlas/Sporadic/Mathieu12.lean#L20) |

No general recognition theorem claimed by this entry


<a id="sporadic-m22"></a>

## M₂₂

<a id="sporadic-m22-legacy"></a>

### Original concrete model

two coordinate pointwise stabilizer in full Golay automorphism group

Parameters: any coordinate a and distinct coordinate b

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Mathieu22.Model`](../Atlas/Sporadic/Mathieu22.lean#L6) |
| finite | [`Atlas.Sporadic.Mathieu22.finite`](../Atlas/Sporadic/Mathieu22.lean#L15) |
| order | [`Atlas.Sporadic.Mathieu22.card`](../Atlas/Sporadic/Mathieu22.lean#L18) |
| simple | [`Atlas.Sporadic.Mathieu22.isSimpleGroup`](../Atlas/Sporadic/Mathieu22Simple.lean#L6) |

No general recognition theorem claimed by this entry


<a id="sporadic-m23"></a>

## M₂₃

<a id="sporadic-m23-legacy"></a>

### Original concrete model

coordinate stabilizer in full Golay automorphism group

Parameters: any coordinate a

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Mathieu23.Model`](../Atlas/Sporadic/Mathieu23.lean#L12) |
| finite | [`Atlas.Sporadic.Mathieu23.finite`](../Atlas/Sporadic/Mathieu23.lean#L23) |
| order | [`Atlas.Sporadic.Mathieu23.card`](../Atlas/Sporadic/Mathieu23.lean#L25) |
| simple | [`Atlas.Sporadic.Mathieu23.isSimpleGroup`](../Atlas/Sporadic/Mathieu23.lean#L38) |

No general recognition theorem claimed by this entry


<a id="sporadic-m24"></a>

## M₂₄

<a id="sporadic-m24-legacy"></a>

### Original concrete model

full permutation automorphism group of constructed binary Golay code

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Mathieu24.Model`](../Atlas/Sporadic/Mathieu24.lean#L13) |
| finite | [`Atlas.Sporadic.Mathieu24.finite`](../Atlas/Sporadic/Mathieu24.lean#L16) |
| order | [`Atlas.Sporadic.Mathieu24.card`](../Atlas/Sporadic/Mathieu24Construction.lean#L17) |
| simple | [`Atlas.Sporadic.Mathieu24.isSimpleGroup`](../Atlas/Sporadic/Mathieu24Construction.lean#L19) |

No general recognition theorem claimed by this entry


<a id="sporadic-co1"></a>

## Co₁

<a id="sporadic-co1-legacy"></a>

### Original concrete model

full Golay Leech isometry group modulo its center {±1}

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Conway1.Model`](../Atlas/Sporadic/Conway1.lean#L9) |
| finite | [`Atlas.Sporadic.Conway1.finite`](../Atlas/Sporadic/Conway1.lean#L22) |
| order | [`Atlas.Sporadic.Conway1.card`](../Atlas/Sporadic/Conway1.lean#L24) |
| simple | [`Atlas.Sporadic.Conway1.isSimpleGroup`](../Atlas/Sporadic/Conway1.lean#L30) |

No general recognition theorem claimed by this entry


<a id="sporadic-co2"></a>

## Co₂

<a id="sporadic-co2-legacy"></a>

### Original concrete model

actual norm-four vector stabilizer in full Leech isometry group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Conway2.Model`](../Atlas/Sporadic/Conway2.lean#L12) |
| finite | [`Atlas.Sporadic.Conway2.finite`](../Atlas/Sporadic/Conway2.lean#L16) |
| order | [`Atlas.Sporadic.Conway2.card`](../Atlas/Sporadic/Conway2.lean#L18) |
| simple | [`Atlas.Sporadic.Conway2.isSimpleGroup`](../Atlas/Sporadic/Conway2Simplicity.lean#L7) |

No general recognition theorem claimed by this entry


<a id="sporadic-co3"></a>

## Co₃

<a id="sporadic-co3-legacy"></a>

### Original concrete model

actual norm-six vector stabilizer in full Leech isometry group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Conway3.Model`](../Atlas/Sporadic/Conway3.lean#L13) |
| finite | [`Atlas.Sporadic.Conway3.finite`](../Atlas/Sporadic/Conway3.lean#L15) |
| order | [`Atlas.Sporadic.Conway3.card`](../Atlas/Sporadic/Conway3.lean#L57) |
| simple | [`Atlas.Sporadic.Conway3.isSimpleGroup`](../Atlas/Sporadic/Conway3Simplicity.lean#L5) |

No general recognition theorem claimed by this entry


<a id="sporadic-mcl"></a>

## McL

<a id="sporadic-mcl-legacy"></a>

### Original concrete model

actual pointwise Leech 2-2-3 triangle stabilizer

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.McLaughlin.Model`](../Atlas/Sporadic/McLaughlin.lean#L8) |
| finite | [`Atlas.Sporadic.McLaughlin.finite`](../Atlas/Sporadic/McLaughlin.lean#L18) |
| order | [`Atlas.Sporadic.McLaughlin.card`](../Atlas/Sporadic/McLaughlin.lean#L20) |
| simple | [`Atlas.Sporadic.McLaughlin.isSimpleGroup`](../Atlas/Sporadic/McLaughlinSimplicity.lean#L10) |

No general recognition theorem claimed by this entry


<a id="sporadic-hs"></a>

## HS

<a id="sporadic-hs-legacy"></a>

### Original concrete model

actual pointwise Leech 2-3-3 triangle stabilizer

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.HigmanSims.Model`](../Atlas/Sporadic/HigmanSimsConfiguration.lean#L9) |
| finite | [`Atlas.Sporadic.HigmanSims.finite`](../Atlas/Sporadic/HigmanSimsLattice.lean#L16) |
| order | [`Atlas.Sporadic.HigmanSims.card`](../Atlas/Sporadic/HigmanSims.lean#L12) |
| simple | [`Atlas.Sporadic.HigmanSims.isSimpleGroup`](../Atlas/Sporadic/HigmanSimsSimplicity.lean#L16) |

No general recognition theorem claimed by this entry


<a id="sporadic-suz"></a>

## Suz

<a id="sporadic-suz-legacy"></a>

### Original concrete model

actual Eisenstein Leech centralizer modulo six scalar isometries

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Suzuki.Model`](../Atlas/Sporadic/Suzuki.lean#L12) |
| finite | [`Atlas.Sporadic.Suzuki.finite`](../Atlas/Sporadic/Suzuki.lean#L31) |
| order | [`Atlas.Sporadic.Suzuki.card`](../Atlas/Sporadic/Suzuki.lean#L33) |
| simple | [`Atlas.Sporadic.Suzuki.isSimpleGroup`](../Atlas/Sporadic/Suzuki.lean#L39) |

No general recognition theorem claimed by this entry


<a id="sporadic-j2"></a>

## J₂

<a id="sporadic-j2-legacy"></a>

### Original concrete model

actual icosian linear group modulo its center of order two

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Janko2.Model`](../Atlas/Sporadic/Janko2.lean#L11) |
| finite | [`Atlas.Sporadic.Janko2.finite`](../Atlas/Sporadic/Janko2.lean#L35) |
| order | [`Atlas.Sporadic.Janko2.card`](../Atlas/Sporadic/Janko2.lean#L37) |
| simple | [`Atlas.Sporadic.Janko2.isSimpleGroup`](../Atlas/Sporadic/Janko2.lean#L43) |

No general recognition theorem claimed by this entry


<a id="sporadic-fi22"></a>

## Fi₂₂

<a id="sporadic-fi22-legacy"></a>

### Original concrete model

commuting-pair centralizer quotient in actual full ray group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Fischer22.Model`](../Atlas/Sporadic/Fischer22.lean#L11) |
| finite | [`Atlas.Sporadic.Fischer22.finite`](../Atlas/Sporadic/Fischer22.lean#L19) |
| order | [`Atlas.Sporadic.Fischer22.card`](../Atlas/Sporadic/Fischer22.lean#L20) |
| simple | [`Atlas.Sporadic.Fischer22.simple`](../Atlas/Sporadic/Fischer22.lean#L23) |

No general recognition theorem claimed by this entry


<a id="sporadic-fi23"></a>

## Fi₂₃

<a id="sporadic-fi23-legacy"></a>

### Original concrete model

singleton centralizer quotient in actual full ray group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Fischer23.Model`](../Atlas/Sporadic/Fischer23.lean#L11) |
| finite | [`Atlas.Sporadic.Fischer23.finite`](../Atlas/Sporadic/Fischer23.lean#L19) |
| order | [`Atlas.Sporadic.Fischer23.card`](../Atlas/Sporadic/Fischer23.lean#L20) |
| simple | [`Atlas.Sporadic.Fischer23.simple`](../Atlas/Sporadic/Fischer23.lean#L23) |

No general recognition theorem claimed by this entry


<a id="sporadic-fi24prime"></a>

## Fi₂₄′

<a id="sporadic-fi24prime-legacy"></a>

### Original concrete model

positive subgroup of actual Conway-Parker root-generated ray group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Fischer24Prime.Model`](../Atlas/Sporadic/Fischer24Prime.lean#L9) |
| finite | [`Atlas.Sporadic.Fischer24Prime.finite`](../Atlas/Sporadic/Fischer24Prime.lean#L15) |
| order | [`Atlas.Sporadic.Fischer24Prime.card`](../Atlas/Sporadic/Fischer24Prime.lean#L16) |
| simple | [`Atlas.Sporadic.Fischer24Prime.simple`](../Atlas/Sporadic/Fischer24Prime.lean#L18) |

No general recognition theorem claimed by this entry


<a id="sporadic-ru"></a>

## Ru

<a id="sporadic-ru-legacy"></a>

### Original concrete model

full Gaussian automorphism group of the explicit Conway–Wales lattice, modulo its scalar units

Parameters: fixed constructed lattice stabilizer quotient; no supplied order or simplicity certificate

| Interface | Lean declaration and source |
|---|---|
| model | [`Atlas.Sporadic.Rudvalis.Model`](../Atlas/Sporadic/Rudvalis.lean#L10) |
| finite | [`Atlas.Sporadic.Rudvalis.finite`](../Atlas/Sporadic/Rudvalis.lean#L20) |
| order | [`Atlas.Sporadic.Rudvalis.card`](../Atlas/Sporadic/Rudvalis.lean#L22) |
| simple | [`Atlas.Sporadic.Rudvalis.isSimpleGroup`](../Atlas/Sporadic/Rudvalis.lean#L28) |

Direct Conway–Wales lattice construction; no general recognition or classification uniqueness theorem claimed

