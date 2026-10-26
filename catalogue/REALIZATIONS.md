# Constructions and identification certificates

Each result below has a **Lean statement** and a separate **verification certificate**.
Certificates record passed full dependency audits; independent Comparator results
are identified separately. Here q is a finite-field size, B/C/D subscripts are
Lie ranks, and PSL/PSU subscripts are dimensions. A_m denotes an alternating group.

<a id="same-group"></a>

## 1. Isomorphisms between different models

| Models and domain | Lean statement | Verification certificate |
|---|---|---|
| Aₙ(q): Matrix ≃ Chevalley; n ≥ 1, every finite q | [A_identification](ISOMORPHISMS.md#chevalley-a-to-legacy-v1 "Atlas.Chevalley.Catalogue.A_identification") | [Passed audit (18 Oct)](../verification/runs/chevalley-a-to-legacy-v1/20261018T160827-105/CERTIFICATE.md) |
| Bₙ(q): Quadratic ≃ Chevalley; n ≥ 2, every finite q | [B_identification](ISOMORPHISMS.md#chevalley-b-to-legacy-v1 "Atlas.Chevalley.Catalogue.B_identification") | [Passed audit (18 Oct)](../verification/runs/chevalley-b-to-legacy-v1/20261018T165216-105/CERTIFICATE.md) |
| Cₙ(q): Symplectic ≃ Chevalley; n ≥ 2, every finite q | [C_identification](ISOMORPHISMS.md#chevalley-c-to-legacy-v1 "Atlas.Chevalley.Catalogue.C_identification") | [Passed audit (18 Oct)](../verification/runs/chevalley-c-to-legacy-v1/20261018T162154-105/CERTIFICATE.md) |
| Dₙ(q): Quadratic ≃ Chevalley; n ≥ 4, every finite q | [D_identification](ISOMORPHISMS.md#chevalley-d-to-legacy-v1 "Atlas.Chevalley.Catalogue.D_identification") | [Passed audit (18 Oct)](../verification/runs/chevalley-d-to-legacy-v1/20261018T163507-105/CERTIFICATE.md) |
| Same family and parameters over different finite fields or extension presentations of the same sizes; within the comparison registry | [statement](../Atlas/Comparisons/CatalogueSameLabel.lean#L14 "Atlas.Comparisons.Catalogue.same_label_equiv") | [Passed audit (12 Oct)](../verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019/CERTIFICATE.md) |

The A/B/C/D maps also cover nonsimple parameters in the stated domains.
**G₂:** the Chevalley–Octonion map has ten passed local audit scopes, but its
final preservation/registration and source export are outside this snapshot.
**F₄:** the Chevalley–Albert map remains unfinished. Neither is presented as
an included identification certificate. Each sporadic entry currently has
one advertised construction; the comparison registry fixes the Mathieu markings.

<a id="construction-inventory"></a>

<details>
<summary>Reference: all 39 construction models (33 catalogue entries)</summary>

Definitions and full parameter ranges are retained in the [catalogue](../CATALOGUE.md).

<a id="family-cyclic"></a>

**[Cₚ](../CATALOGUE.md#family-cyclic)**

<a id="family-cyclic-legacy"></a>

- Residues: [`Atlas.Families.Cyclic.Model`](../Atlas/Families/Cyclic/Basic.lean#L7)

<a id="family-alternating"></a>

**[Aₙ](../CATALOGUE.md#family-alternating)**

<a id="family-alternating-legacy"></a>

- Permutation: [`Atlas.Families.Alternating.Model`](../Atlas/Families/Alternating/Basic.lean#L7)

<a id="family-psl"></a>

**[Aₙ(q)](../CATALOGUE.md#family-psl)**

<a id="family-psl-matrix"></a>

- Matrix: [`Matrix.ProjectiveSpecialLinearGroup`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean)
<a id="family-psl-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Catalogue.A`](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean#L13)

<a id="family-psu"></a>

**[²Aₙ(q)](../CATALOGUE.md#family-psu)**

<a id="family-psu-legacy"></a>

- Hermitian: [`Atlas.Unitary.PSU`](../Atlas/LinearGroups/Unitary/Basic.lean#L41)

<a id="family-b"></a>

**[Bₙ(q)](../CATALOGUE.md#family-b)**

<a id="family-b-quadratic"></a>

- Quadratic: [`Atlas.Orthogonal.B`](../Atlas/LinearGroups/Orthogonal/BFamily.lean#L9)
<a id="family-b-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Catalogue.B`](../Atlas/LinearGroups/Chevalley/Catalogue/BConstruction.lean#L10)

<a id="family-suzuki"></a>

**[²B₂(q)](../CATALOGUE.md#family-suzuki)**

<a id="family-suzuki-legacy"></a>

- Matrix: [`Atlas.SuzukiFamily.Group`](../Atlas/LinearGroups/SuzukiFamily/Model.lean#L35)

<a id="family-c"></a>

**[Cₙ(q)](../CATALOGUE.md#family-c)**

<a id="family-c-symplectic"></a>

- Symplectic: [`Atlas.Symplectic.PSp`](../Atlas/LinearGroups/Symplectic/Basic.lean#L16)
<a id="family-c-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Catalogue.C`](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean#L18)

<a id="family-d"></a>

**[Dₙ(q)](../CATALOGUE.md#family-d)**

<a id="family-d-quadratic"></a>

- Quadratic: [`Atlas.Orthogonal.DPlus`](../Atlas/LinearGroups/Orthogonal/DFamily.lean#L13)
<a id="family-d-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Catalogue.D`](../Atlas/LinearGroups/Chevalley/Catalogue/DConstruction.lean#L10)

<a id="family-2d"></a>

**[²Dₙ(q)](../CATALOGUE.md#family-2d)**

<a id="family-2d-legacy"></a>

- Quadratic: [`Atlas.Orthogonal.DMinus`](../Atlas/LinearGroups/Orthogonal/Minus/Family.lean#L11)

<a id="family-3d4"></a>

**[³D₄(q)](../CATALOGUE.md#family-3d4)**

<a id="family-3d4-legacy"></a>

- Triality: [`Atlas.Triality.Group`](../Atlas/LinearGroups/Triality/FoldedGenerators.lean#L31)

<a id="family-e6"></a>

**[E₆(q)](../CATALOGUE.md#family-e6)**

<a id="family-e6-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Catalogue.E6`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean#L14)

<a id="family-e7"></a>

**[E₇(q)](../CATALOGUE.md#family-e7)**

<a id="family-e7-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Catalogue.E7`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean#L29)

<a id="family-e8"></a>

**[E₈(q)](../CATALOGUE.md#family-e8)**

<a id="family-e8-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Catalogue.E8`](../Atlas/LinearGroups/Chevalley/Catalogue/ESeriesConstruction.lean#L44)

<a id="family-f4"></a>

**[F₄(q)](../CATALOGUE.md#family-f4)**

<a id="family-f4-albert"></a>

- Albert: [`Atlas.F4.Model`](../Atlas/LinearGroups/F4/Basic.lean#L8)
<a id="family-f4-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Model .F4`](../Atlas/LinearGroups/Chevalley/Models.lean)

<a id="exceptional-tits"></a>

**[²F₄(2)′ (Tits)](../CATALOGUE.md#exceptional-tits)**

<a id="exceptional-tits-legacy"></a>

- Lattice: [`Atlas.Tits.Model`](../Atlas/Tits/LocalGroups.lean#L92)

<a id="family-g2"></a>

**[G₂(q)](../CATALOGUE.md#family-g2)**

<a id="family-g2-octonion"></a>

- Octonion: [`Atlas.G2.Model`](../Atlas/LinearGroups/G2/Basic.lean#L8)
<a id="family-g2-chevalley"></a>

- Chevalley: [`Atlas.Chevalley.Model .G2`](../Atlas/LinearGroups/Chevalley/Models.lean)

<a id="family-reeg2"></a>

**[²G₂(q)](../CATALOGUE.md#family-reeg2)**

<a id="family-reeg2-legacy"></a>

- Matrix: [`Atlas.ReeG2.Model`](../Atlas/LinearGroups/ReeG2/Generators.lean#L134)

<a id="sporadic-m11"></a>

**[M₁₁](../CATALOGUE.md#sporadic-m11)**

<a id="sporadic-m11-legacy"></a>

- Golay: [`Atlas.Sporadic.Mathieu11.Model`](../Atlas/Sporadic/Mathieu11.lean#L10)

<a id="sporadic-m12"></a>

**[M₁₂](../CATALOGUE.md#sporadic-m12)**

<a id="sporadic-m12-legacy"></a>

- Golay: [`Atlas.Sporadic.Mathieu12.Model`](../Atlas/Sporadic/Mathieu12.lean#L10)

<a id="sporadic-m22"></a>

**[M₂₂](../CATALOGUE.md#sporadic-m22)**

<a id="sporadic-m22-legacy"></a>

- Golay: [`Atlas.Sporadic.Mathieu22.Model`](../Atlas/Sporadic/Mathieu22.lean#L6)

<a id="sporadic-m23"></a>

**[M₂₃](../CATALOGUE.md#sporadic-m23)**

<a id="sporadic-m23-legacy"></a>

- Golay: [`Atlas.Sporadic.Mathieu23.Model`](../Atlas/Sporadic/Mathieu23.lean#L12)

<a id="sporadic-m24"></a>

**[M₂₄](../CATALOGUE.md#sporadic-m24)**

<a id="sporadic-m24-legacy"></a>

- Golay: [`Atlas.Sporadic.Mathieu24.Model`](../Atlas/Sporadic/Mathieu24.lean#L13)

<a id="sporadic-co1"></a>

**[Co₁](../CATALOGUE.md#sporadic-co1)**

<a id="sporadic-co1-legacy"></a>

- Leech: [`Atlas.Sporadic.Conway1.Model`](../Atlas/Sporadic/Conway1.lean#L9)

<a id="sporadic-co2"></a>

**[Co₂](../CATALOGUE.md#sporadic-co2)**

<a id="sporadic-co2-legacy"></a>

- Leech: [`Atlas.Sporadic.Conway2.Model`](../Atlas/Sporadic/Conway2.lean#L12)

<a id="sporadic-co3"></a>

**[Co₃](../CATALOGUE.md#sporadic-co3)**

<a id="sporadic-co3-legacy"></a>

- Leech: [`Atlas.Sporadic.Conway3.Model`](../Atlas/Sporadic/Conway3.lean#L13)

<a id="sporadic-mcl"></a>

**[McL](../CATALOGUE.md#sporadic-mcl)**

<a id="sporadic-mcl-legacy"></a>

- Leech: [`Atlas.Sporadic.McLaughlin.Model`](../Atlas/Sporadic/McLaughlin.lean#L8)

<a id="sporadic-hs"></a>

**[HS](../CATALOGUE.md#sporadic-hs)**

<a id="sporadic-hs-legacy"></a>

- Leech: [`Atlas.Sporadic.HigmanSims.Model`](../Atlas/Sporadic/HigmanSimsConfiguration.lean#L9)

<a id="sporadic-suz"></a>

**[Suz](../CATALOGUE.md#sporadic-suz)**

<a id="sporadic-suz-legacy"></a>

- Eisenstein: [`Atlas.Sporadic.Suzuki.Model`](../Atlas/Sporadic/Suzuki.lean#L12)

<a id="sporadic-j2"></a>

**[J₂](../CATALOGUE.md#sporadic-j2)**

<a id="sporadic-j2-legacy"></a>

- Icosian: [`Atlas.Sporadic.Janko2.Model`](../Atlas/Sporadic/Janko2.lean#L11)

<a id="sporadic-fi22"></a>

**[Fi₂₂](../CATALOGUE.md#sporadic-fi22)**

<a id="sporadic-fi22-legacy"></a>

- Rays: [`Atlas.Sporadic.Fischer22.Model`](../Atlas/Sporadic/Fischer22.lean#L11)

<a id="sporadic-fi23"></a>

**[Fi₂₃](../CATALOGUE.md#sporadic-fi23)**

<a id="sporadic-fi23-legacy"></a>

- Rays: [`Atlas.Sporadic.Fischer23.Model`](../Atlas/Sporadic/Fischer23.lean#L11)

<a id="sporadic-fi24prime"></a>

**[Fi₂₄′](../CATALOGUE.md#sporadic-fi24prime)**

<a id="sporadic-fi24prime-legacy"></a>

- Rays: [`Atlas.Sporadic.Fischer24Prime.Model`](../Atlas/Sporadic/Fischer24Prime.lean#L9)

<a id="sporadic-ru"></a>

**[Ru](../CATALOGUE.md#sporadic-ru)**

<a id="sporadic-ru-legacy"></a>

- Lattice: [`Atlas.Sporadic.Rudvalis.Model`](../Atlas/Sporadic/Rudvalis.lean#L10)

</details>

<a id="between-families"></a>

## 2. Exceptional isomorphisms

These identify different family labels: low-rank or characteristic-dependent
coincidences, and isolated small-parameter coincidences. A prime (′) denotes
the derived subgroup; full groups and derived subgroups are separate endpoints.
In unitary and minus-orthogonal notation q is the base-field size and the
scalar field has size q².

| Isomorphism and domain | Lean statements | Verification certificates |
|---|---|---|
| B₁(q) ≃ C₁(q) ≃ PSU₂(q) ≃ PSL₂(q); every finite q | [B₁](../Atlas/Comparisons/Classical/Orthogonal.lean#L20 "Atlas.Comparisons.Classical.b1EquivA1") · [C₁](../Atlas/Comparisons/LowRank/Symplectic.lean#L9 "Atlas.Comparisons.Classical.c1EquivA1") · [PSU₂](../Atlas/Comparisons/LowRank/Unitary.lean#L10 "Atlas.Comparisons.Classical.psuTwoEquivA1") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) · [Passed audit (27 Sep)](../verification/runs/comparison-low-rank-exposure/20260927T093630-6/CERTIFICATE.md) |
| B₂(q) ≃ C₂(q); every finite q | [statement](../Atlas/Comparisons/Classical/Orthogonal.lean#L29 "Atlas.Comparisons.Classical.b2EquivC2") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) |
| Bₙ(q) ≃ Cₙ(q); even q, n ≥ 1 | [statement](../Atlas/Comparisons/Classical/Orthogonal.lean#L24 "Atlas.Comparisons.Classical.evenBEquivC") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) |
| D₂⁺(q) ≃ PSL₂(q) × PSL₂(q); every finite q (a product) | [statement](../Atlas/Comparisons/Classical/Orthogonal.lean#L37 "Atlas.Comparisons.Classical.d2EquivProduct") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) |
| D₃⁺(q) ≃ PSL₄(q); every finite q | [statement](../Atlas/Comparisons/Classical/Orthogonal.lean#L43 "Atlas.Comparisons.Classical.d3EquivA3") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) |
| ²D₂(q) ≃ PSL₂(q²); every finite q | [statement](../Atlas/Comparisons/LowRank/MinusOrthogonal.lean#L8 "Atlas.Comparisons.Classical.dMinusTwoEquivA1") | [Passed audit (27 Sep)](../verification/runs/comparison-low-rank-exposure/20260927T093630-6/CERTIFICATE.md) |
| ²D₃(q) ≃ PSU₄(q); every finite q | [statement](../Atlas/Comparisons/LowRank/MinusOrthogonal.lean#L13 "Atlas.Comparisons.Classical.dMinusThreeEquivUnitary") | [Passed audit (27 Sep)](../verification/runs/comparison-low-rank-exposure/20260927T093630-6/CERTIFICATE.md) |
| PSL₂(4) ≃ PSL₂(5) ≃ A₅; order 60 | [q = 4](../Atlas/Comparisons/Exceptional/Order60Four.lean#L21 "Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5") · [q = 5](../Atlas/Comparisons/Exceptional/Order60Five.lean#L15 "Atlas.Comparisons.Exceptional.psl2Card5EquivAlt5") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) |
| PSL₃(2) ≃ PSL₂(7); order 168 | [statement](../Atlas/Comparisons/Exceptional/Order168.lean#L38 "Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) |
| PSL₂(9) ≃ A₆ ≃ C₂(2)′ ≃ B₂(2)′; order 360 | [PSL₂/A₆](../Atlas/Comparisons/Exceptional/Order360.lean#L47 "Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6") · [C₂′/A₆](../Atlas/Comparisons/Exceptional/BinaryDerived.lean#L21 "Atlas.Comparisons.Exceptional.c2BinaryDerivedEquivAlt6") · [B₂′/C₂′](../Atlas/Comparisons/Exceptional/BinaryDerived.lean#L15 "Atlas.Comparisons.Exceptional.b2BinaryDerivedEquivC2Derived") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) |
| B₂(2) ≃ C₂(2) ≃ S₆; full groups, order 720 | [B₂/S₆](../Atlas/Comparisons/Small/BinarySymplectic.lean#L37 "Atlas.Comparisons.Exceptional.b2Card2EquivSymmetric") · [C₂/S₆](../Atlas/Comparisons/Small/BinarySymplectic.lean#L33 "Atlas.Comparisons.Exceptional.c2Card2EquivSymmetric") | [Passed audit (27 Sep)](../verification/runs/comparison-low-rank-exposure/20260927T093630-6/CERTIFICATE.md) |
| PSL₄(2) ≃ D₃⁺(2) ≃ A₈; order 20,160 | [PSL₄/A₈](../Atlas/Comparisons/Exceptional/Order20160A8.lean#L88 "Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8") · [A₈/D₃](../Atlas/Comparisons/Exceptional/Order20160A8.lean#L81 "Atlas.Comparisons.Exceptional.alt8EquivD3Two") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) |
| PSU₄(2) ≃ ²D₃(2) ≃ C₂(3) ≃ B₂(3); order 25,920 | [PSU₄/C₂](../Atlas/Comparisons/Exceptional/Order25920.lean#L29 "Atlas.Comparisons.Exceptional.psu4Card2EquivPSp4Card3") · [²D₃/C₂](../Atlas/Comparisons/Exceptional/Order25920.lean#L38 "Atlas.Comparisons.Exceptional.dMinus3Card2EquivPSp4Card3") · [PSU₄/B₂](../Atlas/Comparisons/Exceptional/Order25920.lean#L45 "Atlas.Comparisons.Exceptional.psu4Card2EquivB2Card3") | [Passed audit (10 Oct)](../verification/runs/comparison-order25920-public/20261010T130445-1081507/CERTIFICATE.md) |

**Still open in this snapshot:** the bridges G₂(2)′ ≃ PSU₃(3) (order 6,048)
and ²G₂(3)′ ≃ PSL₂(8) (order 504). Their equal orders are not identification
certificates. The [complete statement index](COMPARISONS.md#between-families)
retains all compositions, canonical-field wrappers and full hypotheses.

<a id="remaining-pairs"></a>

## 3. Non-isomorphisms of all other cases

After the exceptional isomorphisms in Theme 2, the remaining distinct
normalized labels are separated by unequal orders or one of the two
invariants below. The order argument combines the proved cardinalities
of the constructed models with the uniform numerical classification.

| Non-isomorphism result and reason | Lean statements | Verification certificates |
|---|---|---|
| **Combined comparison theorem:** distinct normalized labels give nonisomorphic groups within its [specified registry](../COMPARISON.md#scope-and-definitions) | [statement](../Atlas/Comparisons.lean#L59 "Atlas.Comparisons.Catalogue.not_isomorphic_of_normalized_label_ne") | [Passed audit (12 Oct)](../verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019/CERTIFICATE.md) |
| <a id="order-certificates"></a><a id="e-series-order"></a> **By order:** outside the listed isomorphisms and the two patterns below, orders differ. The numerical classification is uniform, with no bound on rank or field size. | [Model orders](../THEOREM_STATEMENTS.md) · [order classification](../Atlas/OrderArithmetic/Classification.lean#L43 "Atlas.OrderArithmetic.catalogue_order_eq_iff") · [unequal orders](../Atlas/OrderArithmetic/Classification.lean#L64 "Atlas.OrderArithmetic.catalogue_order_ne") · [unequal orders imply nonisomorphism](../Atlas/Comparisons/Cardinality.lean#L9 "Atlas.Comparisons.not_isomorphic_of_card_ne") | [Compiled model audit (26 Oct)](../verification/2026-10-26-cache-audit/RESULT.json) · [Passed audit (12 Oct)](../verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019/CERTIFICATE.md) |
| **Equal order, different involution-class counts:** Bₙ(q) and Cₙ(q), odd q and n ≥ 3; counts n and ⌊n/2⌋ + 1 | [equal order](../Atlas/Comparisons/Classical/OrthogonalOrder.lean#L10 "Atlas.Comparisons.Classical.oddB_card_eq_C") · [nonisomorphism](../Atlas/Comparisons/Classical/OrthogonalInvolutions.lean#L21 "Atlas.Comparisons.Classical.oddB_not_equiv_C") · [counts](../Atlas/Comparisons/Classical/OrthogonalInvolutions.lean#L15 "Atlas.Comparisons.Classical.oddB_C_involution_counts") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) · [B invariant replay](../verification/existence/2026-10-25-draft/AtlasDistinguished-typeB/RESULT.json) · [C invariant replay](../verification/existence/2026-10-25-draft/AtlasDistinguished-typeC/RESULT.json) |
| **Equal order, different Sylow-2 centers:** A₈ ≃ PSL₄(2) versus PSL₃(4), both order 20,160; center sizes 2 and 4 | [equal order](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L31 "Atlas.Comparisons.Exceptional.alt8_card_eq_psl3Card4") · [A₈ nonisomorphism](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L22 "Atlas.Comparisons.Exceptional.alt8_not_equiv_psl3Card4") · [PSL₄ nonisomorphism](../Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean#L13 "Atlas.Comparisons.Exceptional.psl4Two_not_equiv_psl3Card4") | [Passed audit (15 Sep)](../verification/runs/orthogonal-comparison-contracts/20260915T124053-3/CERTIFICATE.md) · [A₈ invariant replay](../verification/existence/2026-10-25-draft/AtlasDistinguished-alternating8/RESULT.json) · [PSL₃(4) invariant replay](../verification/existence/2026-10-25-draft/AtlasDistinguished-psl3Four/RESULT.json) |

A normalized label is the family and parameter label after the proved
exceptional identifications. The 16 completed sporadic groups and Tits are
separated from one another and from all admissible values of the 16 completed
families by order. The four invariant replays passed separately. The
[two aggregate Comparator replays](../verification/existence/2026-10-25-draft/Catalogue-isomorphism/RESULT.json)
remain memory-stopped; the passed full audits above do not assert a replay pass.

<a id="comparison-scope"></a>

The linked statements retain their exact model and parameter hypotheses.
The combined theorem's registry is specified in the [technical description](../COMPARISON.md#scope-and-definitions).
For G₂/F₄ the registry uses the Octonion/Albert models; the comparisons to
their Chevalley models have the status in Theme 1. The unfinished derived-group
bridges in Theme 2 remain separate. [Exact theorem and compiled statements](../COMPARISON.md).
