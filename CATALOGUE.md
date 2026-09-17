# Constructive ATLAS catalogue

Entries describe explicit models, not a classification or recognition from order.
All source paths and declarations below are part of the default root import.
Full machine-readable interfaces, auxiliary groups and comparison maps: [catalogue.json](docs/catalogue.json).

## Cₚ

Multiplicative (ZMod p)

Parameters: p prime; card theorem m>0; simple iff m prime. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Families.Cyclic.Model` | [source](Atlas/Families/Cyclic/Basic.lean) |
| finite | `Atlas.Families.Cyclic.finite` | [source](Atlas/Families/Cyclic/Basic.lean) |
| order | `Atlas.Families.Cyclic.card` | [source](Atlas/Families/Cyclic/Basic.lean) |
| simple | `Atlas.Families.Cyclic.isSimpleGroup` | [source](Atlas/Families/Cyclic/Basic.lean) |
| commutative | `Atlas.Families.Cyclic.commutative` | [source](Atlas/Families/Cyclic/Basic.lean) |

Order: p

No general recognition theorem claimed by this entry

## Aₙ

alternatingGroup (Fin n)

Parameters: n>=5 for nonabelian simplicity; A3 cyclic simple; A4 not simple; n<=2 trivial. Exceptions: A3 is cyclic simple; A4 is not simple; degrees <=2 are trivial.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Families.Alternating.Model` | [source](Atlas/Families/Alternating/Basic.lean) |
| finite | `Atlas.Families.Alternating.finite` | [source](Atlas/Families/Alternating/Basic.lean) |
| order | `Atlas.Families.Alternating.card_factorial` | [source](Atlas/Families/Alternating/Basic.lean) |
| simple | `Atlas.Families.Alternating.isSimpleGroup` | [source](Atlas/Families/Alternating/Basic.lean) |
| nonabelian | `Atlas.Families.Alternating.exists_mul_ne_mul` | [source](Atlas/Families/Alternating/Basic.lean) |

Order: n!/2

No general recognition theorem claimed by this entry

## Aₙ(q)

The catalogue uses Lie rank n: Aₙ(q) = PSL_(n+1)(q). The audited PSL parameters and order formula below instead use n for the matrix dimension; no compiled declaration is renamed or reparameterized.

**Audited interface below: n denotes matrix dimension.**

SL_n(F)/center(SL_n(F))

Parameters: F arbitrary finite field; n>=2; simple iff (n,|F|) not (2,2),(2,3); prime-power existence p prime f>=1. Exceptions: (n,q)=(2,2),(2,3) are excluded from simplicity for n>=2.

| Interface | Declaration | Source |
|---|---|---|
| model | `Matrix.ProjectiveSpecialLinearGroup` | [source](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean) |
| finite | `Atlas.finite_psl` | [source](Atlas/LinearGroups/ProjectiveSpecialLinear.lean) |
| order | `Atlas.card_psl_factor` | [source](Atlas/LinearGroups/ProjectiveSpecialLinear.lean) |
| simple | `Atlas.psl_simple_iff` | [source](Atlas/LinearGroups/PSLFamily.lean) |
| nonabelian | `Atlas.psl_nonabelian_simple` | [source](Atlas/LinearGroups/PSLFamily.lean) |

Order: q^(n(n-1)/2)*product(i=2..n,q^i-1)/gcd(n,q-1)

No general recognition theorem claimed by this entry

## Bₙ(q)

Actual scalar quotient of the Siegel-generated subgroup of the quadratic form Q(x,y,z)=sum x_i*y_i+z^2; identified with the determinant/spinor kernel in odd characteristic and the full orthogonal group in characteristic two

Parameters: n is Lie rank, natural dimension 2*n+1; F arbitrary finite field, q=|F|; n>=1, every characteristic. Exceptions: Nonsimple exactly (n,q)=(1,2),(1,3),(2,2); these actual groups remain constructed.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Orthogonal.B` | [source](Atlas/LinearGroups/Orthogonal/BFamily.lean) |
| finite | `Atlas.Orthogonal.B_finite` | [source](Atlas/LinearGroups/Orthogonal/BFamily.lean) |
| order | `Atlas.Orthogonal.B_card_all_rank` | [source](Atlas/LinearGroups/Orthogonal/BAllRanks.lean) |
| simple | `Atlas.Orthogonal.B_simple_all_rank` | [source](Atlas/LinearGroups/Orthogonal/BAllRanksConstruction.lean) |
| nonabelian | `Atlas.Orthogonal.B_noncommutative_all_rank` | [source](Atlas/LinearGroups/Orthogonal/BAllRanksConstruction.lean) |

Order: q^(n*n) * product_(i=1)^n (q^(2*i)-1) / gcd(2,q-1)

No general recognition theorem or classification of family coincidences is claimed

## Cₙ(q)

Carrier of Matrix.symplecticGroup (Fin n) F, quotiented by its actual center

Parameters: n is symplectic rank, dimension 2*n; F arbitrary finite field, q=|F|; simple exactly when (n=1 and q>3) or (n>=2 and (n,q)!=(2,2)). Exceptions: Rank zero is trivial; nonsimple positive-rank pairs (n,q)=(1,2),(1,3),(2,2).

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Symplectic.PSp` | [source](Atlas/LinearGroups/Symplectic/Basic.lean) |
| finite | `Atlas.Symplectic.finite_psp` | [source](Atlas/LinearGroups/Symplectic/Basic.lean) |
| order | `Atlas.Symplectic.card_psp` | [source](Atlas/LinearGroups/Symplectic/ProjectiveOrder.lean) |
| simple | `Atlas.Symplectic.simple_of_good` | [source](Atlas/LinearGroups/Symplectic/Simplicity.lean) |
| nonabelian | `Atlas.Symplectic.projective_not_commutative` | [source](Atlas/LinearGroups/Symplectic/Noncommutative.lean) |

Order: q^(n^2) * product_(i=1)^n (q^(2*i)-1) / gcd(2,q-1) (n>=1); order 1 at n=0

Constructed symplectic family with its natural alternating form and actions; no CFSG or external recognition theorem assumed

## Dₙ(q)

Actual scalar quotient of the Siegel-generated subgroup of the split quadratic form Q(x,y)=sum x_i*y_i; identified with the determinant/spinor kernel in odd characteristic and Dickson kernel in characteristic two

Parameters: n is Lie rank, natural dimension 2*n; F arbitrary finite field, q=|F|; n>=4, every characteristic. Exceptions: No exceptions for n>=4; lower-rank comparisons are listed separately below.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Orthogonal.DPlus` | [source](Atlas/LinearGroups/Orthogonal/DFamily.lean) |
| finite | `Atlas.Orthogonal.DPlus_finite` | [source](Atlas/LinearGroups/Orthogonal/DFamily.lean) |
| order | `Atlas.Orthogonal.DPlus_card` | [source](Atlas/LinearGroups/Orthogonal/DFamily.lean) |
| simple | `Atlas.Orthogonal.DPlus_simple` | [source](Atlas/LinearGroups/Orthogonal/DConstruction.lean) |
| nonabelian | `Atlas.Orthogonal.DPlus_noncommutative` | [source](Atlas/LinearGroups/Orthogonal/DConstruction.lean) |

Order: q^(n*(n-1)) * (q^n-1) * product_(i=1)^(n-1) (q^(2*i)-1) / gcd(4,q^n-1)

No general recognition theorem or classification of family coincidences is claimed

## G₂(q)

Full group of linear multiplication-preserving automorphisms of the uniform eight-coordinate split octonion algebra

Parameters: F is an arbitrary finite field, q=|F|, including characteristics 2 and 3; simple exactly when q>2. Exceptions: q=2: actual long-root normal closure has order6048 and index2 in G2(2), whose order is12096.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.G2.Model` | [source](Atlas/LinearGroups/G2/Basic.lean) |
| finite | `Atlas.G2.finite_model` | [source](Atlas/LinearGroups/G2/Basic.lean) |
| order | `Atlas.G2.card_Model` | [source](Atlas/LinearGroups/G2/Order.lean) |
| simple | `Atlas.G2.isSimple` | [source](Atlas/LinearGroups/G2/Simplicity.lean) |
| nonabelian | `Atlas.G2.exists_mul_ne_mul` | [source](Atlas/LinearGroups/G2/RootGroups.lean) |

Order: q^6 * (q^6-1) * (q^2-1)

Concrete Dickson/Wilson octonion construction; no general Chevalley, CFSG, order-recognition or PSU3(3) comparison theorem assumed

## ²G₂(q)

Actual subgroup of GL7(F) generated by the explicit Tits-twisted alpha, beta, gamma, torus and Weyl matrices

Parameters: F finite of characteristic 3, q=|F|=3^(2m+1), m>=1; the public family starts at q=27. Exceptions: m=0 (q=3) is excluded from the public simple family; no low-parameter extension or PSL2(8) identification is certified here.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.ReeG2.Model` | [source](Atlas/LinearGroups/ReeG2/Generators.lean) |
| finite | `Atlas.ReeG2.finite_model` | [source](Atlas/LinearGroups/TypeReeG2.lean) |
| order | `Atlas.ReeG2.order` | [source](Atlas/LinearGroups/ReeG2/Order.lean) |
| simple | `Atlas.ReeG2.simple` | [source](Atlas/LinearGroups/ReeG2/Simplicity.lean) |
| nonabelian | `Atlas.ReeG2.model_noncommutative` | [source](Atlas/LinearGroups/ReeG2/Noncommutative.lean) |

Order: q^3 * (q^3+1) * (q-1)

Direct standard Ree matrix construction and explicit injective map into the existing split-octonion G2 model; no CFSG, abstract Chevalley/Ree theorem or order recognition

## M₁₁

point stabilizer in full Golay dodecad stabilizer

Parameters: any constructed Golay dodecad D and a point of D; canonical standard choices also provided. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Mathieu11.Model` | [source](Atlas/Sporadic/Mathieu11.lean) |
| finite | `Atlas.Sporadic.Mathieu11.finite` | [source](Atlas/Sporadic/Mathieu11.lean) |
| order | `Atlas.Sporadic.Mathieu11.card` | [source](Atlas/Sporadic/Mathieu11.lean) |
| simple | `Atlas.Sporadic.Mathieu11.isSimpleGroup` | [source](Atlas/Sporadic/Mathieu11.lean) |
| nonabelian | `Atlas.Sporadic.Mathieu11.exists_mul_ne_mul` | [source](Atlas/Sporadic/Mathieu11.lean) |

Order: 7920

No general recognition theorem claimed by this entry

## M₁₂

full Golay dodecad stabilizer

Parameters: any constructed Golay dodecad D; canonical standard choice provided. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Mathieu12.Model` | [source](Atlas/Sporadic/Mathieu12.lean) |
| finite | `Atlas.Sporadic.Mathieu12.finite` | [source](Atlas/Sporadic/Mathieu12.lean) |
| order | `Atlas.Sporadic.Mathieu12.card` | [source](Atlas/Sporadic/Mathieu12.lean) |
| simple | `Atlas.Sporadic.Mathieu12.isSimpleGroup` | [source](Atlas/Sporadic/Mathieu12.lean) |
| nonabelian | `Atlas.Sporadic.Mathieu12.exists_mul_ne_mul` | [source](Atlas/Sporadic/Mathieu12.lean) |

Order: 95040

No general recognition theorem claimed by this entry

## M₂₂

two coordinate pointwise stabilizer in full Golay automorphism group

Parameters: any coordinate a and distinct coordinate b. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Mathieu22.Model` | [source](Atlas/Sporadic/Mathieu22.lean) |
| finite | `Atlas.Sporadic.Mathieu22.finite` | [source](Atlas/Sporadic/Mathieu22.lean) |
| order | `Atlas.Sporadic.Mathieu22.card` | [source](Atlas/Sporadic/Mathieu22.lean) |
| simple | `Atlas.Sporadic.Mathieu22.isSimpleGroup` | [source](Atlas/Sporadic/Mathieu22Simple.lean) |
| nonabelian | `Atlas.Sporadic.Mathieu22.exists_mul_ne_mul` | [source](Atlas/Sporadic/Mathieu22.lean) |

Order: 443520

No general recognition theorem claimed by this entry

## M₂₃

coordinate stabilizer in full Golay automorphism group

Parameters: any coordinate a. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Mathieu23.Model` | [source](Atlas/Sporadic/Mathieu23.lean) |
| finite | `Atlas.Sporadic.Mathieu23.finite` | [source](Atlas/Sporadic/Mathieu23.lean) |
| order | `Atlas.Sporadic.Mathieu23.card` | [source](Atlas/Sporadic/Mathieu23.lean) |
| simple | `Atlas.Sporadic.Mathieu23.isSimpleGroup` | [source](Atlas/Sporadic/Mathieu23.lean) |
| nonabelian | `Atlas.Sporadic.Mathieu23.exists_mul_ne_mul` | [source](Atlas/Sporadic/Mathieu23.lean) |

Order: 10200960

No general recognition theorem claimed by this entry

## M₂₄

full permutation automorphism group of constructed binary Golay code

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Mathieu24.Model` | [source](Atlas/Sporadic/Mathieu24.lean) |
| finite | `Atlas.Sporadic.Mathieu24.finite` | [source](Atlas/Sporadic/Mathieu24.lean) |
| order | `Atlas.Sporadic.Mathieu24.card` | [source](Atlas/Sporadic/Mathieu24Construction.lean) |
| simple | `Atlas.Sporadic.Mathieu24.isSimpleGroup` | [source](Atlas/Sporadic/Mathieu24Construction.lean) |
| nonabelian | `Atlas.Sporadic.Mathieu24.exists_mul_ne_mul` | [source](Atlas/Sporadic/Mathieu24Construction.lean) |

Order: 244823040

No general recognition theorem claimed by this entry

## Co₁

full Golay Leech isometry group modulo its center {±1}

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Conway1.Model` | [source](Atlas/Sporadic/Conway1.lean) |
| finite | `Atlas.Sporadic.Conway1.finite` | [source](Atlas/Sporadic/Conway1.lean) |
| order | `Atlas.Sporadic.Conway1.card` | [source](Atlas/Sporadic/Conway1.lean) |
| simple | `Atlas.Sporadic.Conway1.isSimpleGroup` | [source](Atlas/Sporadic/Conway1.lean) |
| nonabelian | `Atlas.Sporadic.Conway1.exists_mul_ne_mul` | [source](Atlas/Sporadic/Conway1.lean) |

Order: 4157776806543360000

No general recognition theorem claimed by this entry

## Co₂

actual norm-four vector stabilizer in full Leech isometry group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Conway2.Model` | [source](Atlas/Sporadic/Conway2.lean) |
| finite | `Atlas.Sporadic.Conway2.finite` | [source](Atlas/Sporadic/Conway2.lean) |
| order | `Atlas.Sporadic.Conway2.card` | [source](Atlas/Sporadic/Conway2.lean) |
| simple | `Atlas.Sporadic.Conway2.isSimpleGroup` | [source](Atlas/Sporadic/Conway2Simplicity.lean) |
| nonabelian | `Atlas.Sporadic.Conway2.exists_mul_ne_mul` | [source](Atlas/Sporadic/Conway2Commutators.lean) |

Order: 42305421312000

No general recognition theorem claimed by this entry

## Co₃

actual norm-six vector stabilizer in full Leech isometry group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Conway3.Model` | [source](Atlas/Sporadic/Conway3.lean) |
| finite | `Atlas.Sporadic.Conway3.finite` | [source](Atlas/Sporadic/Conway3.lean) |
| order | `Atlas.Sporadic.Conway3.card` | [source](Atlas/Sporadic/Conway3.lean) |
| simple | `Atlas.Sporadic.Conway3.isSimpleGroup` | [source](Atlas/Sporadic/Conway3Simplicity.lean) |
| nonabelian | `Atlas.Sporadic.Conway3.exists_mul_ne_mul` | [source](Atlas/Sporadic/Conway3Geometry.lean) |

Order: 495766656000

No general recognition theorem claimed by this entry

## McL

actual pointwise Leech 2-2-3 triangle stabilizer

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.McLaughlin.Model` | [source](Atlas/Sporadic/McLaughlin.lean) |
| finite | `Atlas.Sporadic.McLaughlin.finite` | [source](Atlas/Sporadic/McLaughlin.lean) |
| order | `Atlas.Sporadic.McLaughlin.card` | [source](Atlas/Sporadic/McLaughlin.lean) |
| simple | `Atlas.Sporadic.McLaughlin.isSimpleGroup` | [source](Atlas/Sporadic/McLaughlinSimplicity.lean) |
| nonabelian | `Atlas.Sporadic.McLaughlin.exists_mul_ne_mul` | [source](Atlas/Sporadic/McLaughlinGraph.lean) |

Order: 898128000

No general recognition theorem claimed by this entry

## HS

actual pointwise Leech 2-3-3 triangle stabilizer

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.HigmanSims.Model` | [source](Atlas/Sporadic/HigmanSimsConfiguration.lean) |
| finite | `Atlas.Sporadic.HigmanSims.finite` | [source](Atlas/Sporadic/HigmanSimsLattice.lean) |
| order | `Atlas.Sporadic.HigmanSims.card` | [source](Atlas/Sporadic/HigmanSims.lean) |
| simple | `Atlas.Sporadic.HigmanSims.isSimpleGroup` | [source](Atlas/Sporadic/HigmanSimsSimplicity.lean) |
| nonabelian | `Atlas.Sporadic.HigmanSims.exists_mul_ne_mul` | [source](Atlas/Sporadic/HigmanSimsLocal.lean) |

Order: 44352000

No general recognition theorem claimed by this entry

## Suz

actual Eisenstein Leech centralizer modulo six scalar isometries

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Suzuki.Model` | [source](Atlas/Sporadic/Suzuki.lean) |
| finite | `Atlas.Sporadic.Suzuki.finite` | [source](Atlas/Sporadic/Suzuki.lean) |
| order | `Atlas.Sporadic.Suzuki.card` | [source](Atlas/Sporadic/Suzuki.lean) |
| simple | `Atlas.Sporadic.Suzuki.isSimpleGroup` | [source](Atlas/Sporadic/Suzuki.lean) |
| nonabelian | `Atlas.Sporadic.Suzuki.exists_mul_ne_mul` | [source](Atlas/Sporadic/Suzuki.lean) |

Order: 448345497600

No general recognition theorem claimed by this entry

## J₂

actual icosian linear group modulo its center of order two

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Janko2.Model` | [source](Atlas/Sporadic/Janko2.lean) |
| finite | `Atlas.Sporadic.Janko2.finite` | [source](Atlas/Sporadic/Janko2.lean) |
| order | `Atlas.Sporadic.Janko2.card` | [source](Atlas/Sporadic/Janko2.lean) |
| simple | `Atlas.Sporadic.Janko2.isSimpleGroup` | [source](Atlas/Sporadic/Janko2.lean) |
| nonabelian | `Atlas.Sporadic.Janko2.exists_mul_ne_mul` | [source](Atlas/Sporadic/Janko2.lean) |

Order: 604800

No general recognition theorem claimed by this entry

## Fi₂₂

commuting-pair centralizer quotient in actual full ray group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Fischer22.Model` | [source](Atlas/Sporadic/Fischer22.lean) |
| finite | `Atlas.Sporadic.Fischer22.finite` | [source](Atlas/Sporadic/Fischer22.lean) |
| order | `Atlas.Sporadic.Fischer22.card` | [source](Atlas/Sporadic/Fischer22.lean) |
| simple | `Atlas.Sporadic.Fischer22.simple` | [source](Atlas/Sporadic/Fischer22.lean) |
| nonabelian | `Atlas.Sporadic.Fischer22.exists_mul_ne_mul` | [source](Atlas/Fischer/FischerPublicCompatibility.lean) |

Order: 64561751654400

No general recognition theorem claimed by this entry

## Fi₂₃

singleton centralizer quotient in actual full ray group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Fischer23.Model` | [source](Atlas/Sporadic/Fischer23.lean) |
| finite | `Atlas.Sporadic.Fischer23.finite` | [source](Atlas/Sporadic/Fischer23.lean) |
| order | `Atlas.Sporadic.Fischer23.card` | [source](Atlas/Sporadic/Fischer23.lean) |
| simple | `Atlas.Sporadic.Fischer23.simple` | [source](Atlas/Sporadic/Fischer23.lean) |
| nonabelian | `Atlas.Sporadic.Fischer23.exists_mul_ne_mul` | [source](Atlas/Fischer/FischerPublicCompatibility.lean) |

Order: 4089470473293004800

No general recognition theorem claimed by this entry

## Fi₂₄′

positive subgroup of actual Conway-Parker root-generated ray group

Parameters: fixed constructed carrier; no supplied order or simplicity certificate. Exceptions: None stated beyond the parameter domain.

| Interface | Declaration | Source |
|---|---|---|
| model | `Atlas.Sporadic.Fischer24Prime.Model` | [source](Atlas/Sporadic/Fischer24Prime.lean) |
| finite | `Atlas.Sporadic.Fischer24Prime.finite` | [source](Atlas/Sporadic/Fischer24Prime.lean) |
| order | `Atlas.Sporadic.Fischer24Prime.card` | [source](Atlas/Sporadic/Fischer24Prime.lean) |
| simple | `Atlas.Sporadic.Fischer24Prime.simple` | [source](Atlas/Sporadic/Fischer24Prime.lean) |
| nonabelian | `Atlas.Sporadic.Fischer24Prime.exists_mul_ne_mul` | [source](Atlas/Fischer/FischerPublicCompatibility.lean) |

Order: 1255205709190661721292800

No general recognition theorem claimed by this entry

## Proved comparisons

- B(1,F) / PSL(2,F): isomorphism, F any field; natural quadratic dimension 3; PSL dimension 2; includes q=2,3; `Atlas.Comparisons.Classical.b1EquivA1` ([source](Atlas/Comparisons/Classical/Orthogonal.lean)).
- B(n,F) / C(n,F): isomorphism, F finite, characteristic 2; n >= 1; natural dimensions 2n+1 and 2n; `Atlas.Comparisons.Classical.evenBEquivC` ([source](Atlas/Comparisons/Classical/Orthogonal.lean)).
- B(2,F) / C(2,F): isomorphism, F finite, every characteristic; natural dimensions 5 and 4; `Atlas.Comparisons.Classical.b2EquivC2` ([source](Atlas/Comparisons/Classical/Orthogonal.lean)).
- D+(2,F) / PSL(2,F) x PSL(2,F): isomorphism, F any field; split quadratic dimension 4; PSL dimensions 2 and 2; `Atlas.Comparisons.Classical.d2EquivProduct` ([source](Atlas/Comparisons/Classical/Orthogonal.lean)).
- D+(3,F) / PSL(4,F): isomorphism, F finite, every characteristic; split quadratic dimension 6; PSL dimension 4; `Atlas.Comparisons.Classical.d3EquivA3` ([source](Atlas/Comparisons/Classical/Orthogonal.lean)).
- B(n,F) / B(n,K): isomorphism, F,K any fields; n any natural rank; explicit field isomorphism F ~= K; `Atlas.Comparisons.Classical.bFieldEquiv` ([source](Atlas/Comparisons/Classical/Orthogonal.lean)).
- D+(n,F) / D+(n,K): isomorphism, F,K any fields; n any natural rank; explicit field isomorphism F ~= K; `Atlas.Comparisons.Classical.dFieldEquiv` ([source](Atlas/Comparisons/Classical/Orthogonal.lean)).
- B(n,F) / C(n,F): same_order, F finite, odd characteristic; n >= 2; no isomorphism asserted; `Atlas.Comparisons.Classical.oddB_card_eq_C` ([source](Atlas/Comparisons/Classical/OrthogonalOrder.lean)).
- B(n,F) / C(n,F): nonisomorphism, F finite, odd characteristic; n >= 3; distinguished by proved involution-class counts; `Atlas.Comparisons.Classical.oddB_not_equiv_C` ([source](Atlas/Comparisons/Classical/OrthogonalInvolutions.lean)).
- PSL(2,F) / A6: isomorphism, F any finite field of cardinality 9; common faithful ten-point actions; `Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6` ([source](Atlas/Comparisons/Exceptional/Order360.lean)).
- PSL(2,GaloisField 3 2) / A6: isomorphism, Canonical pinned finite-field wrapper; `Atlas.Comparisons.Exceptional.psl2NineEquivAlt6` ([source](Atlas/Comparisons/Exceptional/Order360.lean)).
- B(2,ZMod 2)' / C(2,ZMod 2)': isomorphism, Actual commutator subgroups; restriction of the full B2/C2 comparison; `Atlas.Comparisons.Exceptional.b2BinaryDerivedEquivC2Derived` ([source](Atlas/Comparisons/Exceptional/BinaryDerived.lean)).
- C(2,ZMod 2)' / A6: isomorphism, Derived group of order 360; full C2(2) is not the endpoint; `Atlas.Comparisons.Exceptional.c2BinaryDerivedEquivAlt6` ([source](Atlas/Comparisons/Exceptional/BinaryDerived.lean)).
- PSL(2,F) / B(2,ZMod 2)': isomorphism, F finite of cardinality 9; composition through actual A6; `Atlas.Comparisons.Exceptional.psl2Card9EquivB2BinaryDerived` ([source](Atlas/Comparisons/Exceptional/Order360.lean)).
- PSL(2,F) / C(2,ZMod 2)': isomorphism, F finite of cardinality 9; composition through actual A6; `Atlas.Comparisons.Exceptional.psl2Card9EquivC2BinaryDerived` ([source](Atlas/Comparisons/Exceptional/Order360.lean)).
- A8 / D+(3,ZMod 2): isomorphism, Actual binary deleted permutation quotient with explicit split isometry; `Atlas.Comparisons.Exceptional.alt8EquivD3Two` ([source](Atlas/Comparisons/Exceptional/Order20160A8.lean)).
- PSL(4,ZMod 2) / A8: isomorphism, Actual D3/A3 comparison composed with the faithful deleted-module action; `Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8` ([source](Atlas/Comparisons/Exceptional/Order20160A8.lean)).
- PSL(4,ZMod 2) / PSL(3,F): nonisomorphism, F finite of cardinality 4; Sylow-2 centers of cardinalities 2 and 4; `Atlas.Comparisons.Exceptional.psl4Two_not_equiv_psl3Card4` ([source](Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean)).
- A8 / PSL(3,F): nonisomorphism, F finite of cardinality 4; transport of the proved Sylow-center obstruction; `Atlas.Comparisons.Exceptional.alt8_not_equiv_psl3Card4` ([source](Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean)).
- PSL(4,ZMod 2) / PSL(3,F): same_order, F finite of cardinality 4; both orders 20160; `Atlas.Comparisons.Exceptional.psl4Two_card_eq_psl3Card4` ([source](Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean)).
- A8 / PSL(3,F): same_order, F finite of cardinality 4; both orders 20160; `Atlas.Comparisons.Exceptional.alt8_card_eq_psl3Card4` ([source](Atlas/Comparisons/Exceptional/Order20160Nonisomorphism.lean)).
- PSL(2,F) / A5: isomorphism, F any finite field of cardinality 4; natural projective-line action; `Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5` ([source](Atlas/Comparisons/Exceptional/Order60Four.lean)).
- PSL(2,F) / A5: isomorphism, F any finite field of cardinality 5; proved elementary order-60 recognition; `Atlas.Comparisons.Exceptional.psl2Card5EquivAlt5` ([source](Atlas/Comparisons/Exceptional/Order60Five.lean)).
- PSL(2,ZMod 7) / PSL(3,ZMod 2): isomorphism, Actual matrix models; common faithful action on eight points; `Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two` ([source](Atlas/Comparisons/Exceptional/Order168.lean)).
- PSL(2,F) / PSL(2,ZMod 5): isomorphism, F any finite field of cardinality 4; composition of the verified maps; `Atlas.Comparisons.Exceptional.psl2Card4EquivPsl2Five` ([source](Atlas/Comparisons/Exceptional/Order60Five.lean)).
