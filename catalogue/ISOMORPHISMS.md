# Lean certificates identifying construction models

These are actual `MulEquiv` terms between the named concrete carriers. Their
verbatim compiled types come from the source-bound 26 October audit. The linked
Lean definitions contain the proofs; the separate full audits retain type, instance
and proof dependencies. A certificate applies on its stated domain, including
nonsimple parameters when specified. Order equality alone is not an identification.

This is the technical appendix for the four included construction-identification maps. The [comparison guide](REALIZATIONS.md) also covers [isomorphisms between families](REALIZATIONS.md#between-families), [nonisomorphism by orders and invariants](REALIZATIONS.md#remaining-pairs), and [remaining gaps](REALIZATIONS.md#comparison-scope).

<a id="chevalley-a-to-legacy-v1"></a>

## family.PSL/chevalley ≃ family.PSL/matrix

Domain: K an arbitrary finite field; q = Nat.card K; r >= 1; every finite characteristic.

| Interface | Exact Lean reference |
|---|---|
| Source model | [`Atlas.Chevalley.Catalogue.A`](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean#L13) |
| Source group operations | [`Atlas.Chevalley.Catalogue.AGroup`](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean#L15) |
| Target model | [`Matrix.ProjectiveSpecialLinearGroup`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean) |
| Target group operations | [`Atlas.Chevalley.Catalogue.PSLGroup`](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L16) |
| Parameter map | [`Atlas.Chevalley.Catalogue.A_matrixDimension`](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L10) |
| Isomorphism witness | [`Atlas.Chevalley.Catalogue.A_identification`](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L24) |

Proof definition (verbatim source, in namespace `Atlas.Chevalley.Catalogue`):

```lean
def A_identification (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K]
    (hK : AFieldDomain r hr K) :
    A r hr K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (A_matrixDimension r)) K := by
  letI : Finite K := hK
  exact Comparison.TypeA.projectiveEquiv r hr K
```

<details>
<summary>Complete compiled type, including implicit instances</summary>

```lean
Atlas.Chevalley.Catalogue.A_identification.{u_1} : (r : Nat) →
  (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) →
    (K : Type u_1) →
      [inst : Field.{u_1} K] →
        @Atlas.Chevalley.Catalogue.AFieldDomain.{u_1} r hr K inst →
          @MulEquiv.{u_1, u_1} (@Atlas.Chevalley.Catalogue.A.{u_1} r hr K inst)
            (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
              (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
              (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K (@Field.toCommRing.{u_1} K inst))
            (@MulOne.toMul.{u_1} (@Atlas.Chevalley.Catalogue.A.{u_1} r hr K inst)
              (@MulOneClass.toMulOne.{u_1} (@Atlas.Chevalley.Catalogue.A.{u_1} r hr K inst)
                (@Monoid.toMulOneClass.{u_1} (@Atlas.Chevalley.Catalogue.A.{u_1} r hr K inst)
                  (@DivInvMonoid.toMonoid.{u_1} (@Atlas.Chevalley.Catalogue.A.{u_1} r hr K inst)
                    (@Group.toDivInvMonoid.{u_1} (@Atlas.Chevalley.Catalogue.A.{u_1} r hr K inst)
                      (@Atlas.Chevalley.Catalogue.AGroup.{u_1} r hr K inst))))))
            (@MulOne.toMul.{u_1}
              (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K (@Field.toCommRing.{u_1} K inst))
              (@MulOneClass.toMulOne.{u_1}
                (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                  (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                  (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K (@Field.toCommRing.{u_1} K inst))
                (@Monoid.toMulOneClass.{u_1}
                  (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                    (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                    (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K (@Field.toCommRing.{u_1} K inst))
                  (@DivInvMonoid.toMonoid.{u_1}
                    (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1} (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                      (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                      (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K (@Field.toCommRing.{u_1} K inst))
                    (@Group.toDivInvMonoid.{u_1}
                      (@Matrix.ProjectiveSpecialLinearGroup.{0, u_1}
                        (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                        (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                        (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K
                        (@Field.toCommRing.{u_1} K inst))
                      (@QuotientGroup.Quotient.group.{u_1}
                        (@Matrix.SpecialLinearGroup.{0, u_1} (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                          (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                          (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K
                          (@Field.toCommRing.{u_1} K inst))
                        (@Matrix.SpecialLinearGroup.instGroup.{0, u_1}
                          (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                          (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                          (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K
                          (@Field.toCommRing.{u_1} K inst))
                        (@Subgroup.center.{u_1}
                          (@Matrix.SpecialLinearGroup.{0, u_1} (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                            (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                            (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K
                            (@Field.toCommRing.{u_1} K inst))
                          (@Matrix.SpecialLinearGroup.instGroup.{0, u_1}
                            (Fin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                            (instDecidableEqFin (Atlas.Chevalley.Catalogue.A_matrixDimension r))
                            (Fin.fintype (Atlas.Chevalley.Catalogue.A_matrixDimension r)) K
                            (@Field.toCommRing.{u_1} K inst)))
                        ⋯))))))
```

</details>

[Compiled evidence](../verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz) · [Full dependency audit](../verification/runs/chevalley-a-to-legacy-v1/20261018T160827-105).

Marked-generator compatibility:

- [`Atlas.Chevalley.Comparison.TypeA.projectiveEquiv_rho`](../Atlas/LinearGroups/Chevalley/Comparison/TypeAProjectiveEquiv.lean#L16)
- [`Atlas.Chevalley.Comparison.TypeA.projectiveEquiv_X`](../Atlas/LinearGroups/Chevalley/Comparison/TypeAProjectiveEquiv.lean#L36)
- [`Atlas.Chevalley.Comparison.TypeA.projectiveEquiv_Y`](../Atlas/LinearGroups/Chevalley/Comparison/TypeAProjectiveEquiv.lean#L45)

<a id="chevalley-c-to-legacy-v1"></a>

## family.C/chevalley ≃ family.C/symplectic

Domain: K an arbitrary finite field; q = Nat.card K; r >= 2; every finite characteristic.

| Interface | Exact Lean reference |
|---|---|
| Source model | [`Atlas.Chevalley.Catalogue.C`](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean#L18) |
| Source group operations | [`Atlas.Chevalley.Catalogue.CGroup`](../Atlas/LinearGroups/Chevalley/Catalogue/ACConstruction.lean#L21) |
| Target model | [`Atlas.Symplectic.PSp`](../Atlas/LinearGroups/Symplectic/Basic.lean#L16) |
| Target group operations | [`Atlas.Chevalley.Catalogue.PSpGroup`](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L20) |
| Parameter map | [`Atlas.Chevalley.Catalogue.C_symplecticRank`](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L13) |
| Isomorphism witness | [`Atlas.Chevalley.Catalogue.C_identification`](../Atlas/LinearGroups/Chevalley/Catalogue/ACIdentification.lean#L31) |

Proof definition (verbatim source, in namespace `Atlas.Chevalley.Catalogue`):

```lean
def C_identification (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : CFieldDomain n hn K) :
    C n hn K ≃* Atlas.Symplectic.PSp (C_symplecticRank n) K := by
  letI : Finite K := hK
  exact Comparison.TypeC.projectiveEquiv n hn K
```

<details>
<summary>Complete compiled type, including implicit instances</summary>

```lean
Atlas.Chevalley.Catalogue.C_identification.{u_1} : (n : Nat) →
  (hn :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    (K : Type u_1) →
      [inst : Field.{u_1} K] →
        @Atlas.Chevalley.Catalogue.CFieldDomain.{u_1} n hn K inst →
          @MulEquiv.{u_1, u_1} (@Atlas.Chevalley.Catalogue.C.{u_1} n hn K inst)
            (@Atlas.Symplectic.PSp.{u_1} (Atlas.Chevalley.Catalogue.C_symplecticRank n) K
              (@Field.toCommRing.{u_1} K inst))
            (@MulOne.toMul.{u_1} (@Atlas.Chevalley.Catalogue.C.{u_1} n hn K inst)
              (@MulOneClass.toMulOne.{u_1} (@Atlas.Chevalley.Catalogue.C.{u_1} n hn K inst)
                (@Monoid.toMulOneClass.{u_1} (@Atlas.Chevalley.Catalogue.C.{u_1} n hn K inst)
                  (@DivInvMonoid.toMonoid.{u_1} (@Atlas.Chevalley.Catalogue.C.{u_1} n hn K inst)
                    (@Group.toDivInvMonoid.{u_1} (@Atlas.Chevalley.Catalogue.C.{u_1} n hn K inst)
                      (@Atlas.Chevalley.Catalogue.CGroup.{u_1} n hn K inst))))))
            (@MulOne.toMul.{u_1}
              (@Atlas.Symplectic.PSp.{u_1} (Atlas.Chevalley.Catalogue.C_symplecticRank n) K
                (@Field.toCommRing.{u_1} K inst))
              (@MulOneClass.toMulOne.{u_1}
                (@Atlas.Symplectic.PSp.{u_1} (Atlas.Chevalley.Catalogue.C_symplecticRank n) K
                  (@Field.toCommRing.{u_1} K inst))
                (@Monoid.toMulOneClass.{u_1}
                  (@Atlas.Symplectic.PSp.{u_1} (Atlas.Chevalley.Catalogue.C_symplecticRank n) K
                    (@Field.toCommRing.{u_1} K inst))
                  (@DivInvMonoid.toMonoid.{u_1}
                    (@Atlas.Symplectic.PSp.{u_1} (Atlas.Chevalley.Catalogue.C_symplecticRank n) K
                      (@Field.toCommRing.{u_1} K inst))
                    (@Group.toDivInvMonoid.{u_1}
                      (@Atlas.Symplectic.PSp.{u_1} (Atlas.Chevalley.Catalogue.C_symplecticRank n) K
                        (@Field.toCommRing.{u_1} K inst))
                      (@QuotientGroup.Quotient.group.{u_1}
                        (@Atlas.Symplectic.Sp.{u_1} (Atlas.Chevalley.Catalogue.C_symplecticRank n) K
                          (@Field.toCommRing.{u_1} K inst))
                        (@SymplecticGroup.instGroupSubtypeMatrixSumMemSubmonoidSymplecticGroup.{0, u_1}
                          (Fin (Atlas.Chevalley.Catalogue.C_symplecticRank n)) K
                          (instDecidableEqFin (Atlas.Chevalley.Catalogue.C_symplecticRank n))
                          (Fin.fintype (Atlas.Chevalley.Catalogue.C_symplecticRank n)) (@Field.toCommRing.{u_1} K inst))
                        (@Subgroup.center.{u_1}
                          (@Atlas.Symplectic.Sp.{u_1} (Atlas.Chevalley.Catalogue.C_symplecticRank n) K
                            (@Field.toCommRing.{u_1} K inst))
                          (@SymplecticGroup.instGroupSubtypeMatrixSumMemSubmonoidSymplecticGroup.{0, u_1}
                            (Fin (Atlas.Chevalley.Catalogue.C_symplecticRank n)) K
                            (instDecidableEqFin (Atlas.Chevalley.Catalogue.C_symplecticRank n))
                            (Fin.fintype (Atlas.Chevalley.Catalogue.C_symplecticRank n))
                            (@Field.toCommRing.{u_1} K inst)))
                        ⋯))))))
```

</details>

[Compiled evidence](../verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz) · [Full dependency audit](../verification/runs/chevalley-c-to-legacy-v1/20261018T162154-105).

Marked-generator compatibility:

- [`Atlas.Chevalley.Comparison.TypeC.projectiveEquiv_rho`](../Atlas/LinearGroups/Chevalley/Comparison/TypeCProjectiveEquiv.lean#L22)
- [`Atlas.Chevalley.Comparison.TypeC.projectiveEquiv_X_short`](../Atlas/LinearGroups/Chevalley/Comparison/TypeCProjectiveEquiv.lean#L43)
- [`Atlas.Chevalley.Comparison.TypeC.projectiveEquiv_Y_short`](../Atlas/LinearGroups/Chevalley/Comparison/TypeCProjectiveEquiv.lean#L53)
- [`Atlas.Chevalley.Comparison.TypeC.projectiveEquiv_X_long`](../Atlas/LinearGroups/Chevalley/Comparison/TypeCProjectiveEquiv.lean#L63)
- [`Atlas.Chevalley.Comparison.TypeC.projectiveEquiv_Y_long`](../Atlas/LinearGroups/Chevalley/Comparison/TypeCProjectiveEquiv.lean#L73)

<a id="chevalley-d-to-legacy-v1"></a>

## family.D/chevalley ≃ family.D/quadratic

Domain: K an arbitrary finite field; q = Nat.card K; r >= 4; every finite characteristic.

| Interface | Exact Lean reference |
|---|---|
| Source model | [`Atlas.Chevalley.Catalogue.D`](../Atlas/LinearGroups/Chevalley/Catalogue/DConstruction.lean#L10) |
| Source group operations | [`Atlas.Chevalley.Catalogue.DGroup`](../Atlas/LinearGroups/Chevalley/Catalogue/DConstruction.lean#L12) |
| Target model | [`Atlas.Orthogonal.DPlus`](../Atlas/LinearGroups/Orthogonal/DFamily.lean#L13) |
| Target group operations | [`Atlas.Chevalley.Catalogue.DPlusGroup`](../Atlas/LinearGroups/Chevalley/Catalogue/DIdentification.lean#L12) |
| Parameter map | [`Atlas.Chevalley.Catalogue.D_quadraticRank`](../Atlas/LinearGroups/Chevalley/Catalogue/DIdentification.lean#L9) |
| Isomorphism witness | [`Atlas.Chevalley.Catalogue.D_identification`](../Atlas/LinearGroups/Chevalley/Catalogue/DIdentification.lean#L16) |

Proof definition (verbatim source, in namespace `Atlas.Chevalley.Catalogue`):

```lean
def D_identification (r : ℕ) (hr : 4 ≤ r) (K : Type*) [Field K]
    (hK : DFieldDomain r hr K) :
    D r hr K ≃* Atlas.Orthogonal.DPlus (D_quadraticRank r) K := by
  letI : Finite K := hK
  exact Comparison.TypeD.modelDPlusEquiv r hr K
```

<details>
<summary>Complete compiled type, including implicit instances</summary>

```lean
Atlas.Chevalley.Catalogue.D_identification.{u_1} : (r : Nat) →
  (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) r) →
    (K : Type u_1) →
      [inst : Field.{u_1} K] →
        @Atlas.Chevalley.Catalogue.DFieldDomain.{u_1} r hr K inst →
          @MulEquiv.{u_1, u_1} (@Atlas.Chevalley.Catalogue.D.{u_1} r hr K inst)
            (@Atlas.Orthogonal.DPlus.{u_1} (Atlas.Chevalley.Catalogue.D_quadraticRank r) K inst)
            (@MulOne.toMul.{u_1} (@Atlas.Chevalley.Catalogue.D.{u_1} r hr K inst)
              (@MulOneClass.toMulOne.{u_1} (@Atlas.Chevalley.Catalogue.D.{u_1} r hr K inst)
                (@Monoid.toMulOneClass.{u_1} (@Atlas.Chevalley.Catalogue.D.{u_1} r hr K inst)
                  (@DivInvMonoid.toMonoid.{u_1} (@Atlas.Chevalley.Catalogue.D.{u_1} r hr K inst)
                    (@Group.toDivInvMonoid.{u_1} (@Atlas.Chevalley.Catalogue.D.{u_1} r hr K inst)
                      (@Atlas.Chevalley.Catalogue.DGroup.{u_1} r hr K inst))))))
            (@MulOne.toMul.{u_1} (@Atlas.Orthogonal.DPlus.{u_1} (Atlas.Chevalley.Catalogue.D_quadraticRank r) K inst)
              (@MulOneClass.toMulOne.{u_1}
                (@Atlas.Orthogonal.DPlus.{u_1} (Atlas.Chevalley.Catalogue.D_quadraticRank r) K inst)
                (@Monoid.toMulOneClass.{u_1}
                  (@Atlas.Orthogonal.DPlus.{u_1} (Atlas.Chevalley.Catalogue.D_quadraticRank r) K inst)
                  (@DivInvMonoid.toMonoid.{u_1}
                    (@Atlas.Orthogonal.DPlus.{u_1} (Atlas.Chevalley.Catalogue.D_quadraticRank r) K inst)
                    (@Group.toDivInvMonoid.{u_1}
                      (@Atlas.Orthogonal.DPlus.{u_1} (Atlas.Chevalley.Catalogue.D_quadraticRank r) K inst)
                      (@Atlas.Orthogonal.projectiveElementaryGroup.{u_1, u_1} K
                        (Atlas.Orthogonal.VectorD.{u_1} (Atlas.Chevalley.Catalogue.D_quadraticRank r) K) inst
                        (@Pi.addCommGroup.{0, u_1}
                          (Atlas.Orthogonal.Index (Atlas.Chevalley.Catalogue.D_quadraticRank r)) (fun a ↦ K) fun i ↦
                          @Ring.toAddCommGroup.{u_1} K
                            (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst)))
                        (@Pi.Function.module.{0, u_1, u_1}
                          (Atlas.Orthogonal.Index (Atlas.Chevalley.Catalogue.D_quadraticRank r)) K K
                          (@CommSemiring.toSemiring.{u_1} K
                            (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst)))
                          (@Semiring.toAddCommMonoid.{u_1} K
                            (@CommSemiring.toSemiring.{u_1} K
                              (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst))))
                          (@Semiring.toModule.{u_1} K
                            (@CommSemiring.toSemiring.{u_1} K
                              (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst)))))
                        (@Atlas.Orthogonal.formD.{u_1} (Atlas.Chevalley.Catalogue.D_quadraticRank r) K
                          (@Field.toCommRing.{u_1} K inst))))))))
```

</details>

[Compiled evidence](../verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz) · [Full dependency audit](../verification/runs/chevalley-d-to-legacy-v1/20261018T163507-105).

Marked-generator compatibility:

- [`Atlas.Chevalley.Catalogue.D_identification_apply`](../Atlas/LinearGroups/Chevalley/Catalogue/DIdentification.lean#L23)
- [`Atlas.Chevalley.Comparison.TypeD.modelNaturalProjectiveHom_rho`](../Atlas/LinearGroups/Chevalley/Comparison/TypeDNaturalProjective.lean#L99)
- [`Atlas.Chevalley.Comparison.TypeD.modelNaturalProjectiveEquiv_X`](../Atlas/LinearGroups/Chevalley/Comparison/TypeDOrthogonalEquiv.lean#L38)
- [`Atlas.Chevalley.Comparison.TypeD.modelNaturalProjectiveEquiv_Y`](../Atlas/LinearGroups/Chevalley/Comparison/TypeDOrthogonalEquiv.lean#L44)

<a id="chevalley-b-to-legacy-v1"></a>

## family.B/chevalley ≃ family.B/quadratic

Domain: K an arbitrary finite field; q = Nat.card K; n : Nat, rank r = n+1 >= 2; every finite characteristic, including B2(F2).

| Interface | Exact Lean reference |
|---|---|
| Source model | [`Atlas.Chevalley.Catalogue.B`](../Atlas/LinearGroups/Chevalley/Catalogue/BConstruction.lean#L10) |
| Source group operations | [`Atlas.Chevalley.Catalogue.BGroup`](../Atlas/LinearGroups/Chevalley/Catalogue/BConstruction.lean#L13) |
| Target model | [`Atlas.Orthogonal.B`](../Atlas/LinearGroups/Orthogonal/BFamily.lean#L9) |
| Target group operations | [`Atlas.Chevalley.Catalogue.BQuadraticGroup`](../Atlas/LinearGroups/Chevalley/Catalogue/BIdentification.lean#L12) |
| Parameter map | [`Atlas.Chevalley.Catalogue.B_quadraticRank`](../Atlas/LinearGroups/Chevalley/Catalogue/BIdentification.lean#L9) |
| Isomorphism witness | [`Atlas.Chevalley.Catalogue.B_identification`](../Atlas/LinearGroups/Chevalley/Catalogue/BIdentification.lean#L16) |

Proof definition (verbatim source, in namespace `Atlas.Chevalley.Catalogue`):

```lean
def B_identification (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K]
    (hK : BFieldDomain n hn K) :
    B n hn K ≃* Atlas.Orthogonal.B (B_quadraticRank n) K := by
  letI : Finite K := hK
  exact Comparison.TypeB.projectiveEquiv n hn K
```

<details>
<summary>Complete compiled type, including implicit instances</summary>

```lean
Atlas.Chevalley.Catalogue.B_identification.{u_1} : (n : Nat) →
  (hn :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    (K : Type u_1) →
      [inst : Field.{u_1} K] →
        @Atlas.Chevalley.Catalogue.BFieldDomain.{u_1} n hn K inst →
          @MulEquiv.{u_1, u_1} (@Atlas.Chevalley.Catalogue.B.{u_1} n hn K inst)
            (@Atlas.Orthogonal.B.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K inst)
            (@MulOne.toMul.{u_1} (@Atlas.Chevalley.Catalogue.B.{u_1} n hn K inst)
              (@MulOneClass.toMulOne.{u_1} (@Atlas.Chevalley.Catalogue.B.{u_1} n hn K inst)
                (@Monoid.toMulOneClass.{u_1} (@Atlas.Chevalley.Catalogue.B.{u_1} n hn K inst)
                  (@DivInvMonoid.toMonoid.{u_1} (@Atlas.Chevalley.Catalogue.B.{u_1} n hn K inst)
                    (@Group.toDivInvMonoid.{u_1} (@Atlas.Chevalley.Catalogue.B.{u_1} n hn K inst)
                      (@Atlas.Chevalley.Catalogue.BGroup.{u_1} n hn K inst))))))
            (@MulOne.toMul.{u_1} (@Atlas.Orthogonal.B.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K inst)
              (@MulOneClass.toMulOne.{u_1}
                (@Atlas.Orthogonal.B.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K inst)
                (@Monoid.toMulOneClass.{u_1}
                  (@Atlas.Orthogonal.B.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K inst)
                  (@DivInvMonoid.toMonoid.{u_1}
                    (@Atlas.Orthogonal.B.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K inst)
                    (@Group.toDivInvMonoid.{u_1}
                      (@Atlas.Orthogonal.B.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K inst)
                      (@Atlas.Orthogonal.projectiveElementaryGroup.{u_1, u_1} K
                        (Atlas.Orthogonal.VectorB.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K) inst
                        (@Prod.instAddCommGroup.{u_1, u_1}
                          (Atlas.Orthogonal.VectorD.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K) K
                          (@Pi.addCommGroup.{0, u_1}
                            (Atlas.Orthogonal.Index (Atlas.Chevalley.Catalogue.B_quadraticRank n)) (fun a ↦ K) fun i ↦
                            @Ring.toAddCommGroup.{u_1} K
                              (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst)))
                          (@Ring.toAddCommGroup.{u_1} K
                            (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst))))
                        (@Prod.instModule.{u_1, u_1, u_1} K
                          (Atlas.Orthogonal.VectorD.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K) K
                          (@CommSemiring.toSemiring.{u_1} K
                            (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst)))
                          (@Pi.addCommMonoid.{0, u_1}
                            (Atlas.Orthogonal.Index (Atlas.Chevalley.Catalogue.B_quadraticRank n)) (fun a ↦ K) fun i ↦
                            @Semiring.toAddCommMonoid.{u_1} K
                              (@CommSemiring.toSemiring.{u_1} K
                                (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst))))
                          (@Semiring.toAddCommMonoid.{u_1} K
                            (@CommSemiring.toSemiring.{u_1} K
                              (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst))))
                          (@Pi.Function.module.{0, u_1, u_1}
                            (Atlas.Orthogonal.Index (Atlas.Chevalley.Catalogue.B_quadraticRank n)) K K
                            (@CommSemiring.toSemiring.{u_1} K
                              (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst)))
                            (@Semiring.toAddCommMonoid.{u_1} K
                              (@CommSemiring.toSemiring.{u_1} K
                                (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst))))
                            (@Semiring.toModule.{u_1} K
                              (@CommSemiring.toSemiring.{u_1} K
                                (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst)))))
                          (@Semiring.toModule.{u_1} K
                            (@CommSemiring.toSemiring.{u_1} K
                              (@CommRing.toCommSemiring.{u_1} K (@Field.toCommRing.{u_1} K inst)))))
                        (@Atlas.Orthogonal.formB.{u_1} (Atlas.Chevalley.Catalogue.B_quadraticRank n) K
                          (@Field.toCommRing.{u_1} K inst))))))))
```

</details>

[Compiled evidence](../verification/2026-10-26-cache-audit/full-dependency-extraction.log.gz) · [Full dependency audit](../verification/runs/chevalley-b-to-legacy-v1/20261018T165216-105).

Marked-generator compatibility:

- [`Atlas.Chevalley.Catalogue.B_identification_rho`](../Atlas/LinearGroups/Chevalley/Catalogue/BIdentification.lean#L23)
- [`Atlas.Chevalley.Comparison.TypeB.projectiveEquiv_X_long`](../Atlas/LinearGroups/Chevalley/Comparison/TypeBProjectiveEquiv.lean#L54)
- [`Atlas.Chevalley.Comparison.TypeB.projectiveEquiv_Y_long`](../Atlas/LinearGroups/Chevalley/Comparison/TypeBProjectiveEquiv.lean#L65)
- [`Atlas.Chevalley.Comparison.TypeB.projectiveEquiv_X_short`](../Atlas/LinearGroups/Chevalley/Comparison/TypeBProjectiveEquiv.lean#L76)
- [`Atlas.Chevalley.Comparison.TypeB.projectiveEquiv_Y_short`](../Atlas/LinearGroups/Chevalley/Comparison/TypeBProjectiveEquiv.lean#L86)

## family.F4: comparison scope

The isomorphism between the Chevalley and full split-Albert models remains unfinished. No certificate identifying them is claimed.

[Both constructions](../CATALOGUE.md#family-f4).

## family.G2: comparison scope

The research note records a marked Chevalley–octonion equivalence with ten passed local audit scopes, but its final preservation/registration and source export are outside this review snapshot. This review therefore supplies both model contracts, without claiming that their isomorphism certificate is included.

[Both constructions](../CATALOGUE.md#family-g2).

