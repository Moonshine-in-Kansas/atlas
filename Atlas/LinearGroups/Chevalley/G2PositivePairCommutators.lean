import Atlas.LinearGroups.Chevalley.G2PositivePairsRational
import Atlas.LinearGroups.Chevalley.G2ShortPairRational
import Atlas.LinearGroups.Chevalley.A2WeylCommutator

/-! Source candidates: all-ring descent of the remaining fourteen unordered
G2 positive-root pairs. No cancellation is performed in the target ring. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
include hdiamond

private theorem adjoint_g2_positive_pairs_twoStep_and_commute_intPolynomial
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let IntPoly := MvPolynomial (Fin 2) ℤ
    let s : IntPoly := MvPolynomial.X 0
    let t : IntPoly := MvPolynomial.X 1
    let ni := adjointWeyl P b IntPoly i 1
    let nj := adjointWeyl P b IntPoly j 1
    let Z (u : IntPoly) := nj * adjointX P b IntPoly i u * nj⁻¹
    let W (u : IntPoly) := (ni * nj) * adjointX P b IntPoly i u * (ni * nj)⁻¹
    let V (u : IntPoly) := ni * adjointX P b IntPoly j u * ni⁻¹
    let H (u : IntPoly) := (nj * ni) * adjointX P b IntPoly j u * (nj * ni)⁻¹
    ⁅adjointX P b IntPoly i s, W t⁆ = V (3*s*t) ∧
    ⁅adjointX P b IntPoly j s, V t⁆ = H (s*t) ∧
    ⁅Z s, W t⁆ = H (3*s*t) ∧
    Commute (adjointX P b IntPoly i s) (V t) ∧
    Commute (adjointX P b IntPoly i s) (H t) ∧
    Commute (adjointX P b IntPoly j s) (Z t) ∧
    Commute (adjointX P b IntPoly j s) (W t) ∧
    Commute (adjointX P b IntPoly j s) (H t) ∧
    Commute (Z s) (V t) ∧ Commute (Z s) (H t) ∧
    Commute (W s) (V t) ∧ Commute (W s) (H t) ∧ Commute (V s) (H t) := by
  dsimp only
  let φ : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hφ : Function.Injective φ :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have h := adjoint_g2_positive_pairs_twoStep_and_commute_rat P b hdiamond (MvPolynomial (Fin 2) ℚ)
    i j hne hij hji (MvPolynomial.X 0) (MvPolynomial.X 1)
  dsimp only at h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h1
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h2
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h3
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h4.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h5.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h6.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h7.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h8.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h9.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h10.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h11.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h12.eq
  · apply adjointMap_injective P b φ hφ
    simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h13.eq

/-- The literal G2 pair identity over every commutative ring, including characteristics 2 and 3. -/
theorem adjoint_g2_positive_pairs_twoStep_and_commute
    (R : Type*) [CommRing R]
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (s t : R) :
    let ni := adjointWeyl P b R i 1
    let nj := adjointWeyl P b R j 1
    let Z (u : R) := nj * adjointX P b R i u * nj⁻¹
    let W (u : R) := (ni * nj) * adjointX P b R i u * (ni * nj)⁻¹
    let V (u : R) := ni * adjointX P b R j u * ni⁻¹
    let H (u : R) := (nj * ni) * adjointX P b R j u * (nj * ni)⁻¹
    ⁅adjointX P b R i s, W t⁆ = V (3*s*t) ∧
    ⁅adjointX P b R j s, V t⁆ = H (s*t) ∧
    ⁅Z s, W t⁆ = H (3*s*t) ∧
    Commute (adjointX P b R i s) (V t) ∧
    Commute (adjointX P b R i s) (H t) ∧
    Commute (adjointX P b R j s) (Z t) ∧
    Commute (adjointX P b R j s) (W t) ∧
    Commute (adjointX P b R j s) (H t) ∧
    Commute (Z s) (V t) ∧ Commute (Z s) (H t) ∧
    Commute (W s) (V t) ∧ Commute (W s) (H t) ∧ Commute (V s) (H t) := by
  let ev : MvPolynomial (Fin 2) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun k : Fin 2 => if k = 0 then s else t)
  have hzero : ev (MvPolynomial.X 0) = s := by simp [ev]
  have hone : ev (MvPolynomial.X 1) = t := by simp [ev]
  have h := adjoint_g2_positive_pairs_twoStep_and_commute_intPolynomial P b hdiamond i j hne hij hji
  dsimp only at h ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using congrArg (adjointMap P b ev) h1
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using congrArg (adjointMap P b ev) h2
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using congrArg (adjointMap P b ev) h3
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h4.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h5.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h6.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h7.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h8.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h9.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h10.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h11.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h12.map (adjointMap P b ev)
  · simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using h13.map (adjointMap P b ev)

private theorem adjointX_g2_short_pair_commutator_intPolynomial
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    let IntPoly := MvPolynomial (Fin 2) ℤ
    let s : IntPoly := MvPolynomial.X 0
    let t : IntPoly := MvPolynomial.X 1
    let ni := adjointWeyl P b IntPoly i 1
    let nj := adjointWeyl P b IntPoly j 1
    ⁅adjointX P b IntPoly i s, nj * adjointX P b IntPoly i t * nj⁻¹⁆ =
      ((ni*nj) * adjointX P b IntPoly i (-2*s*t) * (ni*nj)⁻¹) *
      (ni * adjointX P b IntPoly j (-3*s^2*t) * ni⁻¹) *
      ((nj*ni) * adjointX P b IntPoly j (-3*s*t^2) * (nj*ni)⁻¹) := by
  dsimp only
  let φ : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hφ : Function.Injective φ :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have h := adjointX_g2_short_pair_commutator_rat P b hdiamond (MvPolynomial (Fin 2) ℚ)
    i j hne hij hji (MvPolynomial.X 0) (MvPolynomial.X 1)
  dsimp only at h
  apply adjointMap_injective P b φ hφ
  simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, φ, MvPolynomial.map_X] using h

/-- The literal G2 pair identity over every commutative ring, including characteristics 2 and 3. -/
theorem adjointX_g2_short_pair_commutator
    (R : Type*) [CommRing R]
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    (s t : R) :
    let ni := adjointWeyl P b R i 1
    let nj := adjointWeyl P b R j 1
    ⁅adjointX P b R i s, nj * adjointX P b R i t * nj⁻¹⁆ =
      ((ni*nj) * adjointX P b R i (-2*s*t) * (ni*nj)⁻¹) *
      (ni * adjointX P b R j (-3*s^2*t) * ni⁻¹) *
      ((nj*ni) * adjointX P b R j (-3*s*t^2) * (nj*ni)⁻¹) := by
  let ev : MvPolynomial (Fin 2) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun k : Fin 2 => if k = 0 then s else t)
  have hzero : ev (MvPolynomial.X 0) = s := by simp [ev]
  have hone : ev (MvPolynomial.X 1) = t := by simp [ev]
  have h := adjointX_g2_short_pair_commutator_intPolynomial P b hdiamond i j hne hij hji
  dsimp only at h ⊢
  simpa only [map_commutatorElement, map_mul, map_inv, map_pow, map_neg, map_ofNat, adjointMap_x, adjointMap_weyl_one, map_one, hzero, hone] using congrArg (adjointMap P b ev) h

end Atlas.Chevalley
