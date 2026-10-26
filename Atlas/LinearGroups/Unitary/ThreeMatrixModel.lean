import Atlas.LinearGroups.Unitary.WittThree

/-! # Two-way matrix transport for the actual hyperbolic SU₃ model -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def threeUnitaryOfMatrix (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (R : Matrix (Fin 3) (Fin 3) K)
    (hR : ∀ x y, hyperbolicThreeForm (F := F) (R *ᵥ x) (R *ᵥ y) =
      hyperbolicThreeForm (F := F) x y) (hdet : R.det = 1) : SU F K 3 hdeg := by
  let P := wittThreeMatrix a b
  have hP := wittThreeMatrix_det_unit a b ha
  refine ⟨P * R * P⁻¹, (mem_u_iff_preserves_hermitian hdeg _).mpr ?_, ?_⟩
  · intro x y
    have hx : P *ᵥ (P⁻¹ *ᵥ x) = x := by
      rw [mulVec_mulVec, mul_nonsing_inv P hP, one_mulVec]
    have hy : P *ᵥ (P⁻¹ *ᵥ y) = y := by
      rw [mulVec_mulVec, mul_nonsing_inv P hP, one_mulVec]
    simp only [← mulVec_mulVec]
    rw [wittThreeMatrix_preserves a b ha hb, hR]
    exact (wittThreeMatrix_preserves a b ha hb (P⁻¹ *ᵥ x) (P⁻¹ *ᵥ y)).symm.trans
      (congrArg₂ (hermitian F K) hx hy)
  · change (P * R * P⁻¹).det = 1
    simp only [det_mul, hdet, mul_one, det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_inv_cancel₀ (isUnit_iff_ne_zero.mp hP)

theorem three_witt_conjugate_det (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (g : SU F K 3 hdeg) :
    ((wittThreeMatrix a b)⁻¹ * g.val * wittThreeMatrix a b).det = 1 := by
  simp only [det_mul, show g.val.det = 1 from g.prop.2, mul_one, det_nonsing_inv,
    Ring.inverse_eq_inv]
  exact inv_mul_cancel₀ (isUnit_iff_ne_zero.mp (wittThreeMatrix_det_unit a b ha))

theorem three_witt_conjugate_preserves (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (g : SU F K 3 hdeg) (x y : Fin 3 → K) :
    hyperbolicThreeForm (F := F)
      (((wittThreeMatrix a b)⁻¹ * g.val * wittThreeMatrix a b) *ᵥ x)
      (((wittThreeMatrix a b)⁻¹ * g.val * wittThreeMatrix a b) *ᵥ y) =
        hyperbolicThreeForm (F := F) x y := by
  let P := wittThreeMatrix a b
  have hP := wittThreeMatrix_det_unit a b ha
  have hx : P *ᵥ ((P⁻¹ * g.val * P) *ᵥ x) = g.val *ᵥ (P *ᵥ x) := by
    simp only [mulVec_mulVec, ← mul_assoc, mul_nonsing_inv P hP, one_mul]
  have hy : P *ᵥ ((P⁻¹ * g.val * P) *ᵥ y) = g.val *ᵥ (P *ᵥ y) := by
    simp only [mulVec_mulVec, ← mul_assoc, mul_nonsing_inv P hP, one_mul]
  rw [← wittThreeMatrix_preserves a b ha hb, hx, hy,
    u_preserves_hermitian hdeg (⟨g.val, g.prop.1⟩ : U F K 3 hdeg), wittThreeMatrix_preserves a b ha hb]

end Atlas.Unitary
