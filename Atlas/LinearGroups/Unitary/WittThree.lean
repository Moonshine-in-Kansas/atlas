import Atlas.LinearGroups.Unitary.GenerationThree

/-! Transfer of the explicit three-dimensional root matrices to the retained
standard Hermitian special unitary carrier. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Insert the anisotropic coordinate between the two hyperbolic coordinates. -/
def wittThreeMatrix (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1, 0, 1-b; a, 0, -b*a]

omit [Finite K] in
theorem wittThreeMatrix_det (a b : K) : (wittThreeMatrix a b).det = a := by
  simp [wittThreeMatrix, det_fin_three]
  ring

theorem wittThreeMatrix_preserves (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (x y : Fin 3 → K) :
    hermitian F K (wittThreeMatrix a b *ᵥ x) (wittThreeMatrix a b *ᵥ y) =
      hyperbolicThreeForm (F := F) x y := by
  have h := wittPlaneMatrix_preserves a b ha hb ![x 0, x 2] ![y 0, y 2]
  have h' := congrArg (fun z => x 1 * conjugation F K (y 1) + z) h
  simpa [hermitian, hyperbolicPlaneForm, hyperbolicThreeForm, wittThreeMatrix,
    wittPlaneMatrix, mulVec, dotProduct, Fin.sum_univ_succ, add_assoc, add_left_comm] using h'

theorem wittThreeMatrix_det_unit (a b : K) (ha : a * conjugation F K a = -1) :
    IsUnit (wittThreeMatrix a b).det := by
  rw [wittThreeMatrix_det]
  apply isUnit_iff_ne_zero.mpr
  intro h
  simp [h] at ha

/-- A genuine actual SU₃ element, obtained by the proved Hermitian coordinate change. -/
def rootThreeUnitary (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (c d : K) (hcd : rootThreeCondition (F := F) c d) : SU F K 3 hdeg := by
  let P := wittThreeMatrix a b
  let R := rootThreeMatrix (F := F) c d
  have hP := wittThreeMatrix_det_unit a b ha
  refine ⟨P * R * P⁻¹, (mem_u_iff_preserves_hermitian hdeg _).mpr ?_, ?_⟩
  · intro x y
    have hx : P *ᵥ (P⁻¹ *ᵥ x) = x := by
      rw [mulVec_mulVec, mul_nonsing_inv P hP, one_mulVec]
    have hy : P *ᵥ (P⁻¹ *ᵥ y) = y := by
      rw [mulVec_mulVec, mul_nonsing_inv P hP, one_mulVec]
    simp only [← mulVec_mulVec]
    rw [wittThreeMatrix_preserves a b ha hb, rootThreeMatrix_preserves hdeg c d hcd]
    exact (wittThreeMatrix_preserves a b ha hb (P⁻¹ *ᵥ x) (P⁻¹ *ᵥ y)).symm.trans
      (congrArg₂ (hermitian F K) hx hy)
  · change (P * R * P⁻¹).det = 1
    simp only [det_mul, R, rootThreeMatrix_det, mul_one, det_nonsing_inv,
      Ring.inverse_eq_inv]
    exact mul_inv_cancel₀ (isUnit_iff_ne_zero.mp hP)

/-- The root law holds inside the actual standard special unitary group. -/
theorem rootThreeUnitary_mul (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (c d e f : K) (hcd : rootThreeCondition (F := F) c d)
    (hef : rootThreeCondition (F := F) e f) :
    rootThreeUnitary hdeg a b ha hb c d hcd * rootThreeUnitary hdeg a b ha hb e f hef =
      rootThreeUnitary hdeg a b ha hb (c+e) (d+f-conjugation F K c*e)
        (rootThreeCondition_mul hdeg c d e f hcd hef) := by
  apply Subtype.ext
  change (wittThreeMatrix a b * rootThreeMatrix (F := F) c d * (wittThreeMatrix a b)⁻¹) *
    (wittThreeMatrix a b * rootThreeMatrix (F := F) e f * (wittThreeMatrix a b)⁻¹) = _
  simp only [mul_assoc, ← mul_assoc (wittThreeMatrix a b)⁻¹ (wittThreeMatrix a b),
    nonsing_inv_mul _ (wittThreeMatrix_det_unit a b ha), one_mul]
  change _ = wittThreeMatrix a b * rootThreeMatrix (F := F) (c+e)
    (d+f-conjugation F K c*e) * (wittThreeMatrix a b)⁻¹
  rw [← rootThreeMatrix_mul]
  simp only [mul_assoc]
end Atlas.Unitary
