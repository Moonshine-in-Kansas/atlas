import Atlas.LinearGroups.Unitary.ThreeBruhat

/-! The full isotropic-line stabilizer in hyperbolic three-dimensional coordinates.
Every preserving determinant-one matrix fixing the first line is explicitly U·T. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem three_line_stabilizer_factor (hdeg : Module.finrank F K = 2)
    (g : Matrix (Fin 3) (Fin 3) K) (hd : g.det = 1)
    (hp : ∀ x y, hyperbolicThreeForm (F := F) (g *ᵥ x) (g *ᵥ y) =
      hyperbolicThreeForm (F := F) x y)
    (t : K) (ht : t ≠ 0) (hcol : g *ᵥ Pi.single 0 1 = t • Pi.single 0 1) :
    ∃ a b : K, rootThreeCondition (F := F) a b ∧
      g = rootThreeMatrix (F := F) a b * fullTorusThreeMatrix (F := F) t := by
  have hbt : conjugation F K t ≠ 0 := (map_ne_zero _).mpr ht
  have h00 : g 0 0 = t := by simpa using congrFun hcol 0
  have h10 : g 1 0 = 0 := by simpa using congrFun hcol 1
  have h20 : g 2 0 = 0 := by simpa using congrFun hcol 2
  have h02 := hp (Pi.single 0 1) (Pi.single 2 1)
  have h01 := hp (Pi.single 0 1) (Pi.single 1 1)
  have h12 := hp (Pi.single 1 1) (Pi.single 2 1)
  have h22 := hp (Pi.single 2 1) (Pi.single 2 1)
  simp only [mulVec_single_one, hyperbolicThreeForm] at h02 h01 h12 h22
  simp [Pi.single_apply, h00, h10, h20] at h02 h01 h12 h22
  have h21 : g 2 1 = 0 := h01.resolve_left ht
  have hdiag : g 2 2 = (conjugation F K t)⁻¹ := by
    have he := congrArg (conjugation F K) h02
    simp only [map_mul, conjugation_conjugation hdeg, map_one] at he
    apply mul_left_cancel₀ hbt
    simpa only [mul_inv_cancel₀ hbt] using he
  have h11 : g 1 1 = conjugation F K t / t := by
    rw [Matrix.det_fin_three, h10, h20, h21, h00, hdiag] at hd
    simp only [mul_zero, zero_mul, add_zero, sub_zero, zero_add] at hd
    apply (eq_div_iff ht).mpr
    have he := congrArg (fun x : K => x * conjugation F K t) hd
    field_simp at he
    linear_combination he
  have htop : g 0 1 = -conjugation F K t * conjugation F K (g 1 2) := by
    rw [h21, h11, hdiag] at h12
    simp only [map_inv₀, conjugation_conjugation hdeg, zero_mul, add_zero] at h12
    field_simp at h12
    linear_combination h12
  let a := g 1 2 * conjugation F K t
  let b := g 0 2 * conjugation F K t
  have hab : rootThreeCondition (F := F) a b := by
    rw [hdiag] at h22
    simp only [map_inv₀, conjugation_conjugation hdeg] at h22
    dsimp [rootThreeCondition, a, b]
    simp only [map_mul, conjugation_conjugation hdeg]
    field_simp at h22
    linear_combination h22
  refine ⟨a, b, hab, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootThreeMatrix, fullTorusThreeMatrix, Matrix.mul_diagonal,
      a, b, map_mul, conjugation_conjugation hdeg, h00, h10, h20, h21, hdiag, h11, htop,
      ht, hbt] <;> field_simp <;> ring
end Atlas.Unitary
