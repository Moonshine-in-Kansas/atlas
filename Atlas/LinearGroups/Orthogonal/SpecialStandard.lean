import Atlas.LinearGroups.Orthogonal.DeterminantSign
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Atlas.LinearGroups.Orthogonal.EvenGeneration

/-! # Determinant-one kernels in the actual standard B and D groups -/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F]

abbrev SO_B (n : ℕ) (F : Type*) [Field F] := ↥(specialSubgroup (formB n F))
abbrev SO_DPlus (n : ℕ) (F : Type*) [Field F] := ↥(specialSubgroup (formD n F))

theorem polarB_nondegenerate (h2 : (2 : F) ≠ 0) : (formB n F).polarBilin.Nondegenerate := by
  constructor
  · exact polarB_separating_of_two_ne_zero h2
  · intro x hx
    apply polarB_separating_of_two_ne_zero h2 x
    intro y
    rw [Atlas.Quadratic.polar_swap]
    exact hx y

theorem formD_anisotropic (i : Fin n) : formD n F (e i + f i) = 1 := by
  rw [QuadraticMap.map_add (formD n F)]
  change formD n F (e i) + formD n F (f i) + (formD n F).polarBilin (e i) (f i) = 1
  rw [formD_e, formD_f, polarD_ef, zero_add, zero_add]

theorem card_specialB_mul_two (h2 : (2 : F) ≠ 0) :
    Nat.card (SO_B n F) * 2 = Nat.card (O_B n F) := by
  have h := card_special_mul_sign (formB n F) (polarB_nondegenerate h2) z
    (by rw [formB_z]; exact one_ne_zero)
  simpa only [if_neg h2] using h

theorem card_specialD_mul_sign (hn : 0 < n) :
    Nat.card (SO_DPlus n F) * (if (2 : F) = 0 then 1 else 2) = Nat.card (O_DPlus n F) := by
  let i : Fin n := ⟨0, hn⟩
  exact card_special_mul_sign (formD n F) polarD_nondegenerate (e i + f i)
    (by rw [formD_anisotropic]; exact one_ne_zero)

/-- In characteristic two the full split-D group has trivial determinant; Omega still needs Dickson. -/
theorem even_specialD_eq_top [CharP F 2] : specialSubgroup (formD n F) = ⊤ := by
  apply top_unique
  intro g _
  rw [mem_specialSubgroup]
  apply Units.ext
  change (g.val.det : F) = 1
  have h := Atlas.Quadratic.isometry_det_sq (formD n F) polarD_nondegenerate (isometryCarrierEquiv _ g)
  change (g.val.det : F)^2 = 1 at h
  rcases sq_eq_one_iff.mp h with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

/-- For finite characteristic-two B, actual Siegel generation makes the determinant trivial. -/
theorem even_specialB_eq_top [CharP F 2] [PerfectRing F 2] : specialSubgroup (formB n F) = ⊤ := by
  apply top_unique
  rw [← even_elementary_eq_top]
  exact elementary_le_special (formB n F)

end Atlas.Orthogonal
