import Atlas.Lattices.EisensteinCongruence
import Atlas.Lattices.EisensteinScalar

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Lattices
open Atlas.Algebra
open scoped QuadraticAlgebra BigOperators


def eisensteinCoordinateEmbedding :
    EisensteinCoordinates →ₗ[ℤ] EisensteinRationalCoordinates where
  toFun z i := eisensteinToRational (z i)
  map_add' z w := by funext i; exact map_add _ _ _
  map_smul' r z := by
    funext i
    exact map_zsmul eisensteinToRational r (z i)

/-- The actual image of the integral congruence module, prior to any comparison. -/
def rationalEisensteinLattice : Submodule ℤ EisensteinRationalCoordinates :=
  (eisensteinLeechModule.restrictScalars ℤ).map eisensteinCoordinateEmbedding

theorem eisensteinLeechModule_contains_nine (w : EisensteinCoordinates) :
    (9 : Eisenstein) • w ∈ eisensteinLeechModule := by
  have h := eisensteinLeechModule_contains_multiple ((-eisensteinTheta) • w)
  have he : (3 * eisensteinTheta) * (-eisensteinTheta) = (9 : Eisenstein) := by
    calc
      _ = -3 * eisensteinTheta ^ 2 := by ring
      _ = 9 := by rw [eisensteinTheta_sq]; ring
  simpa only [smul_smul, he] using h

theorem rationalEisensteinLattice_full_span :
    Submodule.span ℚ (rationalEisensteinLattice : Set EisensteinRationalCoordinates) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro z
  have hm (i : Fin 12) (a : Eisenstein) :
      eisensteinCoordinateEmbedding ((9 : Eisenstein) • Pi.single i a) ∈
        Submodule.span ℚ (rationalEisensteinLattice : Set EisensteinRationalCoordinates) :=
    Submodule.subset_span (Submodule.mem_map.mpr
      ⟨_, eisensteinLeechModule_contains_nine _, rfl⟩)
  have he : z = ∑ i : Fin 12, (
      ((z i).re / 9) • eisensteinCoordinateEmbedding ((9 : Eisenstein) • Pi.single i 1) +
      ((z i).im / 9) • eisensteinCoordinateEmbedding
        ((9 : Eisenstein) • Pi.single i eisensteinOmega)) := by
    have hi (i : Fin 12) :
        ((z i).re / 9) • eisensteinCoordinateEmbedding ((9 : Eisenstein) • Pi.single i 1) +
        ((z i).im / 9) • eisensteinCoordinateEmbedding
          ((9 : Eisenstein) • Pi.single i eisensteinOmega) = Pi.single i (z i) := by
      funext j
      by_cases hj : j = i
      · subst j
        apply QuadraticAlgebra.ext <;>
          simp [eisensteinCoordinateEmbedding, eisensteinToRational,
            eisensteinOmega, QuadraticAlgebra.omega, Pi.single_apply, smul_eq_mul]
      · apply QuadraticAlgebra.ext <;>
          simp [eisensteinCoordinateEmbedding, eisensteinToRational,
            eisensteinOmega, QuadraticAlgebra.omega, Pi.single_apply, smul_eq_mul, hj]
    simp_rw [hi]
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hm i 1))
    (Submodule.smul_mem _ _ (hm i eisensteinOmega))

theorem rationalEisensteinCoordinates_finrank :
    Module.finrank ℚ EisensteinRationalCoordinates = 24 := by
  simp [EisensteinRationalCoordinates, EisensteinRational, Module.finrank_pi_fintype, QuadraticAlgebra.finrank_eq_two]

end Atlas.Lattices
