import Atlas.LinearAlgebra.QuadraticWittTwo
import Atlas.LinearAlgebra.QuadraticSingularSpan
import Atlas.LinearAlgebra.QuadraticAnisotropicSplit
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! # Singular witnesses in polar hyperplanes of Witt index at least two -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

include hQ in
theorem polar_restriction_ne_zero (u d : V) (hu : u ∉ Submodule.span F {d}) :
    (Q.polarBilin u).comp (linePerp Q d).subtype ≠ 0 := by
  intro h
  apply hu
  have hr : Q.polarBilin.IsRefl := fun x y h => (polar_swap Q y x).trans h
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ hr (Submodule.span F {d})]
  intro x hx
  have hdx := hx d (Submodule.subset_span (Set.mem_singleton d))
  have hxd : Q.polarBilin x d = 0 := (polar_swap Q x d).trans hdx
  have hp := LinearMap.congr_fun h (⟨x, hxd⟩ : linePerp Q d)
  exact (polar_swap Q x u).trans hp

include hQ in
/-- Away from the perpendicular line itself, a polar functional has a singular witness. -/
theorem exists_singular_perpendicular_witness (H : WittTwoFrame Q) (h2 : (2 : F) ≠ 0)
    (u d : V) (hu : u ∉ Submodule.span F {d}) :
    ∃ w, Q w = 0 ∧ Q.polarBilin w d = 0 ∧ Q.polarBilin u w ≠ 0 := by
  obtain ⟨a, b, ha, hb, hab, had, hbd⟩ := hyperbolic_pair_in_perpendicular Q H hQ h2 d
  let a' : linePerp Q d := ⟨a, had⟩
  let b' : linePerp Q d := ⟨b, hbd⟩
  have hp : (linePerpForm Q d).polarBilin a' b' = 1 := by
    rw [linePerpForm_polar]
    exact hab
  obtain ⟨w, hw, hlw⟩ := exists_singular_functional_ne_zero (linePerpForm Q d) a' b'
    ha hb hp ((Q.polarBilin u).comp (linePerp Q d).subtype)
    (polar_restriction_ne_zero Q hQ u d hu)
  exact ⟨w.val, hw, w.prop, hlw⟩

end Atlas.Quadratic
