import Atlas.LinearGroups.Orthogonal.Radical
import Atlas.LinearAlgebra.QuadraticPairTransport

/-! # Full isometry transitivity for the actual B and split D quadratic forms -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F]

theorem radicalD_eq_bot : (formD n F).radical = ⊥ := by
  apply bot_unique
  intro x hx
  rw [Submodule.mem_bot]
  apply polarD_separating x
  intro w
  exact LinearMap.congr_fun hx.2 w

theorem radicalB_eq_bot : (formB n F).radical = ⊥ := by
  apply bot_unique
  intro x hx
  rw [Submodule.mem_bot]
  exact quadratic_radicalB_trivial x (fun w => LinearMap.congr_fun hx.2 w) hx.1

theorem singular_transitiveD (u v : VectorD n F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : formD n F u = 0) (hqv : formD n F v = 0) :
    ∃ g : O_DPlus n F, g.val u = v := by
  obtain ⟨g, hg⟩ := Atlas.Quadratic.exists_isometry_singular (formD n F)
    radicalD_eq_bot u v hu hv hqu hqv
  exact ⟨(isometryCarrierEquiv _).symm g, hg⟩

theorem singular_transitiveB (u v : VectorB n F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : formB n F u = 0) (hqv : formB n F v = 0) :
    ∃ g : O_B n F, g.val u = v := by
  obtain ⟨g, hg⟩ := Atlas.Quadratic.exists_isometry_singular (formB n F)
    radicalB_eq_bot u v hu hv hqu hqv
  exact ⟨(isometryCarrierEquiv _).symm g, hg⟩

theorem pair_transitiveD (e f u v : VectorD n F)
    (he : formD n F e = 0) (hf : formD n F f = 0)
    (hu : formD n F u = 0) (hv : formD n F v = 0)
    (hef : (formD n F).polarBilin e f = 1) (huv : (formD n F).polarBilin u v = 1) :
    ∃ g : O_DPlus n F, g.val e = u ∧ g.val f = v := by
  obtain ⟨g, hg⟩ := Atlas.Quadratic.exists_isometry_hyperbolic_pair (formD n F)
    radicalD_eq_bot e f u v he hf hu hv hef huv
  exact ⟨(isometryCarrierEquiv _).symm g, hg⟩

theorem pair_transitiveB (e f u v : VectorB n F)
    (he : formB n F e = 0) (hf : formB n F f = 0)
    (hu : formB n F u = 0) (hv : formB n F v = 0)
    (hef : (formB n F).polarBilin e f = 1) (huv : (formB n F).polarBilin u v = 1) :
    ∃ g : O_B n F, g.val e = u ∧ g.val f = v := by
  obtain ⟨g, hg⟩ := Atlas.Quadratic.exists_isometry_hyperbolic_pair (formB n F)
    radicalB_eq_bot e f u v he hf hu hv hef huv
  exact ⟨(isometryCarrierEquiv _).symm g, hg⟩

end Atlas.Orthogonal
