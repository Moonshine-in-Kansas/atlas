import Atlas.LinearGroups.Orthogonal.Radical
import Atlas.LinearAlgebra.QuadraticHyperbolic

/-! # Singular vectors admit hyperbolic partners in the actual standard forms -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F]

theorem exists_hyperbolic_partnerD (u : VectorD n F) (hu : u ≠ 0)
    (hq : formD n F u = 0) :
    ∃ f, formD n F f = 0 ∧ (formD n F).polarBilin u f = 1 :=
  Atlas.Quadratic.exists_hyperbolic_partner _ u hq
    (fun h => hu (polarD_separating u h))

theorem exists_hyperbolic_partnerB (u : VectorB n F) (hu : u ≠ 0)
    (hq : formB n F u = 0) :
    ∃ f, formB n F f = 0 ∧ (formB n F).polarBilin u f = 1 :=
  Atlas.Quadratic.exists_hyperbolic_partner _ u hq
    (fun h => hu (quadratic_radicalB_trivial u h hq))

end Atlas.Orthogonal
