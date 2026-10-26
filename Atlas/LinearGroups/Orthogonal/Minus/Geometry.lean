import Atlas.LinearGroups.Orthogonal.Minus.SingularCount
import Atlas.LinearGroups.Orthogonal.Transitivity
import Atlas.LinearAlgebra.QuadraticPairCount

/-! Full-isometry transport and singular-partner counts for the nonsplit form. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem radical_eq_bot (hdeg : Module.finrank F K = 2) (k : ℕ) :
    (form hdeg k).radical = ⊥ := by
  apply bot_unique
  intro x hx
  rw [Submodule.mem_bot]
  exact polar_separating hdeg k x (fun w => LinearMap.congr_fun hx.2 w)

theorem exists_hyperbolic_partner (hdeg : Module.finrank F K = 2) (k : ℕ)
    (u : Vector k F K) (hu : u ≠ 0) (hq : form hdeg k u = 0) :
    ∃ f, form hdeg k f = 0 ∧ (form hdeg k).polarBilin u f = 1 :=
  Atlas.Quadratic.exists_hyperbolic_partner _ u hq
    (fun h => hu (polar_separating hdeg k u h))

theorem singular_transitive (hdeg : Module.finrank F K = 2) (k : ℕ)
    (u v : Vector k F K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : form hdeg k u = 0) (hqv : form hdeg k v = 0) :
    ∃ g : O hdeg k, g.val u = v := by
  obtain ⟨g,hg⟩ := Atlas.Quadratic.exists_isometry_singular (form hdeg k)
    (radical_eq_bot hdeg k) u v hu hv hqu hqv
  exact ⟨(isometryCarrierEquiv _).symm g,hg⟩

theorem pair_transitive (hdeg : Module.finrank F K = 2) (k : ℕ)
    (e f u v : Vector k F K)
    (he : form hdeg k e = 0) (hf : form hdeg k f = 0)
    (hu : form hdeg k u = 0) (hv : form hdeg k v = 0)
    (hef : (form hdeg k).polarBilin e f = 1)
    (huv : (form hdeg k).polarBilin u v = 1) :
    ∃ g : O hdeg k, g.val e = u ∧ g.val f = v := by
  obtain ⟨g,hg⟩ := Atlas.Quadratic.exists_isometry_hyperbolic_pair (form hdeg k)
    (radical_eq_bot hdeg k) e f u v he hf hu hv hef huv
  exact ⟨(isometryCarrierEquiv _).symm g,hg⟩

theorem card_partners (hdeg : Module.finrank F K = 2) (k : ℕ)
    (u : Vector k F K) (hu : u ≠ 0) (hq : form hdeg k u = 0) :
    Nat.card {x : Vector k F K // form hdeg k x = 0 ∧ (form hdeg k).polarBilin u x = 1} =
      Nat.card F ^ (2*k) := by
  obtain ⟨f,hf,huf⟩ := exists_hyperbolic_partner hdeg k u hu hq
  rw [Atlas.Quadratic.card_partners _ u f hq hf huf,vector_finrank hdeg]
  congr 1
end Atlas.Orthogonal.Minus
