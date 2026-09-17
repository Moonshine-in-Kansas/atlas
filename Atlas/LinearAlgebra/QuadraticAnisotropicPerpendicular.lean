import Atlas.LinearAlgebra.QuadraticSiegelResidual
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! # An anisotropic vector perpendicular to two prescribed vectors -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

include hQ in
/-- In dimension at least five, a codimension-two perpendicular space cannot be
entirely singular for a polar-nondegenerate quadratic form. -/
theorem exists_anisotropic_perpendicular_pair (hd : 5 ≤ Module.finrank F V)
    (u v : V) : ∃ w : V, Q w ≠ 0 ∧ Q.polarBilin u w = 0 ∧
      Q.polarBilin v w = 0 := by
  classical
  let S : Submodule F V := Submodule.span F {u, v}
  let W := LinearMap.BilinForm.orthogonal Q.polarBilin S
  have hs : Module.finrank F S ≤ 2 := by
    have h := finrank_span_le_card (R := F) ({u, v} : Set V)
    exact h.trans (by simpa using Finset.card_insert_le u ({v} : Finset V))
  have hw : Module.finrank F W = Module.finrank F V - Module.finrank F S :=
    LinearMap.BilinForm.finrank_orthogonal hQ S
  by_contra! hn
  have hz : ∀ w ∈ W, Q w = 0 := by
    intro w hw
    by_contra hnw
    exact hn w hnw (hw u (Submodule.subset_span (by simp)))
      (hw v (Submodule.subset_span (by simp)))
  have hle : W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W := by
    intro w hw z hz'
    change Q.polarBilin z w = 0
    have h := QuadraticMap.map_add Q z w
    change Q (z+w) = Q z + Q w + Q.polarBilin z w at h
    rw [hz z hz', hz w hw, hz (z+w) (W.add_mem hz' hw), zero_add, zero_add] at h
    exact h.symm
  have hr := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ W] at hr
  omega
end Atlas.Quadratic
