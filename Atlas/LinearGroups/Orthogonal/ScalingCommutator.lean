import Atlas.LinearGroups.Orthogonal.RootSubgroup
import Mathlib.GroupTheory.Commutator.Basic

/-! # A scalar normalizer expresses a Siegel generator as an elementary commutator -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
open scoped commutatorElement
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem siegel_mem_commutator_of_scaling (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) (t : isometrySubgroup Q) (ht : t ∈ elementarySubgroup Q)
    (c : F) (hc : c ≠ 1) (htu : t.val u = c • u) (htv : t.val v = v) :
    siegelElement Q u v hu huv ∈ ⁅elementarySubgroup Q, elementarySubgroup Q⁆ := by
  let p := (c-1)⁻¹ • v
  have hp : Q.polarBilin u p = 0 := by
    change Q.polarBilin u ((c-1)⁻¹ • v) = 0
    rw [map_smul, huv, smul_zero]
  have htp : t.val p = p := by dsimp [p]; rw [map_smul, htv]
  let r := rootParameterHom Q u hu (Multiplicative.ofAdd ⟨p, hp⟩)
  have hr : r ∈ elementarySubgroup Q := siegelElement_mem _ _ _ _ _
  have hcp : Q.polarBilin u (c • p) = 0 := by rw [map_smul, hp, smul_zero]
  have hconj : t*r*t⁻¹ = rootParameterHom Q u hu (Multiplicative.ofAdd ⟨c • p, hcp⟩) := by
    change t * siegelElement Q u p hu hp * t⁻¹ = _
    rw [siegelElement_conj]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change siegel Q (t.val u) (t.val p) x = siegel Q u (c • p) x
    rw [htu, htp]
    exact siegel_scale Q u p x c
  have hcoef : c • p + -p = v := by
    have hc' := sub_ne_zero.mpr hc
    dsimp [p]
    match_scalars <;> field_simp <;> ring
  have he : ⁅t,r⁆ = siegelElement Q u v hu huv := by
    rw [commutatorElement_def, hconj]
    change rootParameterHom Q u hu (Multiplicative.ofAdd ⟨c • p, hcp⟩) *
      (rootParameterHom Q u hu (Multiplicative.ofAdd ⟨p, hp⟩))⁻¹ =
        rootParameterHom Q u hu (Multiplicative.ofAdd ⟨v, huv⟩)
    rw [← map_inv, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hcoef
  rw [← he]
  exact Subgroup.commutator_mem_commutator ht hr

end Atlas.Orthogonal
