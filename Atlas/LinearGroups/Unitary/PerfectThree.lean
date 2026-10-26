import Atlas.LinearGroups.Unitary.TransvectionCommutator
import Atlas.LinearGroups.Unitary.GenerationThreeComplete
import Atlas.LinearGroups.Unitary.PointNormalClosure
import Atlas.LinearGroups.Unitary.ThreeAction
import Mathlib.GroupTheory.IsPerfect

/-! Perfectness of the actual dimension-three matrix group, from a full-field
torus scaling a line group and the proved transvection generation theorem. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem exists_nonunit_norm (hdeg : Module.finrank F K = 2) (hq : 2 < Nat.card F) :
    ∃ t : K, t ≠ 0 ∧ t * conjugation F K t ≠ 1 := by
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨u, hu1⟩ := exists_ne (1 : Fˣ)
  obtain ⟨t, ht⟩ := norm_units_surjective F K u
  refine ⟨t.val, t.ne_zero, ?_⟩
  have he : norm F K t.val = u.val := congrArg Units.val ht
  intro h
  apply hu1
  apply Units.ext
  apply (algebraMap F K).injective
  rw [← he, norm_formula hdeg]
  simpa using h

theorem special_three_perfect (hdeg : Module.finrank F K = 2) (hq : 2 < Nat.card F) :
    Group.IsPerfect (SU F K 3 hdeg) := by
  obtain ⟨a,b,ha,hb⟩ := exists_witt_parameters hdeg
  obtain ⟨t, ht, hnorm⟩ := exists_nonunit_norm hdeg hq
  let v : Fin 3 → K := wittThreeMatrix a b *ᵥ Pi.single 0 1
  have hv : hermitian F K v v = 0 := by
    rw [wittThreeMatrix_preserves a b ha hb]
    simp [hyperbolicThreeForm, Pi.single_apply]
  have hv0 : v ≠ 0 := wittThree_mulVec_ne_zero a b ha _ (by simp)
  let g := threeUnitaryOfMatrix hdeg a b ha hb (fullTorusThreeMatrix (F := F) t)
    (fullTorusThreeMatrix_preserves hdeg t ht) (fullTorusThreeMatrix_det t ht)
  have hg : g.val *ᵥ v = t • v := by
    change (wittThreeMatrix a b * fullTorusThreeMatrix (F := F) t *
      (wittThreeMatrix a b)⁻¹) *ᵥ (wittThreeMatrix a b *ᵥ Pi.single 0 1) = _
    simp only [mulVec_mulVec, mul_assoc, nonsing_inv_mul _ (wittThreeMatrix_det_unit a b ha), mul_one]
    rw [← mulVec_mulVec]
    have he : fullTorusThreeMatrix (F := F) t *ᵥ Pi.single 0 1 = t • Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp [fullTorusThreeMatrix, mulVec_diagonal, Pi.single_apply]
    rw [he, mulVec_smul]
  let p := isotropicPoint v hv0 hv
  have hp : pointTransvections hdeg p = lineTransvections hdeg v hv := by
    apply lineTransvections_eq_of_projective_eq hdeg _ _ _ _ p.val.rep_nonzero hv0
    exact Projectivization.mk_rep p.val
  have hle : pointTransvections hdeg p ≤ commutator (SU F K 3 hdeg) := by
    rw [hp]
    exact lineTransvections_le_commutator_of_scaling hdeg v hv g t hg hnorm
  have hcl := Subgroup.normalClosure_le_normal hle
  rw [normalClosure_pointTransvections, transvectionGenerated_three_eq_top hdeg hq] at hcl
  exact ⟨top_unique hcl⟩

theorem projective_three_perfect (hdeg : Module.finrank F K = 2) (hq : 2 < Nat.card F) :
    Group.IsPerfect (PSU F K 3 hdeg) := by
  letI := special_three_perfect hdeg hq
  infer_instance
end Atlas.Unitary
