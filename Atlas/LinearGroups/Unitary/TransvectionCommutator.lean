import Atlas.LinearGroups.Unitary.LineTransvections
import Mathlib.GroupTheory.Commutator.Basic

/-! Actual torus/transvection commutators, with the nonzero coefficient hypothesis
visible. Existence of an appropriate torus is a separate structural theorem. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped commutatorElement
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

theorem transvection_mem_commutator_of_scaling (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0)
    (g : SU F K n hdeg) (c : K) (hg : g.val *ᵥ v = c • v)
    (hc : c * conjugation F K c ≠ 1)
    (a : K) (ha : a + conjugation F K a = 0) :
    transvection hdeg v a hv ha ∈ commutator (SU F K n hdeg) := by
  let d := c * conjugation F K c
  have hd : d - 1 ≠ 0 := sub_ne_zero.mpr hc
  have hdf : conjugation F K d = d := by
    simp [d, map_mul, conjugation_conjugation hdeg, mul_comm]
  let b := a / (d - 1)
  have hb : b + conjugation F K b = 0 := by
    dsimp [b]
    rw [map_div₀, map_sub, hdf, map_one]
    field_simp
    simpa using ha
  have hnb : -b + conjugation F K (-b) = 0 := by
    rw [map_neg]
    linear_combination -hb
  let u := transvection hdeg v b hv hb
  have huinv : u⁻¹ = transvection hdeg v (-b) hv hnb := by
    apply mul_left_cancel (a := u)
    rw [mul_inv_cancel]
    apply Subtype.ext
    exact (transvectionMatrix_inverse v hv b).symm
  have he : ⁅g, u⁆ = transvection hdeg v a hv ha := by
    rw [commutatorElement_def, huinv]
    change (g * transvection hdeg v b hv hb * g⁻¹) *
      transvection hdeg v (-b) hv hnb = _
    rw [transvection_conjugate]
    apply Subtype.ext
    change transvectionMatrix (F := F) (g.val *ᵥ v) b *
      transvectionMatrix (F := F) v (-b) = transvectionMatrix (F := F) v a
    rw [hg, transvectionMatrix_smul, transvectionMatrix_mul v hv]
    congr 1
    change b * d + -b = a
    dsimp [b]
    field_simp
    ring
  rw [← he, commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet g u)

theorem lineTransvections_le_commutator_of_scaling (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0)
    (g : SU F K n hdeg) (c : K) (hg : g.val *ᵥ v = c • v)
    (hc : c * conjugation F K c ≠ 1) :
    lineTransvections hdeg v hv ≤ commutator (SU F K n hdeg) := by
  rintro x ⟨a, rfl⟩
  exact transvection_mem_commutator_of_scaling hdeg v hv g c hg hc a.toAdd.val
    ((trace_zero_iff hdeg _).mp a.toAdd.prop)
end Atlas.Unitary
