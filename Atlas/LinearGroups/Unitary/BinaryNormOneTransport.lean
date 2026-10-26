import Atlas.LinearGroups.Unitary.BinaryField
import Atlas.LinearGroups.Unitary.GeneratedNormal

/-! In binary even dimension the root subgroup already acts transitively on
norm-one vectors: every such vector has a zero coordinate. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable [CharP K 2] {n : ℕ}

theorem charTwo_generated_swap_orthogonal (hdeg : Module.finrank F K = 2)
    (v w : Fin n → K) (hv : hermitian F K v v = 1)
    (hw : hermitian F K w w = 1) (hvw : hermitian F K v w = 0) :
    ∃ g : SU F K n hdeg, g ∈ transvectionGenerated hdeg ∧ g.val *ᵥ v = w := by
  have hwv : hermitian F K w v = 0 := by
    rw [← hermitian_symmetry hdeg, hvw, map_zero]
  have hiso : hermitian F K (v+w) (v+w) = 0 := by
    simp only [hermitian_add_left, hermitian_add_right, hv, hw, hvw, hwv,
      add_zero, zero_add, CharTwo.add_self_eq_zero]
  have htrace : (1 : K) + conjugation F K 1 = 0 := by
    simp [CharTwo.add_self_eq_zero]
  refine ⟨transvection hdeg (v+w) 1 hiso htrace,
    transvection_mem_generated _ _ _ _ _, ?_⟩
  change transvectionMatrix (F := F) (v+w) 1 *ᵥ v = w
  rw [transvectionMatrix_apply, hermitian_add_right, hv, hvw, add_zero, one_mul, one_smul]
  ext i
  change v i + (v i + w i) = w i
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem binary_norm_one_zero_coordinate (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) (hn : Even n) (v : Fin n → K)
    (hv : hermitian F K v v = 1) : ∃ i, v i = 0 := by
  classical
  by_contra h
  push_neg at h
  have he : hermitian F K v v = (n : K) := by
    rw [binary_hermitian_support_sum hdeg hq]
    simp [h]
  obtain ⟨k,hk⟩ := hn
  have hnzero : (n : K) = 0 := by
    rw [hk, Nat.cast_add, CharTwo.add_self_eq_zero]
  exact one_ne_zero (hv.symm.trans (he.trans hnzero))

theorem charTwo_generated_map_to_first_of_zero (hdeg : Module.finrank F K = 2)
    (hnpos : 0 < n) (v : Fin n → K) (hv : hermitian F K v v = 1)
    (hzero : ∃ i, v i = 0) :
    ∃ g : SU F K n hdeg, g ∈ transvectionGenerated hdeg ∧
      g.val *ᵥ v = Pi.single ⟨0,hnpos⟩ 1 := by
  classical
  let i0 : Fin n := ⟨0,hnpos⟩
  obtain ⟨j,hj⟩ := hzero
  obtain ⟨g,hg,he⟩ := charTwo_generated_swap_orthogonal hdeg v (Pi.single j 1) hv
    (by simp) (by simpa using hj)
  by_cases hji : j = i0
  · exact ⟨g,hg,by simpa [hji] using he⟩
  · obtain ⟨h,hh,heh⟩ := charTwo_generated_swap_orthogonal hdeg
      (Pi.single j 1) (Pi.single i0 1) (by simp) (by simp)
      (by simp [Pi.single_apply, Ne.symm hji])
    refine ⟨h*g, (transvectionGenerated hdeg).mul_mem hh hg, ?_⟩
    change (h.val*g.val) *ᵥ v = _
    rw [← mulVec_mulVec, he, heh]
theorem binary_even_generated_map_to_first (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) (hn : Even n) (hnpos : 0 < n)
    (v : Fin n → K) (hv : hermitian F K v v = 1) :
    ∃ g : SU F K n hdeg, g ∈ transvectionGenerated hdeg ∧
      g.val *ᵥ v = Pi.single ⟨0,hnpos⟩ 1 :=
  charTwo_generated_map_to_first_of_zero hdeg hnpos v hv
    (binary_norm_one_zero_coordinate hdeg hq hn v hv)
end Atlas.Unitary
