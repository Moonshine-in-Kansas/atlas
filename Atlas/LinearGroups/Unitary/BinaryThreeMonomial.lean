import Atlas.LinearGroups.Unitary.CoordinateStabilizer
import Atlas.LinearGroups.Unitary.BinaryField
import Atlas.LinearGroups.Unitary.BinaryFourCommutator

/-! The actual binary dimension-three transvections preserve the coordinate frame. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem binary_three_norm_one_axis_of_zero (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) (x : Fin 3 → K) (hx : hermitian F K x x = 1)
    (k : Fin 3) (hk : x k = 0) : ∃ i : Fin 3, ∃ c : K, c ≠ 0 ∧ x = c • Pi.single i 1 := by
  classical
  letI := binary_charP hdeg hq
  rw [binary_hermitian_support_sum hdeg hq, Fin.sum_univ_three] at hx
  fin_cases k <;>
    by_cases h0 : x 0 = 0 <;> by_cases h1 : x 1 = 0 <;> by_cases h2 : x 2 = 0 <;>
    simp_all only [ite_true, ite_false, zero_add, add_zero, CharTwo.add_self_eq_zero, zero_ne_one]
  all_goals first
    | (refine ⟨0, x 0, h0, ?_⟩; ext i; fin_cases i <;> simp_all [Pi.single_apply])
    | (refine ⟨1, x 1, h1, ?_⟩; ext i; fin_cases i <;> simp_all [Pi.single_apply])
    | (refine ⟨2, x 2, h2, ?_⟩; ext i; fin_cases i <;> simp_all [Pi.single_apply])

theorem binary_three_transvection_coordinateStabilizer (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) (v : Fin 3 → K) (hv : hermitian F K v v = 0)
    (a : K) (ha : a + conjugation F K a = 0) :
    transvection hdeg v a hv ha ∈ coordinateStabilizer hdeg 3 := by
  letI := binary_charP hdeg hq
  rcases binary_trace_zero_cases hq a ha with hzero | hone
  · apply coordinateStabilizer_mem_of_columns hdeg
    intro i
    refine ⟨i,1,one_ne_zero, ?_⟩
    change transvectionMatrix (F := F) v a *ᵥ Pi.single i 1 = _
    rw [hzero, transvectionMatrix_zero, one_mulVec, one_smul]
  · subst a
    apply coordinateStabilizer_mem_of_columns hdeg
    intro i
    by_cases hi : v i = 0
    · refine ⟨i,1,one_ne_zero, ?_⟩
      change transvectionMatrix (F := F) v 1 *ᵥ Pi.single i 1 = _
      rw [transvectionMatrix_apply, one_smul]
      have hp : hermitian F K (Pi.single i 1) v = 0 := by
        rw [← hermitian_symmetry hdeg v _, hermitian_single_right, hi, map_zero]
      rw [hp, mul_zero, zero_smul, add_zero]
    · let g := transvection hdeg v 1 hv ha
      have hnorm : hermitian F K (g.val *ᵥ Pi.single i 1) (g.val *ᵥ Pi.single i 1) = 1 := by
        rw [u_preserves_hermitian hdeg (⟨g.val,g.prop.1⟩ : U F K 3 hdeg)]
        simp
      have hdiag : (g.val *ᵥ Pi.single i 1) i = 0 := by
        change (transvectionMatrix (F := F) v 1 *ᵥ Pi.single i 1) i = 0
        rw [transvectionMatrix_apply]
        have hp : hermitian F K (Pi.single i 1) v = conjugation F K (v i) := by
          rw [← hermitian_symmetry hdeg v _, hermitian_single_right]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, hp, one_mul]
        rw [mul_comm, binary_nonzero_norm hdeg hq _ hi, CharTwo.add_self_eq_zero]
      exact binary_three_norm_one_axis_of_zero hdeg hq _ hnorm i hdiag

theorem binary_three_generated_le_coordinateStabilizer (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) : transvectionGenerated hdeg (n := 3) ≤ coordinateStabilizer hdeg 3 := by
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  rintro g ⟨a,rfl⟩
  exact binary_three_transvection_coordinateStabilizer hdeg hq v hv a.toAdd.val
    ((trace_zero_iff hdeg _).mp a.toAdd.prop)
end Atlas.Unitary
