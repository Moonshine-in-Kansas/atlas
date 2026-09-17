import Atlas.Fischer.BasicFramePhases
import Atlas.Fischer.ProductTraceAutomorphisms

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

private theorem sum_basicAxis : ∑ i : Omega, basicAxis i = (16 : Scalar) • axisSum := by
  rw [show (∑ i : Omega, basicAxis i) = ∑ i : Omega, (axisSum - (8 : Scalar) • u i) from Finset.sum_congr rfl (fun i _ => basicAxis_eq i)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Finset.smul_sum]
  change (24 : ℕ) • axisSum - (8 : Scalar) • axisSum = (16 : Scalar) • axisSum
  module

/-- The common phase on the basic reflecting roots is the same phase on the
actual coordinate axes. -/
theorem basicFrame_axis_phase (e : SemilinearAlgebraAutomorphism)
    (σ : Equiv.Perm Omega) (a : Mu3)
    (ha : ∀ i, e.val (basicAxis i) = a.val.val • basicAxis (σ i)) :
    ∀ i, e.val (u i) = a.val.val • u (σ i) := by
  have hs : e.val axisSum = a.val.val • axisSum := by
    have h := congrArg (fun x => productTraceAlgebraEquiv e x) sum_basicAxis
    rw [map_sum, map_smulₛₗ, map_ofNat] at h
    have ht : ∑ i, productTraceAlgebraEquiv e (basicAxis i) =
        a.val.val • (∑ i, basicAxis i) := by
      simp only [show ∀ i, productTraceAlgebraEquiv e (basicAxis i) =
        a.val.val • basicAxis (σ i) from ha, ← Finset.smul_sum]
      rw [Equiv.sum_comp σ]
    rw [ht, sum_basicAxis, smul_smul] at h
    change (a.val.val * 16) • axisSum = (16 : Scalar) • e.val axisSum at h
    have h' : (16 : Scalar) • e.val axisSum =
        (16 : Scalar) • (a.val.val • axisSum) := by
      rw [smul_smul]
      simpa only [mul_comm] using h.symm
    exact (smul_right_injective _ (by norm_num : (16 : Scalar) ≠ 0)) h'
  intro i
  have h := ha i
  change productTraceAlgebraEquiv e (basicAxis i) = _ at h
  have hs' : productTraceAlgebraEquiv e axisSum = a.val.val • axisSum := hs
  rw [basicAxis_eq, map_sub, map_smulₛₗ, map_ofNat, hs', basicAxis_eq,
    smul_sub, smul_smul] at h
  have h' : (8 : Scalar) • e.val (u i) = (8 : Scalar) • (a.val.val • u (σ i)) := by
    rw [smul_smul]
    have hh := sub_right_injective h
    change (8 : Scalar) • e.val (u i) = (a.val.val * 8) • u (σ i) at hh
    simpa only [mul_comm] using hh
  exact (smul_right_injective _ (by norm_num : (8 : Scalar) ≠ 0)) h'

end Atlas.Fischer
