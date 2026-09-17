import Atlas.LinearGroups.G2.IwasawaLocal
import Atlas.LinearGroups.G2.Primitivity

noncomputable section
namespace Atlas.G2
open scoped Pointwise
variable {K : Type*} [Field K]

theorem localAt_le_stabilizer (p : SingularPoints K) :
    localAt p ≤ MulAction.stabilizer (Model K) p := by
  rintro x ⟨a,ha,rfl⟩
  change (pointTransport p*a*(pointTransport p)⁻¹) • p = p
  have he : (pointTransport p*a*(pointTransport p)⁻¹) • (pointTransport p • (firstPoint (K := K))) =
      pointTransport p • (firstPoint (K := K)) := by
    rw [mul_smul,mul_smul,inv_smul_smul]
    rw [(show a • (firstPoint (K := K)) = (firstPoint (K := K)) from longRootLocal_le_pointStabilizer ha)]
  simpa only [pointTransport_action] using he

theorem localAt_normal (p : SingularPoints K) :
    ((localAt p).subgroupOf (MulAction.stabilizer (Model K) p)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (localAt_le_stabilizer p)).mpr
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg a ha
  have hc : MulAut.conj g • localAt p = localAt p := by
    rw [← localAt_conj,MulAction.mem_stabilizer_iff.mp hg]
  rw [← hc]
  exact ⟨a,ha,rfl⟩

theorem subdegree_sum [Finite K] :
    (∑ i : Fin 4,singularSubdegree (Nat.card K) i) = Nat.card (SingularPoints K) := by
  rw [card_singularPoints_sum]
  simp [Fin.sum_univ_succ,singularSubdegree,Finset.sum_range_succ]
  ring

/-- Every nonzero A-root parameter gives a nonidentity actual automorphism. -/
theorem rootA_ne_one {a : K} (ha : a ≠ 0) : rootA a ≠ 1 := by
  intro h
  exact ha (rootA_injective (h.trans (rootA_zero (K := K)).symm))

/-- A canonical explicit nonidentity automorphism over every field. -/
theorem rootA_one_ne_one : rootA (1 : K) ≠ 1 := rootA_ne_one one_ne_zero

end Atlas.G2

