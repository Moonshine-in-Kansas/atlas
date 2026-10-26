import Atlas.LinearGroups.Unitary.PerfectHigher
import Atlas.LinearGroups.Unitary.PointGeometry
import Atlas.LinearGroups.Unitary.SimplicityThree

/-! Uniform positive simplicity for q>2 in the actual center quotient. -/
noncomputable section
namespace Atlas.Unitary
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem projective_simple_of_three_le (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) {n : ℕ} (hn : 3 ≤ n) : IsSimpleGroup (PSU F K n hdeg) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨v,hv,hvv⟩ := exists_nonzero_isotropic_add_three hdeg k
  let p := isotropicPoint v hv hvv
  have hn0 : 0 < 3+k := by omega
  letI := projective_nontrivial_of_isotropic_point hdeg hn0 p
  letI := isotropicAction hdeg hn0
  letI := isotropicAction_faithful hdeg hn0
  letI := projective_isotropic_preprimitive hdeg hn0 p
  letI := projective_perfect_of_three_le hdeg hq (by omega : 3 ≤ 3+k)
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple p (projectivePointTransvections hdeg p)
    (projectivePointTransvections_le_stabilizer hdeg hn0 p)
    (projectivePointTransvections_normal hdeg hn0 p) inferInstance
    (normalClosure_projectivePointTransvections_eq_top hdeg p
      (transvectionGenerated_add_three_eq_top hdeg hq k))

theorem projective_noncommutative_of_three_le (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) {n : ℕ} (hn : 3 ≤ n) : ¬ IsMulCommutative (PSU F K n hdeg) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨v,hv,hvv⟩ := exists_nonzero_isotropic_add_three hdeg k
  letI := projective_nontrivial_of_isotropic_point hdeg (by omega) (isotropicPoint v hv hvv)
  letI := projective_perfect_of_three_le hdeg hq (by omega : 3 ≤ 3+k)
  exact Group.IsPerfect.not_isMulCommutative _
end Atlas.Unitary
