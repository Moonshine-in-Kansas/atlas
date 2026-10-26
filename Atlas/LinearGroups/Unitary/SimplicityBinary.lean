import Atlas.LinearGroups.Unitary.BinaryFourGeneration
import Atlas.LinearGroups.Unitary.BinaryFourCommutator
import Atlas.LinearGroups.Unitary.PerfectFourLift
import Atlas.LinearGroups.Unitary.SimplicityHigher

/-! Binary generation, perfectness and simplicity on the retained matrix models. -/
noncomputable section
namespace Atlas.Unitary
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem binary_transvectionGenerated_eq_top (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n) : transvectionGenerated hdeg (n := n) = ⊤ :=
  transvectionGenerated_eq_top_of_four hdeg (binary_transvectionGenerated_four_eq_top hdeg hq) hn

theorem binary_special_four_perfect (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2) :
    Group.IsPerfect (SU F K 4 hdeg) := by
  letI := binary_charP hdeg hq
  obtain ⟨c,hc⟩ := exists_binary_primitive hdeg hq
  exact special_four_perfect_of_binary_generated hdeg hq c hc
    (binary_transvectionGenerated_four_eq_top hdeg hq)

theorem binary_special_perfect (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    {n : ℕ} (hn : 4 ≤ n) : Group.IsPerfect (SU F K n hdeg) := by
  letI := binary_special_four_perfect hdeg hq
  exact special_perfect_of_four hdeg (binary_transvectionGenerated_four_eq_top hdeg hq) hn

theorem binary_projective_perfect (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    {n : ℕ} (hn : 4 ≤ n) : Group.IsPerfect (PSU F K n hdeg) := by
  letI := binary_special_perfect hdeg hq hn
  infer_instance

theorem binary_projective_simple (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    {n : ℕ} (hn : 4 ≤ n) : IsSimpleGroup (PSU F K n hdeg) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  obtain ⟨v,hv,hvv⟩ := exists_nonzero_isotropic_add_three hdeg k
  let p := isotropicPoint v hv hvv
  have hn0 : 0 < 3+k := by omega
  letI := projective_nontrivial_of_isotropic_point hdeg hn0 p
  letI := isotropicAction hdeg hn0
  letI := isotropicAction_faithful hdeg hn0
  letI := projective_isotropic_preprimitive hdeg hn0 p
  letI := binary_projective_perfect hdeg hq hn
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple p (projectivePointTransvections hdeg p)
    (projectivePointTransvections_le_stabilizer hdeg hn0 p)
    (projectivePointTransvections_normal hdeg hn0 p) inferInstance
    (normalClosure_projectivePointTransvections_eq_top hdeg p
      (binary_transvectionGenerated_eq_top hdeg hq hn))

theorem binary_projective_noncommutative (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n) : ¬ IsMulCommutative (PSU F K n hdeg) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  obtain ⟨v,hv,hvv⟩ := exists_nonzero_isotropic_add_three hdeg k
  letI := projective_nontrivial_of_isotropic_point hdeg (by omega) (isotropicPoint v hv hvv)
  letI := binary_projective_perfect hdeg hq hn
  exact Group.IsPerfect.not_isMulCommutative _
end Atlas.Unitary
