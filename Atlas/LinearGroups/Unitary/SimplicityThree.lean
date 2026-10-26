import Atlas.LinearGroups.Unitary.PerfectThree
import Atlas.LinearGroups.Unitary.ProjectiveLineGroups
import Atlas.GroupTheory.IwasawaStabilizer

/-! Simplicity of the actual PSU₃ center quotient for every q>2. -/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem projective_nontrivial_of_isotropic_point (hdeg : Module.finrank F K = 2)
    {n : ℕ} (hn : 0 < n) (p : IsotropicPoints F K n) : Nontrivial (PSU F K n hdeg) := by
  have hc : 1 < Nat.card (projectivePointTransvections hdeg p) := by
    rw [card_projectivePointTransvections hdeg hn]
    exact Finite.one_lt_card
  letI := Finite.one_lt_card_iff_nontrivial.mp hc
  exact Function.Injective.nontrivial (projectivePointTransvections hdeg p).subtype_injective

theorem projective_three_simple (hdeg : Module.finrank F K = 2) (hq : 2 < Nat.card F) :
    IsSimpleGroup (PSU F K 3 hdeg) := by
  obtain ⟨a,b,ha,hb⟩ := exists_witt_parameters hdeg
  let p := threeFirstPoint a b ha hb
  have hn : 0 < (3 : ℕ) := by decide
  letI := projective_nontrivial_of_isotropic_point hdeg hn p
  letI := isotropicAction hdeg (n := 3) hn
  letI := isotropicAction_faithful hdeg (n := 3) hn
  letI := projective_three_preprimitive hdeg
  letI := projective_three_perfect hdeg hq
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple p (projectivePointTransvections hdeg p)
    (projectivePointTransvections_le_stabilizer hdeg hn p)
    (projectivePointTransvections_normal hdeg hn p) inferInstance
    (normalClosure_projectivePointTransvections_eq_top hdeg p
      (transvectionGenerated_three_eq_top hdeg hq))

theorem projective_three_noncommutative (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) : ¬ IsMulCommutative (PSU F K 3 hdeg) := by
  obtain ⟨a,b,ha,hb⟩ := exists_witt_parameters hdeg
  letI := projective_nontrivial_of_isotropic_point hdeg (by decide) (threeFirstPoint a b ha hb)
  letI := projective_three_perfect hdeg hq
  exact Group.IsPerfect.not_isMulCommutative _
end Atlas.Unitary
