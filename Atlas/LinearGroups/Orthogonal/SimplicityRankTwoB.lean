import Atlas.LinearGroups.Orthogonal.B2ExteriorComparison
import Atlas.LinearGroups.Symplectic.Simplicity
import Atlas.LinearGroups.Symplectic.Noncommutative

/-! # Actual odd B₂ simplicity and perfectness, including the ternary field -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem odd_rank_two_good (h2 : (2 : F) ≠ 0) : Atlas.Symplectic.Good 2 (Nat.card F) := by
  right
  refine ⟨le_rfl, ?_⟩
  intro h
  have he := congrArg Prod.snd h
  have ho := Atlas.odd_card_mod_two h2
  simp only [Prod.snd] at he
  omega

theorem projectiveB_two_simple (h2 : (2 : F) ≠ 0) :
    IsSimpleGroup (ProjectiveElementary (formB 2 F)) := by
  letI := Atlas.Symplectic.simple_of_good (odd_rank_two_good h2)
  exact (B2Exterior.projectiveBEquivPSp h2).isSimpleGroup

theorem elementaryB_two_perfect (h2 : (2 : F) ≠ 0) :
    Group.IsPerfect (elementarySubgroup (formB 2 F)) := by
  letI := Atlas.Symplectic.perfect_of_good (odd_rank_two_good h2)
  exact Group.IsPerfect.ofSurjective (f := B2Exterior.toElementary h2)
    (B2Exterior.toElementary_surjective h2)

theorem elementaryB_two_simple (h2 : (2 : F) ≠ 0) :
    IsSimpleGroup (elementarySubgroup (formB 2 F)) := by
  letI := projectiveB_two_simple h2
  exact (projectiveElementaryBEquiv 0 h2).symm.isSimpleGroup

theorem oddSpinorKernelB_two_simple (h2 : (2 : F) ≠ 0) :
    IsSimpleGroup (oddSpinorKernelB 2 h2) := by
  letI := elementaryB_two_simple h2
  exact (elementaryB_kernelEquiv 0 h2).symm.isSimpleGroup
end Atlas.Orthogonal
