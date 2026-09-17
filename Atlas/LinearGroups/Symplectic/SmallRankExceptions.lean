import Atlas.LinearGroups.Symplectic.RankOne
import Atlas.LinearGroups.PSLExceptions

noncomputable section
namespace Atlas.Symplectic
variable {F : Type*} [Field F] [Finite F]

theorem rank_zero_not_simple : ¬ IsSimpleGroup (PSp 0 F) := by
  intro h
  letI := h.toNontrivial
  exact not_subsingleton (PSp 0 F) inferInstance

theorem rank_one_two_not_simple (hq : Nat.card F = 2) : ¬ IsSimpleGroup (PSp 1 F) := by
  intro h
  letI := h
  exact Atlas.psl_two_two_not_simple hq rankOnePSL.symm.isSimpleGroup

theorem rank_one_three_not_simple (hq : Nat.card F = 3) : ¬ IsSimpleGroup (PSp 1 F) := by
  intro h
  letI := h
  exact Atlas.psl_two_three_not_simple hq rankOnePSL.symm.isSimpleGroup

end Atlas.Symplectic
