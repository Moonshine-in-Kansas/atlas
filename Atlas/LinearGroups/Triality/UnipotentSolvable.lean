import Atlas.LinearGroups.Triality.Unipotent
import Mathlib.GroupTheory.Nilpotent

/-! Nilpotence and solvability from the independently proved unipotent order. -/
noncomputable section
namespace Atlas.Triality
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem unipotent_isPGroup (hdeg : Module.finrank F K = 3)
    (p n : ℕ) (hq : Nat.card F = p^n) : IsPGroup p (unipotent F K hdeg) := by
  apply IsPGroup.of_card (n := n*12)
  rw [card_unipotent F K hdeg, hq, pow_mul]

theorem unipotent_nilpotent (hdeg : Module.finrank F K = 3) :
    Group.IsNilpotent (unipotent F K hdeg) := by
  letI := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hq⟩ := FiniteField.card' F
  letI : Fact p.Prime := ⟨hp⟩
  apply IsPGroup.isNilpotent (p := p)
  apply unipotent_isPGroup F K hdeg p n
  simpa only [Nat.card_eq_fintype_card] using hq

theorem unipotent_solvable (hdeg : Module.finrank F K = 3) :
    Group.IsSolvable (unipotent F K hdeg) := by
  letI := unipotent_nilpotent F K hdeg
  infer_instance

end Atlas.Triality
