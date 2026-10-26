import Atlas.LinearGroups.SuzukiFamily.Simplicity
import Atlas.LinearGroups.SuzukiFamily.SmallField

/-! Exact simplicity range, including the binary exception. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem simple_iff (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    IsSimpleGroup (Group F m) ↔ 1≤m := by
  constructor
  · intro hs
    by_contra hm
    have hm0 : m=0 := by omega
    subst m
    exact binary_not_simple (by simpa using hcard) hs
  · exact simple_of_large m hcard
end Atlas.SuzukiFamily
