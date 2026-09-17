import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB
import Atlas.LinearGroups.Orthogonal.EvenSimplicity

/-! # Exact simplicity range of the same actual even B scalar quotient -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem even_projectiveB_simple_iff (hn : 0 < n) :
    IsSimpleGroup (ProjectiveElementary (formB n F)) ↔
      Atlas.Symplectic.Good n (Nat.card F) :=
  evenProjectiveBEquivFull.isSimpleGroup_congr.trans (even_full_simple_iff hn)

theorem even_projectiveB_simple_iff_rank_ge_two (hn : 2 ≤ n) :
    IsSimpleGroup (ProjectiveElementary (formB n F)) ↔ (n, Nat.card F) ≠ (2, 2) := by
  rw [even_projectiveB_simple_iff (by omega)]
  simp only [Atlas.Symplectic.Good, show n ≠ 1 by omega, false_and, hn,
    true_and, false_or]

theorem even_projectiveB_simple_stable (n : ℕ) :
    IsSimpleGroup (ProjectiveElementary (formB (n + 3) F)) := by
  apply (even_projectiveB_simple_iff_rank_ge_two (by omega)).mpr
  intro h
  have := congrArg Prod.fst h
  simp only [Prod.fst] at this
  omega

theorem even_projectiveB_perfect (h : Atlas.Symplectic.Good n (Nat.card F)) :
    Group.IsPerfect (ProjectiveElementary (formB n F)) := by
  letI := even_full_perfect h
  exact Group.IsPerfect.ofSurjective (f := evenProjectiveBEquivFull.symm.toMonoidHom)
    evenProjectiveBEquivFull.symm.surjective

theorem even_projectiveB_noncommutative (h : Atlas.Symplectic.Good n (Nat.card F)) :
    ¬ IsMulCommutative (ProjectiveElementary (formB n F)) := by
  intro hc
  exact even_full_noncommutative h
    (Function.Surjective.isMulCommutative evenProjectiveBEquivFull.surjective hc)
end Atlas.Orthogonal
