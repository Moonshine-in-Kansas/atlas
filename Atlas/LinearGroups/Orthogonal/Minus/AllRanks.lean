import Atlas.LinearGroups.Orthogonal.Minus.RankTwoFamily
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeSimplicity
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeFullImage

/-! Uniform low-rank completion on the existing quadratic-form carrier. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def family_rankThree_equiv (hdeg : Module.finrank F K = 2) :
    DMinus 3 F K hdeg ≃* Atlas.Unitary.PSU F K 4 hdeg :=
  rankThreeProjectiveEquiv hdeg

theorem family_rankThree_comparison (hdeg : Module.finrank F K = 2) :
    Nonempty (DMinus 3 F K hdeg ≃* Atlas.Unitary.PSU F K 4 hdeg) :=
  ⟨family_rankThree_equiv hdeg⟩

theorem family_order_all (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (DMinus n F K hdeg) = orderNumerator (Nat.card F) n /
      Nat.gcd 4 (Nat.card F^n+1) := by
  by_cases h : n=2
  · subst n
    simpa [orderNumerator,Finset.prod_range_succ] using family_rankTwo_order hdeg
  · exact family_order hdeg n (by omega)

theorem family_simple_all (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 2 ≤ n) :
    IsSimpleGroup (DMinus n F K hdeg) := by
  by_cases h : n=2
  · subst n; exact family_rankTwo_simple hdeg
  by_cases h : n=3
  · subst n; exact rankThree_simple hdeg
  exact family_simple hdeg n (by omega)

theorem family_noncommutative_all (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsMulCommutative (DMinus n F K hdeg) := by
  by_cases h : n=2
  · subst n; exact family_rankTwo_noncommutative hdeg
  by_cases h : n=3
  · subst n; exact rankThree_noncommutative hdeg
  exact family_noncommutative hdeg n (by omega)

theorem family_elementary_perfect_all (hdeg : Module.finrank F K = 2)
    (n : ℕ) (hn : 2 ≤ n) : Group.IsPerfect (E hdeg (n-1)) := by
  by_cases h : n=2
  · subst n; exact rankTwo_elementary_perfect hdeg
  by_cases h : n=3
  · subst n; exact rankThree_elementary_perfect hdeg
  exact family_elementary_perfect hdeg n (by omega)

end Atlas.Orthogonal.Minus
