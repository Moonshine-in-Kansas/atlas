import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-! Double-coset products from an explicit sandwich reduction. -/
namespace Atlas.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G]

theorem doubleCoset_mul_left_right
    (B : Subgroup G) (n : G) {g : G}
    (hg : g ∈ DoubleCoset.doubleCoset n B B)
    (a c : G) (ha : a ∈ B) (hc : c ∈ B) :
    a*g*c ∈ DoubleCoset.doubleCoset n B B := by
  obtain ⟨x,hx,y,hy,hg⟩ := DoubleCoset.mem_doubleCoset.mp hg
  apply DoubleCoset.mem_doubleCoset.mpr
  refine ⟨a*x,B.mul_mem ha hx,y*c,B.mul_mem hy hc,?_⟩
  rw [hg]
  group

theorem doubleCoset_mul_subset_of_sandwich
    (B : Subgroup G) (s n : G)
    (hsandwich : ∀ g ∈ B,
      s*g*n ∈ DoubleCoset.doubleCoset (s*n) B B ∨
        s*g*n ∈ DoubleCoset.doubleCoset n B B) :
    DoubleCoset.doubleCoset s B B * DoubleCoset.doubleCoset n B B ⊆
      DoubleCoset.doubleCoset (s*n) B B ∪ DoubleCoset.doubleCoset n B B := by
  rintro g ⟨x,hx,y,hy,rfl⟩
  obtain ⟨a,ha,b,hb,hx⟩ := DoubleCoset.mem_doubleCoset.mp hx
  obtain ⟨c,hc,d,hd,hy⟩ := DoubleCoset.mem_doubleCoset.mp hy
  have he : x*y = a*(s*(b*c)*n)*d := by rw [hx,hy]; group
  change x*y ∈ DoubleCoset.doubleCoset (s*n) B B ∨
    x*y ∈ DoubleCoset.doubleCoset n B B
  rw [he]
  rcases hsandwich (b*c) (B.mul_mem hb hc) with h | h
  · exact Or.inl (doubleCoset_mul_left_right B (s*n) h a d ha hd)
  · exact Or.inr (doubleCoset_mul_left_right B n h a d ha hd)

end Atlas.GroupTheory
