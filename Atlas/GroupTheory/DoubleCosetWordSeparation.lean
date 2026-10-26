import Atlas.GroupTheory.DoubleCosetProduct
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Double-coset separation from simple-lift words and the two-cell bound.
The comparison element remains universally quantified in the list induction.
No Coxeter presentation, length, counting, or prepackaged BN pair is assumed. -/
namespace Atlas.GroupTheory
open scoped Pointwise

variable {G W I : Type*} [Group G] [Group W]
  (B N : Subgroup G) (φ : N →* W) (σ : I → N)
  (hker : ∀ n : N, φ n = 1 ↔ n.val ∈ B)
include hker

theorem N_mem_doubleCoset_of_action_eq (n m : N) (h : φ n = φ m) :
    n.val ∈ DoubleCoset.doubleCoset m.val B B := by
  have hk : (n*m⁻¹).val ∈ B := (hker _).mp (by simp only [map_mul,map_inv,h,mul_inv_cancel])
  exact DoubleCoset.mem_doubleCoset.mpr
    ⟨(n*m⁻¹).val,hk,1,B.one_mem,by simp only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,inv_mul_cancel,mul_one]⟩

theorem simpleLiftWord_action_eq_of_mem_doubleCoset
    (hsquare : ∀ i, (σ i).val ^ 2 ∈ B)
    (hmul : ∀ i (n : N),
      DoubleCoset.doubleCoset (σ i).val B B * DoubleCoset.doubleCoset n.val B B ⊆
        DoubleCoset.doubleCoset (σ i * n).val B B ∪ DoubleCoset.doubleCoset n.val B B)
    (l : List I) (n : N)
    (h : ((l.map σ).prod).val ∈ DoubleCoset.doubleCoset n.val B B) :
    φ ((l.map σ).prod) = φ n := by
  induction l generalizing n with
  | nil =>
    change (1 : G) ∈ DoubleCoset.doubleCoset n.val B B at h
    obtain ⟨a,ha,c,hc,he⟩ := DoubleCoset.mem_doubleCoset.mp h
    have hn : n.val = a⁻¹*c⁻¹ := by
      calc
        n.val = a⁻¹*(a*n.val*c)*c⁻¹ := by group
        _ = _ := by rw [← he]; group
    have hb : n.val ∈ B := by
      rw [hn]
      exact B.mul_mem (B.inv_mem ha) (B.inv_mem hc)
    simpa only [List.map_nil,List.prod_nil,map_one] using ((hker n).mpr hb).symm
  | cons i l ih =>
    let v : N := (l.map σ).prod
    change (σ i * v).val ∈ DoubleCoset.doubleCoset n.val B B at h
    change φ (σ i * v) = φ n
    have hinv : (σ i).val⁻¹ ∈ DoubleCoset.doubleCoset (σ i).val B B := by
      refine DoubleCoset.mem_doubleCoset.mpr
        ⟨((σ i).val^2)⁻¹,B.inv_mem (hsquare i),1,B.one_mem,?_⟩
      group
    have htail : v.val ∈
        DoubleCoset.doubleCoset (σ i * n).val B B ∪ DoubleCoset.doubleCoset n.val B B := by
      apply hmul i n
      exact ⟨(σ i).val⁻¹,hinv,(σ i*v).val,h,by simp only [Subgroup.coe_mul,inv_mul_cancel_left]⟩
    rcases htail with ht | ht
    · have he := ih (σ i*n) ht
      have hs : φ (σ i) * φ (σ i) = 1 := by
        have hb : (σ i*σ i).val ∈ B := by
          simpa only [Subgroup.coe_mul,pow_two] using hsquare i
        simpa only [map_mul] using (hker (σ i*σ i)).mpr hb
      change φ v = φ (σ i*n) at he
      rw [map_mul] at he ⊢
      rw [he,← mul_assoc,hs,one_mul]
    · have he := ih n ht
      have htword : v.val ∈ DoubleCoset.doubleCoset (σ i*v).val B B := by
        rw [DoubleCoset.doubleCoset_eq_of_mem h]
        exact ht
      have heword := ih (σ i*v) htword
      exact heword.symm.trans he

/-- Generation is needed only in the action image: literal word representatives
may differ from an arbitrary N element by its already specified B-kernel. -/
theorem N_action_eq_of_mem_doubleCoset_of_simple_words
    (hsquare : ∀ i, (σ i).val ^ 2 ∈ B)
    (hmul : ∀ i (n : N),
      DoubleCoset.doubleCoset (σ i).val B B * DoubleCoset.doubleCoset n.val B B ⊆
        DoubleCoset.doubleCoset (σ i * n).val B B ∪ DoubleCoset.doubleCoset n.val B B)
    (hwords : ∀ n : N, ∃ l : List I, φ ((l.map σ).prod) = φ n)
    (n m : N) (h : n.val ∈ DoubleCoset.doubleCoset m.val B B) : φ n = φ m := by
  obtain ⟨l,hl⟩ := hwords n
  have hw : ((l.map σ).prod).val ∈ DoubleCoset.doubleCoset m.val B B := by
    rw [← DoubleCoset.doubleCoset_eq_of_mem h]
    exact N_mem_doubleCoset_of_action_eq B N φ hker _ n hl
  exact hl.symm.trans
    (simpleLiftWord_action_eq_of_mem_doubleCoset B N φ σ hker hsquare hmul l m hw)

theorem N_doubleCosets_disjoint_of_action_ne
    (hsquare : ∀ i, (σ i).val ^ 2 ∈ B)
    (hmul : ∀ i (n : N),
      DoubleCoset.doubleCoset (σ i).val B B * DoubleCoset.doubleCoset n.val B B ⊆
        DoubleCoset.doubleCoset (σ i * n).val B B ∪ DoubleCoset.doubleCoset n.val B B)
    (hwords : ∀ n : N, ∃ l : List I, φ ((l.map σ).prod) = φ n)
    (n m : N) (hne : φ n ≠ φ m) :
    Disjoint (DoubleCoset.doubleCoset n.val B B) (DoubleCoset.doubleCoset m.val B B) := by
  by_contra h
  have hm := DoubleCoset.mem_doubleCoset_of_not_disjoint h
  exact hne (N_action_eq_of_mem_doubleCoset_of_simple_words B N φ σ hker
    hsquare hmul hwords m n hm).symm

end Atlas.GroupTheory
