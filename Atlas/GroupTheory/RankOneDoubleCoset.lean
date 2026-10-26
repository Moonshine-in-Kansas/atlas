import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic

/-! A finite rank-one double-coset closure argument, independent of any family. -/
namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G]

def TwoCell (B : Subgroup G) (n g : G) : Prop :=
  g ∈ B ∨ ∃ b ∈ B, ∃ c ∈ B, g = b*n*c

theorem twoCell_mul_left (B : Subgroup G) (n : G) {a b : G}
    (ha : a ∈ B) (hb : TwoCell B n b) : TwoCell B n (a*b) := by
  rcases hb with hb | ⟨r,hr,s,hs,rfl⟩
  · exact Or.inl (B.mul_mem ha hb)
  · exact Or.inr ⟨a*r,B.mul_mem ha hr,s,hs,by group⟩

theorem twoCell_mul_right (B : Subgroup G) (n : G) {a b : G}
    (ha : TwoCell B n a) (hb : b ∈ B) : TwoCell B n (a*b) := by
  rcases ha with ha | ⟨r,hr,s,hs,rfl⟩
  · exact Or.inl (B.mul_mem ha hb)
  · exact Or.inr ⟨r,hr,s*b,B.mul_mem hs hb,by group⟩

private theorem twoCell_mul (B : Subgroup G) (n : G)
    (hn : ∀ b ∈ B, TwoCell B n (n*b*n)) {a b : G}
    (ha : TwoCell B n a) (hb : TwoCell B n b) : TwoCell B n (a*b) := by
  rcases ha with ha | ⟨r,hr,s,hs,rfl⟩
  · rcases hb with hb | ⟨r,hr,s,hs,rfl⟩
    · exact Or.inl (B.mul_mem ha hb)
    · exact Or.inr ⟨a*r,B.mul_mem ha hr,s,hs,by group⟩
  · rcases hb with hb | ⟨t,ht,u,hu,rfl⟩
    · exact Or.inr ⟨r,hr,s*b,B.mul_mem hs hb,by group⟩
    · rcases hn (s*t) (B.mul_mem hs ht) with hm | ⟨v,hv,w,hw,he⟩
      · left
        have he : (r*n*s)*(t*n*u) = r*(n*(s*t)*n)*u := by group
        rw [he]
        exact B.mul_mem (B.mul_mem hr hm) hu
      · right
        refine ⟨r*v,B.mul_mem hr hv,w*u,B.mul_mem hw hu,?_⟩
        calc
          _ = r*(n*(s*t)*n)*u := by group
          _ = _ := by rw [he]; group

/-- Exhaustion by B and BnB follows from the local nBn rewrite. Finiteness
supplies inverse closure of the multiplicatively closed two-cell set. -/
theorem rankOne_double_coset_exhaustion (B : Subgroup G) (n : G)
    (hn : ∀ b ∈ B, TwoCell B n (n*b*n)) (g : G)
    (hg : g ∈ B ⊔ Subgroup.closure {n}) : TwoCell B n g := by
  let S : Submonoid G := {
    carrier := {g | TwoCell B n g}
    one_mem' := Or.inl B.one_mem
    mul_mem' := twoCell_mul B n hn }
  have hi (a : G) (ha : a ∈ S) : a⁻¹ ∈ S := by
    let f : S → S := fun x => ⟨a*x.val,S.mul_mem ha x.property⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    obtain ⟨x,hx⟩ := (Finite.surjective_of_injective hf) (1 : S)
    have he : a*x.val=1 := congrArg Subtype.val hx
    have hx' : x.val=a⁻¹ := by
      calc
        x.val = a⁻¹*(a*x.val) := by group
        _ = a⁻¹ := by rw [he,mul_one]
    exact hx' ▸ x.property
  let H : Subgroup G := { S with inv_mem' := hi _ }
  have hle : B ⊔ Subgroup.closure {n} ≤ H := by
    apply sup_le
    · exact fun x hx => Or.inl hx
    · apply (Subgroup.closure_le _).mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Or.inr ⟨1,B.one_mem,1,B.one_mem,by simp⟩
  exact hle hg

end Atlas.GroupTheory
