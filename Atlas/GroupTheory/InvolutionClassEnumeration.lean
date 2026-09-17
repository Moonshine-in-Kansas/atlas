import Atlas.GroupTheory.InvolutionClasses

/-! # Counting involution classes from proved representatives -/
noncomputable section
namespace Atlas
variable {G I : Type*} [Group G]

/-- The actual conjugacy class of an order-two representative. -/
def involutionClassOfRepresentative (r : I → G) (ho : ∀ i, orderOf (r i) = 2)
    (i : I) : InvolutionClasses G :=
  ⟨ConjClasses.mk (r i), ⟨r i, rfl, ho i⟩⟩

/-- Exhaustiveness and pairwise nonconjugacy give an equivalence with the actual
class subtype; the hypotheses are the mathematical enumeration obligations. -/
def involutionClassesEquivRepresentatives (r : I → G) (ho : ∀ i, orderOf (r i) = 2)
    (hi : ∀ i j, IsConj (r i) (r j) → i = j)
    (hs : ∀ g : G, orderOf g = 2 → ∃ i, IsConj g (r i)) : I ≃ InvolutionClasses G :=
  Equiv.ofBijective (involutionClassOfRepresentative r ho) (by
    constructor
    · intro i j h
      apply hi i j
      exact ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val h)
    · intro c
      obtain ⟨g,hg,ho'⟩ := c.prop
      obtain ⟨i,hi⟩ := hs g ho'
      refine ⟨i,Subtype.ext ?_⟩
      exact (ConjClasses.mk_eq_mk_iff_isConj.mpr hi).symm.trans hg)

theorem k2_eq_card_representatives (r : I → G) (ho : ∀ i, orderOf (r i) = 2)
    (hi : ∀ i j, IsConj (r i) (r j) → i = j)
    (hs : ∀ g : G, orderOf g = 2 → ∃ i, IsConj g (r i)) : k2 G = Nat.card I :=
  (Nat.card_congr (involutionClassesEquivRepresentatives r ho hi hs)).symm

end Atlas
