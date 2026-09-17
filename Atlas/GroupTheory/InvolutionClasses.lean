import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.OrderOfElement

/-! # The number of conjugacy classes of elements of order exactly two -/
noncomputable section
namespace Atlas
variable {G H : Type*} [Group G] [Group H]

/-- Classes containing an element of order exactly two; the identity is excluded. -/
def InvolutionClasses (G : Type*) [Group G] :=
  {c : ConjClasses G // ∃ g : G, ConjClasses.mk g = c ∧ orderOf g = 2}

instance [Finite G] : Finite (InvolutionClasses G) := inferInstanceAs (Finite (Subtype _))

/-- The conjugacy-class count, not the number of individual involutions. -/
def k2 (G : Type*) [Group G] : ℕ := Nat.card (InvolutionClasses G)

/-- An actual group equivalence transports precisely the order-two conjugacy classes. -/
def involutionClassesEquiv (e : G ≃* H) : InvolutionClasses G ≃ InvolutionClasses H where
  toFun c := ⟨ConjClasses.map e.toMonoidHom c.val, by
    obtain ⟨g, hg, ho⟩ := c.prop
    refine ⟨e g, ?_, (e.orderOf_eq g).trans ho⟩
    rw [← hg]
    rfl⟩
  invFun c := ⟨ConjClasses.map e.symm.toMonoidHom c.val, by
    obtain ⟨g, hg, ho⟩ := c.prop
    refine ⟨e.symm g, ?_, (e.symm.orderOf_eq g).trans ho⟩
    rw [← hg]
    rfl⟩
  left_inv c := by
    apply Subtype.ext
    change ConjClasses.map e.symm.toMonoidHom (ConjClasses.map e.toMonoidHom c.val) = c.val
    obtain ⟨g, hg, _⟩ := c.prop
    rw [← hg]
    change ConjClasses.mk (e.symm (e g)) = ConjClasses.mk g
    rw [e.symm_apply_apply]
  right_inv c := by
    apply Subtype.ext
    change ConjClasses.map e.toMonoidHom (ConjClasses.map e.symm.toMonoidHom c.val) = c.val
    obtain ⟨g, hg, _⟩ := c.prop
    rw [← hg]
    change ConjClasses.mk (e (e.symm g)) = ConjClasses.mk g
    rw [e.apply_symm_apply]

theorem k2_mulEquiv (e : G ≃* H) : k2 G = k2 H :=
  Nat.card_congr (involutionClassesEquiv e)

theorem not_nonempty_mulEquiv_of_k2_ne (h : k2 G ≠ k2 H) : ¬ Nonempty (G ≃* H) := by
  rintro ⟨e⟩
  exact h (k2_mulEquiv e)
end Atlas
