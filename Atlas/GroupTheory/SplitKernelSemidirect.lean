import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
Source-only, uncompiled. A homomorphic section gives an actual semidirect
product by its kernel. The action is conjugation by that section, and the
equivalence sends (n,h) to n*s(h). No finiteness or cardinality is used.
-/

noncomputable section
namespace Atlas.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- Restrict actual conjugation to a kernel and compose with the specified section map. -/
def splitKernelAction (p : G →* H) (s : H →* G) : H →* MulAut p.ker :=
  (MulAut.conjNormal (H := p.ker)).comp s

theorem splitKernelAction_apply (p : G →* H) (s : H →* G) (h : H) (n : p.ker) :
    (splitKernelAction p s h n).val = s h * n.val * (s h)⁻¹ := rfl

/-- Multiplication into the same ambient group, using the standard semidirect lift. -/
def splitKernelMulHom (p : G →* H) (s : H →* G) :
    p.ker ⋊[splitKernelAction p s] H →* G :=
  SemidirectProduct.lift p.ker.subtype s (by
    intro h
    apply MonoidHom.ext
    intro n
    rfl)

theorem splitKernelMulHom_apply (p : G →* H) (s : H →* G)
    (x : p.ker ⋊[splitKernelAction p s] H) :
    splitKernelMulHom p s x = x.left.val * s x.right := rfl

theorem splitKernelMulHom_bijective (p : G →* H) (s : H →* G)
    (hs : Function.LeftInverse p s) : Function.Bijective (splitKernelMulHom p s) := by
  constructor
  · intro x y hxy
    change x.left.val * s x.right = y.left.val * s y.right at hxy
    have hx : p x.left.val = 1 := x.left.property
    have hy : p y.left.val = 1 := y.left.property
    have hr : x.right = y.right := by
      have he := congrArg p hxy
      simpa only [map_mul, hx, hy, hs x.right, hs y.right, one_mul] using he
    have hl : x.left = y.left := by
      apply Subtype.ext
      rw [hr] at hxy
      exact mul_right_cancel hxy
    exact SemidirectProduct.ext hl hr
  · intro g
    let n : p.ker := ⟨g * (s (p g))⁻¹, by
      change p (g * (s (p g))⁻¹) = 1
      rw [map_mul, map_inv, hs (p g), mul_inv_cancel]⟩
    refine ⟨⟨n, p g⟩, ?_⟩
    change (g * (s (p g))⁻¹) * s (p g) = g
    exact inv_mul_cancel_right g (s (p g))

/-- The actual split extension, proved by multiplication and the explicit residual g/s(p(g)). -/
def splitKernelMulEquiv (p : G →* H) (s : H →* G)
    (hs : Function.LeftInverse p s) : p.ker ⋊[splitKernelAction p s] H ≃* G :=
  MulEquiv.ofBijective (splitKernelMulHom p s) (splitKernelMulHom_bijective p s hs)

theorem splitKernelMulEquiv_apply (p : G →* H) (s : H →* G)
    (hs : Function.LeftInverse p s) (x : p.ker ⋊[splitKernelAction p s] H) :
    splitKernelMulEquiv p s hs x = x.left.val * s x.right := rfl

theorem splitKernelMulEquiv_inl (p : G →* H) (s : H →* G)
    (hs : Function.LeftInverse p s) (n : p.ker) :
    splitKernelMulEquiv p s hs (SemidirectProduct.inl n) = n.val := by
  rw [splitKernelMulEquiv_apply]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]

theorem splitKernelMulEquiv_inr (p : G →* H) (s : H →* G)
    (hs : Function.LeftInverse p s) (h : H) :
    splitKernelMulEquiv p s hs (SemidirectProduct.inr h) = s h := by
  rw [splitKernelMulEquiv_apply]
  simp only [SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    Subgroup.coe_one, one_mul]

theorem splitKernelMulEquiv_right (p : G →* H) (s : H →* G)
    (hs : Function.LeftInverse p s) (x : p.ker ⋊[splitKernelAction p s] H) :
    p (splitKernelMulEquiv p s hs x) = x.right := by
  rw [splitKernelMulEquiv_apply, map_mul, hs x.right,
    show p x.left.val = 1 from x.left.property, one_mul]

theorem splitKernelMulEquiv_symm_right (p : G →* H) (s : H →* G)
    (hs : Function.LeftInverse p s) (g : G) :
    ((splitKernelMulEquiv p s hs).symm g).right = p g := by
  have he := congrArg p ((splitKernelMulEquiv p s hs).apply_symm_apply g)
  simpa only [splitKernelMulEquiv_right] using he

theorem splitKernelMulEquiv_symm_left (p : G →* H) (s : H →* G)
    (hs : Function.LeftInverse p s) (g : G) :
    ((splitKernelMulEquiv p s hs).symm g).left.val = g * (s (p g))⁻¹ := by
  have he := (splitKernelMulEquiv p s hs).apply_symm_apply g
  rw [splitKernelMulEquiv_apply, splitKernelMulEquiv_symm_right] at he
  exact eq_mul_inv_iff_mul_eq.mpr he

end Atlas.GroupTheory
