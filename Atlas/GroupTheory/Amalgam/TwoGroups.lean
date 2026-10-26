import Atlas.GroupTheory.Amalgam.UniversalCompletion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-! The two-group amalgamated product is a span completion. Its universal
property is proved without assuming that either attaching map is injective. -/

open CategoryTheory CategoryTheory.Limits

namespace Atlas.GroupTheory.Amalgam

variable {H G K L : Type} [Group H] [Group G] [Group K] [Group L]
  (f : H →* G) (g : H →* K)

abbrev twoGroupDiagram := span (GrpCat.ofHom f) (GrpCat.ofHom g)

abbrev TwoGroupCompletion := Completion (twoGroupDiagram f g)

def twoGroupLeft : G →* TwoGroupCompletion f g :=
  inclusion (twoGroupDiagram f g) WalkingSpan.left

def twoGroupRight : K →* TwoGroupCompletion f g :=
  inclusion (twoGroupDiagram f g) WalkingSpan.right

theorem twoGroup_compatible : (twoGroupLeft f g).comp f = (twoGroupRight f g).comp g := by
  ext x
  exact (inclusion_compatible (twoGroupDiagram f g) WalkingSpan.Hom.fst x).trans
    (inclusion_compatible (twoGroupDiagram f g) WalkingSpan.Hom.snd x).symm

/-- The extension of two homomorphisms agreeing on the amalgamated group. -/
def twoGroupLift (a : G →* L) (b : K →* L) (h : a.comp f = b.comp g) :
    TwoGroupCompletion f g →* L :=
  lift (coconeMaps _ (PushoutCocone.mk (GrpCat.ofHom a) (GrpCat.ofHom b)
    (GrpCat.hom_ext h)))

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem twoGroupLift_left (a : G →* L) (b : K →* L)
    (h : a.comp f = b.comp g) (x : G) :
    twoGroupLift f g a b h (twoGroupLeft f g x) = a x :=
  by rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem twoGroupLift_right (a : G →* L) (b : K →* L)
    (h : a.comp f = b.comp g) (x : K) :
    twoGroupLift f g a b h (twoGroupRight f g x) = b x :=
  by rfl

/-- The pair of canonical maps determines homomorphisms out of the product. -/
theorem twoGroup_hom_ext {a b : TwoGroupCompletion f g →* L}
    (hl : ∀ x, a (twoGroupLeft f g x) = b (twoGroupLeft f g x))
    (hr : ∀ x, a (twoGroupRight f g x) = b (twoGroupRight f g x)) : a = b := by
  apply hom_ext
  intro j x
  cases j with
  | none =>
    rw [← inclusion_compatible (twoGroupDiagram f g) WalkingSpan.Hom.fst x]
    exact hl _
  | some j => cases j <;> first | exact hl x | exact hr x

end Atlas.GroupTheory.Amalgam
