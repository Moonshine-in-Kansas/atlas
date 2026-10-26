import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramExponentials
import Atlas.LinearGroups.Chevalley.Adjoint

/-! The E6 diagram map on the existing generated adjoint group. Its definition
uses the permutation of the actual integral Geck matrices, not a presentation
or a group with an assumed E6 order. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open E6Data Integral
local instance : Fintype Root := Fintype.ofFinite Root
variable (R : Type*) [CommRing R]

theorem unitsDiagram_mem {g : (Matrix (base.support ⊕ Root) (base.support ⊕ Root) R)ˣ}
    (hg : g ∈ adjointSubgroup pairing base R) :
    unitsDiagram R g ∈ adjointSubgroup pairing base R := by
  have h : adjointSubgroup pairing base R ≤
      (adjointSubgroup pairing base R).comap (unitsDiagram R) := by
    rw [adjointSubgroup_le_iff]
    constructor
    · intro i t
      change unitsDiagram R _ ∈ adjointSubgroup pairing base R
      rw [unitsDiagram_raising]
      exact raising_mem_adjoint pairing base R (baseDiagram i) t
    · intro i t
      change unitsDiagram R _ ∈ adjointSubgroup pairing base R
      rw [unitsDiagram_lowering]
      exact lowering_mem_adjoint pairing base R (baseDiagram i) t
  exact h hg

def adjointDiagram : Adjoint pairing base R ≃* Adjoint pairing base R where
  toFun g := ⟨unitsDiagram R g.val, unitsDiagram_mem R g.property⟩
  invFun g := ⟨unitsDiagram R g.val, unitsDiagram_mem R g.property⟩
  left_inv g := Subtype.ext (unitsDiagram_involutive R g.val)
  right_inv g := Subtype.ext (unitsDiagram_involutive R g.val)
  map_mul' g h := Subtype.ext ((unitsDiagram R).map_mul g.val h.val)

theorem adjointDiagram_involutive : Function.Involutive (adjointDiagram R) := by
  intro g
  exact Subtype.ext (unitsDiagram_involutive R g.val)

@[simp] theorem adjointDiagram_X (i : base.support) (t : R) :
    adjointDiagram R (adjointX pairing base R i t) =
      adjointX pairing base R (baseDiagram i) t :=
  Subtype.ext (unitsDiagram_raising R i t)

@[simp] theorem adjointDiagram_Y (i : base.support) (t : R) :
    adjointDiagram R (adjointY pairing base R i t) =
      adjointY pairing base R (baseDiagram i) t :=
  Subtype.ext (unitsDiagram_lowering R i t)

theorem adjointDiagram_map {S : Type*} [CommRing S] (φ : R →+* S)
    (g : Adjoint pairing base R) :
    adjointMap pairing base φ (adjointDiagram R g) =
      adjointDiagram S (adjointMap pairing base φ g) := by
  apply Subtype.ext
  apply Units.ext
  rfl

end Atlas.Chevalley.TwistedE6
