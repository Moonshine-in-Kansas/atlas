import Atlas.LinearGroups.Chevalley.TwistedE6.AdjointDiagram
import Atlas.LinearGroups.Chevalley.CoefficientInvolution
import Atlas.GroupTheory.GraphFieldFixedPoints

/-! The graph--Frobenius equalizer in the actual adjoint elementary E6 model.
This is an intermediate group only: no equality with the simply connected
fixed group's central quotient, nor order or simplicity, is asserted here. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open E6Data Atlas.GroupTheory
local instance : Fintype Root := Fintype.ofFinite Root
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem adjointDiagram_commute_frobenius :
    Function.Commute (adjointDiagram K) (adjointFrobenius pairing base F K) := by
  intro g
  exact (adjointDiagram_map K (Atlas.FiniteQuadratic.conjugation F K).toRingHom g).symm

def adjointTwist : Adjoint pairing base K ≃* Adjoint pairing base K :=
  graphFieldTwist (adjointDiagram K) (adjointFrobenius pairing base F K)

theorem adjointTwist_involutive (hdeg : Module.finrank F K = 2) :
    Function.Involutive (adjointTwist F K) :=
  graphFieldTwist_involutive _ _ (adjointDiagram_involutive K)
    (adjointFrobenius_involutive pairing base F K hdeg)
    (adjointDiagram_commute_frobenius F K)

@[simp] theorem adjointTwist_X (i : base.support) (t : K) :
    adjointTwist F K (adjointX pairing base K i t) =
      adjointX pairing base K (baseDiagram i) (t ^ Nat.card F) := by
  simp only [adjointTwist, graphFieldTwist_apply, adjointFrobenius_X, adjointDiagram_X]

@[simp] theorem adjointTwist_Y (i : base.support) (t : K) :
    adjointTwist F K (adjointY pairing base K i t) =
      adjointY pairing base K (baseDiagram i) (t ^ Nat.card F) := by
  simp only [adjointTwist, graphFieldTwist_apply, adjointFrobenius_Y, adjointDiagram_Y]

def adjointFixedSubgroup : Subgroup (Adjoint pairing base K) :=
  automorphismFixedSubgroup (adjointTwist F K)

theorem mem_adjointFixedSubgroup_iff (g : Adjoint pairing base K) :
    g ∈ adjointFixedSubgroup F K ↔ adjointFrobenius pairing base F K g = adjointDiagram K g :=
  mem_graphFieldFixed_iff _ _ (adjointDiagram_involutive K) g

end Atlas.Chevalley.TwistedE6
