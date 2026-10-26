import Atlas.LinearGroups.F4.PointOpenMove
import Atlas.Algebra.Albert.OppositeChart

noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def firstTorusParameter (s : Fˣ) : TorusParameters F := ![s,1,1,1]

theorem firstTorusParameter_C7 (s : Fˣ) (x : Carrier F) :
    ((diagonalTorus (firstTorusParameter s)).val x).2 2 7=(s.val)⁻¹*x.2 2 7 := by
  change (torusApply (firstTorusParameter s) x).2 2 7=_
  simp [torusApply,torusScale,weightCharacter,RootData.simpleCoefficients,
    RootData.coordinates,Weights.slotRoot,firstTorusParameter,Fin.prod_univ_succ]

theorem whiteZero_move_to_normalized_open (x : Carrier F) (hx : x≠0)
    (ha : adjoint x=0) (ht : trace x=0) :
    ∃ g : Model F, (g.val x).2 2 7=1 := by
  obtain ⟨g,hg⟩ := whiteZero_move_to_open x hx ha ht
  let s : Fˣ := Units.mk0 ((g.val x).2 2 7) hg
  refine ⟨diagonalTorus (firstTorusParameter s)*g,?_⟩
  change ((diagonalTorus (firstTorusParameter s)).val (g.val x)).2 2 7=1
  rw [firstTorusParameter_C7]
  exact inv_mul_cancel₀ hg

theorem whiteZero_move_into_oppositeCell (x : Carrier F) (hx : x≠0)
    (ha : adjoint x=0) (ht : trace x=0) :
    ∃ (g : Model F) (y : OppositeCell F), g.val x=y.val := by
  obtain ⟨g,hg⟩ := whiteZero_move_to_normalized_open x hx ha ht
  refine ⟨g,⟨g.val x,?_,?_,hg⟩,rfl⟩
  · rw [stabilizer_adjoint,ha,map_zero]
  · rw [stabilizer_trace,ht]

end Atlas.F4
