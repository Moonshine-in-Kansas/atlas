import Atlas.LinearGroups.F4.Radical

/-! The actual fifteen-parameter subgroup acts regularly on the opposite cell.
The parameters are recovered from its eight lower and seven middle coordinates. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def radicalBetween (x y : OppositeCell F) : RadicalParameters F where
  point := oppositeLowerCoordinates y.val-oppositeLowerCoordinates x.val
  central := centralSevenCoordinates y.val-centralSevenCoordinates x.val-
    radicalCocycle (oppositeLowerCoordinates y.val-oppositeLowerCoordinates x.val)
      (oppositeLowerCoordinates x.val)

theorem radicalBetween_apply (x y : OppositeCell F) :
    radicalOpposite (radicalBetween x y) x=y := by
  apply oppositeCell_coordinate_ext
  · rw [radicalOpposite_lower]
    change _+(_-_)=_
    abel
  · rw [radicalOpposite_central]
    dsimp only [radicalBetween]
    change _+_+(_-_-_)=_
    abel

theorem radicalOpposite_parameter_injective (x : OppositeCell F) :
    Function.Injective (fun p : RadicalParameters F => radicalOpposite p x) := by
  intro p q h
  have hl := congrArg (fun y : OppositeCell F => oppositeLowerCoordinates y.val) h
  have hc := congrArg (fun y : OppositeCell F => centralSevenCoordinates y.val) h
  rw [radicalOpposite_lower,radicalOpposite_lower] at hl
  have hp : p.point=q.point := add_left_cancel hl
  rw [radicalOpposite_central,radicalOpposite_central,hp] at hc
  exact Atlas.GroupTheory.BilinearExtension.ext hp (add_left_cancel hc)

theorem radicalOpposite_regular (x y : OppositeCell F) :
    ∃! p : RadicalParameters F, radicalOpposite p x=y := by
  refine ⟨radicalBetween x y,radicalBetween_apply x y,?_⟩
  intro p hp
  exact radicalOpposite_parameter_injective x (hp.trans (radicalBetween_apply x y).symm)

def radicalOrbitEquiv (x : OppositeCell F) : RadicalParameters F ≃ OppositeCell F where
  toFun p := radicalOpposite p x
  invFun y := radicalBetween x y
  left_inv p := radicalOpposite_parameter_injective x (radicalBetween_apply x _)
  right_inv := radicalBetween_apply x

end Atlas.F4
