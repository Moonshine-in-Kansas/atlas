import Atlas.Conway.NormSixOddOrbits
import Atlas.Conway.SextetIsometry

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

def normSixFusionCoordinates : IntegerCoordinates := fun p =>
  if p.1 = (0,0) then (if p.2 = 0 then 1 else -3)
  else if p.1 = (2,1) then 1 else -1

theorem normSixFusion_formula :
    (zeta.val (normSixVector ((0,0),0))).val = normSixFusionCoordinates := by
  apply rationalEmbedding_injective
  rw [zeta_agrees]
  have hv : (normSixVector ((0,0),0)).val = fun i => if i = ((0,0),0) then 5 else 1 :=
    funext (normSixVector_apply ((0,0),0))
  rw [hv]
  decide +kernel

theorem normSixVector_five_shape :
    (normSixVector ((0,0),0)).val ∈ oddOneFiveVectors 0 := by
  apply reconstruct_oneFive _ (normSixVector ((0,0),0)).prop
  · intro i
    rw [normSixVector_apply]
    split_ifs <;> decide
  · rw [normSixVector_norm]; decide
  · have hv : (normSixVector ((0,0),0)).val = fun i => if i = ((0,0),0) then 5 else 1 :=
      funext (normSixVector_apply ((0,0),0))
    rw [hv]
    decide +kernel
  · have hv : (normSixVector ((0,0),0)).val = fun i => if i = ((0,0),0) then 5 else 1 :=
      funext (normSixVector_apply ((0,0),0))
    rw [hv]
    decide +kernel

theorem normSixFusion_three_shape :
    (zeta.val (normSixVector ((0,0),0))).val ∈ oddNoFiveVectors 3 := by
  apply reconstruct_noFive _ (zeta.val (normSixVector ((0,0),0))).prop
  · rw [normSixFusion_formula]
    decide +kernel
  · rw [zeta.prop,normSixVector_norm]; decide
  · rw [normSixFusion_formula]
    decide +kernel
  · rw [normSixFusion_formula]
    decide +kernel

end Atlas.Conway
