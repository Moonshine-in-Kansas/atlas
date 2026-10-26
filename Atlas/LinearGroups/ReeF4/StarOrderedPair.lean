import Atlas.LinearGroups.ReeF4.StarCoefficientChecks

/-! Evaluation of the candidate on ordered marked-basis wedges. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

private def increasingPair (i j : Fin (Fintype.card TraceZeroCoordinate)) (h : i < j) :
    Fin 2 ↪o Fin (Fintype.card TraceZeroCoordinate) :=
  OrderEmbedding.ofStrictMono ![i,j] (by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all)

theorem proposedStarLinear_ordered_pair
    (i j : Fin (Fintype.card TraceZeroCoordinate)) (h : i < j) :
    proposedStarLinear (wedge (orderedMarkedBasis (F := F) i) (orderedMarkedBasis j)) =
      extensionCoefficient ((Fintype.equivFin TraceZeroCoordinate).symm i)
        ((Fintype.equivFin TraceZeroCoordinate).symm j) := by
  let e := increasingPair i j h
  let s : ExteriorIndex := Set.powersetCard.ofFinEmbEquiv e
  have hb : markedExteriorBasis (F := F) s =
      wedge (orderedMarkedBasis i) (orderedMarkedBasis j) := by
    simp only [markedExteriorBasis, exteriorPower.coe_basis, exteriorPower.ιMulti_family,
      s, Equiv.symm_apply_apply]
    unfold wedge
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [← hb, proposedStarLinear_basis]
  simp only [exteriorLabel, s, Equiv.symm_apply_apply]
  rfl

end Atlas.ReeF4
