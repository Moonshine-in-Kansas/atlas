import Atlas.Rudvalis.CoupleQuartetTransport
import Atlas.Rudvalis.CrossRowEnergy

namespace Atlas.Rudvalis

 theorem codeCouple_selected_coordinate_iff (g : codeCoupleStabilizer) (i : Coordinate) :
    (g.val.val.right i).1∈referenceDozenRows ↔ i.1∈referenceDozenRows := by
  have h := codeCouple_coordinateDozen_iff g (coordinateCross i)
  rw [coordinateCross_action] at h
  simpa only [referenceCoordinateDozen,coordinateCross_mem_selectedRows_iff] using h

 theorem codeCouple_projection_commute (g : codeCoupleStabilizer) (v : RationalSpace) :
    coordinateRowProjection referenceDozenRows (rationalMonomialHom g.val.val v)=
      rationalMonomialHom g.val.val (coordinateRowProjection referenceDozenRows v) := by
  classical
  ext i
  have hm : (g.val.val.right.symm i).1∈referenceDozenRows ↔ i.1∈referenceDozenRows := by
    have h := codeCouple_selected_coordinate_iff g (g.val.val.right.symm i)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  change (if i.1∈referenceDozenRows then liftedSign (g.val.val.left.toAdd i) (v (g.val.val.right.symm i)) else 0)=
    liftedSign (g.val.val.left.toAdd i) (if (g.val.val.right.symm i).1∈referenceDozenRows then v (g.val.val.right.symm i) else 0)
  rw [hm]
  split_ifs <;> simp [liftedSign]

 theorem codeCouple_coordinateRowEnergy (g : codeCoupleStabilizer) (v : RationalSpace) :
    coordinateRowEnergy referenceDozenRows (rationalMonomialHom g.val.val v)=
      coordinateRowEnergy referenceDozenRows v := by
  unfold coordinateRowEnergy
  rw [codeCouple_projection_commute,rationalMonomial_pairing]

 theorem codeCouple_crossRowEnergy (g : codeCoupleStabilizer) (c : MinimalCross) :
    crossRowEnergy referenceDozenRows (g.val • c)=crossRowEnergy referenceDozenRows c := by
  induction c using Quotient.inductionOn with
  | h v =>
    change coordinateRowEnergy referenceDozenRows (rationalMonomialHom g.val.val v.val.val)=
      coordinateRowEnergy referenceDozenRows v.val.val
    exact codeCouple_coordinateRowEnergy g v.val.val

end Atlas.Rudvalis
