import Atlas.Rudvalis.HeavySelectedRowWeights
import Atlas.Rudvalis.CoordinateRowProjection

namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

theorem heavyCouple_minimumWord_energy (w : HeavyCoupleWords) :
    coordinateRowEnergy referenceDozenRows
      (minimumWordShellLift (heavyMinimumWord w.val)).val.val=2 := by
  classical
  change coordinateRowEnergy referenceDozenRows (halfCoordinates (integerLift w.val.val.val))=2
  rw [coordinateRowEnergy_half]
  have hz := heavyCouple_integerLift_selected_square w
  have he : (∑i : Coordinate,if i.1∈referenceDozenRows then
      (integerLift w.val.val.val i : ℚ)^2 else 0)=8 := by
    rw [Fintype.sum_prod_type]
    have hi (p : Point) : (∑x : E,if p∈referenceDozenRows then
        (integerLift w.val.val.val (p,x) : ℚ)^2 else 0)=
        if p∈referenceDozenRows then ∑x : E,(integerLift w.val.val.val (p,x) : ℚ)^2 else 0 := by
      by_cases h : p∈referenceDozenRows <;> simp [h]
    simp_rw [hi]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_filter] at hz ⊢
    exact_mod_cast hz
  rw [he]
  norm_num

theorem heavyCouple_shell_energy
    (v : RestrictedShellPiece heavyShellPiece ReferenceCoupleOrthogonal) :
    coordinateRowEnergy referenceDozenRows v.val.val.val.val=2 := by
  let w := heavyCoupleShellEquiv.symm v
  have h := heavyCoupleShellEquiv.apply_symm_apply v
  have he : (minimumWordShellLift (heavyMinimumWord w.val)).val.val=v.val.val.val.val :=
    congrArg (fun a : RestrictedShellPiece heavyShellPiece ReferenceCoupleOrthogonal =>
      a.val.val.val.val) h
  rw [←he]
  exact heavyCouple_minimumWord_energy w

end Atlas.Rudvalis
