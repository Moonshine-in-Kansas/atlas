import Atlas.Rudvalis.FourInactiveCount
import Atlas.Rudvalis.RestrictedCrossCount
import Atlas.Rudvalis.CoordinateCrossOrthogonality

/-! Exactly 192 four-block crosses are orthogonal to each coordinate cross. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem minimumWordShellLift_zero_iff (w : MinimumWords) (i : Coordinate) :
    (minimumWordShellLift w).val.val i=0 ↔ reduce w.val.val i=0 := by
  have hi := quaternary_minimum_no_twos w.val.val w.val.prop w.prop i
  have h : ∀a : ZMod 4,a≠2 → (((integerRepresentative a : ℤ) : ℚ)/2=0 ↔ reduceScalar a=0) := by
    decide +kernel
  exact h _ hi

theorem fourSupport_pair_zero_iff (d : BinaryWord) (hd : admissibleFourSupport d)
    (p : Point) (x : E) : (d (p,x)=0 ∧ d (p,x+p.val)=0) ↔ ∀y : E,d (p,y)=0 := by
  obtain ⟨v,hv⟩ := fourSupportEquiv.surjective ⟨d,hd⟩
  have he := congrArg Subtype.val hv
  change (fourSupportEquiv v).val=d at he
  rw [←he]
  exact (fourSupport_parameter_pair_zero v p x).trans (fourSupport_parameter_row_zero v p).symm

theorem fourWord_coordinate_orthogonal_iff (w : FourMinimumWords) (p : Point) (x : E) :
    CrossOrthogonal (coordinateCross (p,x)) (minimalCross (minimumWordShellLift (fourMinimumWord w))) ↔
      ∀y : E,reduce w.val.val (p,y)=0 := by
  rw [coordinateCross,crossOrthogonal_mk]
  change HermitianOrthogonal (coordinateMinimum (p,x)) (minimumWordShellLift (fourMinimumWord w)).val.val ↔ _
  rw [coordinate_hermitianOrthogonal_pair,minimumWordShellLift_zero_iff,minimumWordShellLift_zero_iff]
  exact fourSupport_pair_zero_iff _ w.prop.2 p x

noncomputable def fourWordShellEquiv : FourMinimumWords ≃ fourShellPiece :=
  Equiv.ofInjective (fun w : FourMinimumWords => minimumWordShellLift (fourMinimumWord w)) (by
    intro a b h
    exact Subtype.ext (congrArg (fun u : MinimumWords => u.val) (minimumWordShellLift_injective h)))

noncomputable def fourOrthogonalShellEquiv (p : Point) (x : E) :
    FourInactiveWords p ≃ RestrictedShellPiece fourShellPiece (CrossOrthogonal (coordinateCross (p,x))) :=
  Equiv.subtypeEquiv fourWordShellEquiv (fun w => (fourWord_coordinate_orthogonal_iff w p x).symm)

theorem fourOrthogonalShell_card (p : Point) (x : E) :
    Nat.card (RestrictedShellPiece fourShellPiece (CrossOrthogonal (coordinateCross (p,x))))=768 := by
  rw [←Nat.card_congr (fourOrthogonalShellEquiv p x),fourInactiveWords_card]

/-- The count concerns actual quotient crosses of actual minimum lattice vectors. -/
theorem fourOrthogonalCrosses_card (p : Point) (x : E) :
    Nat.card {c : FourBlockCrosses //
      CrossOrthogonal (coordinateCross (p,x)) (shellPieceCrossMap fourShellPiece c)}=192 := by
  have h := restricted_shell_cross_card fourShellPiece (CrossOrthogonal (coordinateCross (p,x)))
  rw [fourOrthogonalShell_card] at h
  change 768=Nat.card {c : FourBlockCrosses // CrossOrthogonal (coordinateCross (p,x)) (shellPieceCrossMap fourShellPiece c)}*4 at h
  omega

end Atlas.Rudvalis
