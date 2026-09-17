import Atlas.Fischer.ParkerBasicFrame

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Cubic scalar times Parker factorization is unique in the actual full algebra
group, without any assertion about root-generated containment. -/
theorem scalar_parker_factor_injective : Function.Injective
    (fun t : Mu3 × ParkerStandardGroup =>
      scalarAlgebraRepresentation t.1 * parkerAlgebraRepresentation t.2) := by
  rintro ⟨a,h⟩ ⟨b,k⟩ he
  have hx := congrArg (fun e : SemilinearAlgebraAutomorphism => e.val axisSum) he
  change a.val.val • parkerCoordinateAction h axisSum =
    b.val.val • parkerCoordinateAction k axisSum at hx
  rw [parkerCoordinateAction_axisSum,parkerCoordinateAction_axisSum] at hx
  have hz : axisSum ≠ 0 := by
    intro hh
    have hv := congrFun hh (.inl (Classical.choice inferInstance : Omega))
    simp [axisSum] at hv
  have hab : a=b := by
    apply Subtype.ext
    apply Units.ext
    exact smul_left_injective Scalar hz hx
  subst b
  have hhk := parkerAlgebraRepresentation_injective (mul_left_cancel he)
  change h=k at hhk
  subst k
  rfl

end Atlas.Fischer
