import Atlas.Fischer.ParkerCoordinateAction
import Atlas.Fischer.ParkerOctadSignFaithfulness

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerCoordinateAction_eq_one (e : ParkerStandardGroup)
    (h : ∀ x : Coordinates, parkerCoordinateAction e x = x) : e = 1 := by
  classical
  have hg : parkerStandardProjection e = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change (parkerStandardProjection e).val i = i
    by_contra hi
    have hh := h (u i)
    rw [parkerCoordinateAction_u] at hh
    have hc := congrFun hh (Sum.inl i)
    simp [u, coordinateVector, Pi.single_apply, hi, Ne.symm hi] at hc
  apply parkerStandard_eq_one_of_octad_signs e hg
  intro O
  have hp : parkerCoordinateEquiv e (Sum.inr O) = Sum.inr O := by
    change Sum.inr (parkerOctadAction e O) = Sum.inr O
    simp [parkerOctadAction, hg]
  have hh := h (xOctad O)
  change parkerCoordinateAction e (coordinateVector (.inr O)) = coordinateVector (.inr O) at hh
  rw [parkerCoordinateAction_basis, hp] at hh
  have hc := congrFun hh (Sum.inr O)
  have hs : parkerScalarSign (parkerCoordinateSign e (.inr O)) = 1 := by
    simpa [coordinateVector, Pi.single_apply] using hc
  exact (parkerScalarSign_eq_one_iff _).mp hs

noncomputable instance : FaithfulSMul ParkerStandardGroup Coordinates where
  eq_of_smul_eq_smul := fun {e f} h => by
    have hh : ∀ x, parkerCoordinateAction (e⁻¹ * f) x = x := by
      intro x
      rw [parkerCoordinateAction_mul]
      change parkerCoordinateAction e⁻¹ (f • x) = x
      rw [← h x]
      change parkerCoordinateAction e⁻¹ (parkerCoordinateAction e x) = x
      rw [← parkerCoordinateAction_mul, inv_mul_cancel, parkerCoordinateAction_one]
    exact inv_mul_eq_one.mp (parkerCoordinateAction_eq_one _ hh)

end Atlas.Fischer
