import Atlas.Fischer.RationalCocodeAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual simultaneous eigenvector condition for the cocode annihilator. -/
def OctadCommonEigenvector (O : Octad) (a : octadEvenCode O) (x : Coordinates) : Prop :=
  ∀ d : octadCocodeAnnihilator O,
    parkerCoordinateAction (parkerCocodeStandard d.val) x =
      rationalBitSign (octadLabelCharacter O d a) • x

/-- Coordinate support characterizes the actual common eigenspaces. -/
theorem octadCommonEigenvector_iff (O : Octad) (a : octadEvenCode O) (x : Coordinates) :
    OctadCommonEigenvector O a x ↔
      ∀ p, octadRationalCodeLabel O p ≠ a → rationalCoordinateEquiv x p=0 := by
  constructor
  · intro hx p hp
    by_contra hn
    apply hp
    apply octadLabelCharacter_separates
    intro d
    have he := congrArg (fun y => rationalCoordinateEquiv y p) (hx d)
    rw [rationalCoordinateEquiv_cocode,map_smul,Pi.smul_apply] at he
    change rationalBitSign (cocodePairing (rationalCoordinateGolayWord p) d.val) *
      rationalCoordinateEquiv x p = rationalBitSign (octadLabelCharacter O d a) *
        rationalCoordinateEquiv x p at he
    apply rationalBitSign_injective
    rw [show octadLabelCharacter O d (octadRationalCodeLabel O p)=
      cocodePairing (rationalCoordinateGolayWord p) d.val from
        octadLabelCharacter_restriction O d _]
    exact mul_right_cancel₀ hn he
  · intro hx d
    apply rationalCoordinateEquiv.injective
    funext p
    rw [rationalCoordinateEquiv_cocode,map_smul,Pi.smul_apply]
    change rationalBitSign (cocodePairing (rationalCoordinateGolayWord p) d.val) *
      rationalCoordinateEquiv x p = rationalBitSign (octadLabelCharacter O d a) *
        rationalCoordinateEquiv x p
    by_cases hp : octadRationalCodeLabel O p=a
    · rw [← octadLabelCharacter_restriction O d]
      change rationalBitSign (octadLabelCharacter O d (octadRationalCodeLabel O p)) * _ = _
      rw [hp]
    · rw [hx p hp,mul_zero,mul_zero]

/-- The previously constructed rational grade is exactly the corresponding
common eigenspace for the actual N_O action. -/
theorem octadRationalGrade_iff_commonEigenvector (O : Octad) (p : RationalCoordinateIndex)
    (x : Coordinates) :
    x ∈ octadRationalGrade O (octadRationalLabel O p) ↔
      OctadCommonEigenvector O (octadRationalCodeLabel O p) x := by
  rw [octadCommonEigenvector_iff]
  change (∀ q, octadRationalLabel O q ≠ octadRationalLabel O p → rationalCoordinateEquiv x q=0) ↔ _
  constructor
  · intro h q hq
    exact h q (fun he => hq ((octadRationalCodeLabel_eq_iff O q p).mpr he))
  · intro h q hq
    exact h q (fun he => hq ((octadRationalCodeLabel_eq_iff O q p).mp he))

end Atlas.Fischer
