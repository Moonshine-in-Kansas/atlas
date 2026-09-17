import Atlas.Fischer.OctadicFortySixBlock
import Atlas.Fischer.SignedCoordinateIndependence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

abbrev OctadicFortySixIndex (O : Octad) := OctadExterior O ⊕ OctadShortenedHyperplane O

def octadicFortySixFamily {O : Octad} (Q : OctadCalibration O) : OctadicFortySixIndex O → Coordinates :=
  Sum.elim (fun i => u i.val) (calibratedHyperplaneVector Q)

theorem octadicFortySixFamily_independent {O : Octad} (Q : OctadCalibration O) :
    LinearIndependent Scalar (octadicFortySixFamily Q) := by
  let j : OctadicFortySixIndex O → CoordinateIndex := Sum.elim (fun i => Sum.inl i.val)
    (fun b => Sum.inr (signedOctadSupport (calibratedHyperplaneLift Q b)))
  have hj : Function.Injective j := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
      | inr b => simp [j] at h
    | inr a =>
      cases b with
      | inl b => simp [j] at h
      | inr b => exact congrArg Sum.inr (calibratedHyperplaneSupport_injective Q (Sum.inr.inj h))
  let s : OctadicFortySixIndex O → Bit :=
    Sum.elim (fun _ => 0) (fun b => (calibratedHyperplaneLift Q b).val.2)
  have hv : octadicFortySixFamily Q = fun i => parkerScalarSign (s i) • coordinateVector (j i) := by
    funext i
    cases i with
    | inl i => simp [octadicFortySixFamily,s,j,parkerScalarSign,u]
    | inr b => rfl
  rw [hv]
  exact signedCoordinate_linearIndependent j hj s

theorem octadicFortySixFamily_range {O : Octad} (Q : OctadCalibration O) :
    Set.range (octadicFortySixFamily Q)=octadicFortySixGenerators Q := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i,rfl⟩
    | inr b => exact Or.inr ⟨b,rfl⟩
  · rintro (⟨i,rfl⟩ | ⟨b,rfl⟩)
    · exact ⟨Sum.inl i,rfl⟩
    · exact ⟨Sum.inr b,rfl⟩

theorem octadicFortySixSpace_dimension {O : Octad} (Q : OctadCalibration O) :
    Module.finrank Scalar (octadicFortySixSpace Q)=46 := by
  classical
  rw [octadicFortySixSpace,← octadicFortySixFamily_range,
    finrank_span_eq_card (octadicFortySixFamily_independent Q)]
  rw [Fintype.card_sum,octadShortenedHyperplane_card]
  have hi : Fintype.card (OctadExterior O)=16 := by
    rw [← Nat.card_eq_fintype_card,octadExterior_card]
  rw [hi]

end Atlas.Fischer
