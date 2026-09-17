import Atlas.Fischer.ProductTraceCocode
import Atlas.Fischer.WeightedCubicTensor

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def coordinateTripleWord (i j k : CoordinateIndex) : golay :=
  productTraceCoordinateWord i + productTraceCoordinateWord j + productTraceCoordinateWord k

theorem cubic_parker_action (e : ParkerStandardGroup) (x y z : Coordinates) :
    cubic (parkerCoordinateAction e x) (parkerCoordinateAction e y) (parkerCoordinateAction e z) =
      scalarParityAut (parkerStandardParity e).toAdd (cubic x y z) := by
  rw [cubic,← parkerCoordinateAction_product,parkerCoordinateAction_hermitian]
  rfl

/-- The actual cocode gives the scalar sign character of every retained cubic coefficient. -/
theorem coordinateCubic_cocode (d : Cocode) (i j k : CoordinateIndex) :
    parkerScalarSign (cocodePairing (coordinateTripleWord i j k) d) * coordinateCubic i j k =
      scalarParityAut (cocodeParity d) (coordinateCubic i j k) := by
  have h := cubic_parker_action (parkerCocodeStandard d)
    (coordinateVector i) (coordinateVector j) (coordinateVector k)
  change cubic ((parkerAlgebraRepresentation (parkerCocodeStandard d)).val (coordinateVector i))
    ((parkerAlgebraRepresentation (parkerCocodeStandard d)).val (coordinateVector j))
    ((parkerAlgebraRepresentation (parkerCocodeStandard d)).val (coordinateVector k)) = _ at h
  rw [productTrace_cocode_basis,productTrace_cocode_basis,productTrace_cocode_basis,
    cubic_smul_first,cubic_smul_second,cubic_smul_third,parkerStandardParity_cocode] at h
  simpa only [coordinateTripleWord,cocodePairing,map_add,parkerScalarSign_add,
    coordinateCubic,mul_assoc,toAdd_ofAdd] using h

theorem coordinateCubic_vanish_of_labels (i j k : CoordinateIndex)
    (h0 : coordinateTripleWord i j k ≠ 0) (h1 : coordinateTripleWord i j k ≠ golayOne) :
    coordinateCubic i j k=0 := by
  obtain ⟨d,hd,hp⟩ := productTrace_evenCocode_separates _ h0 h1
  have h := coordinateCubic_cocode d i j k
  rw [hd,scalarParityAut_zero,hp] at h
  have hs : parkerScalarSign 1 = (-1 : Scalar) := by simp [parkerScalarSign]
  rw [hs] at h
  linear_combination -(1/2 : Scalar) * h

def allOneCodeLine : Submodule Bit golay := Submodule.span Bit ({golayOne} : Set golay)

theorem mem_allOneCodeLine (w : golay) : w ∈ allOneCodeLine ↔ w=0 ∨ w=golayOne := by
  rw [allOneCodeLine,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    rcases (show ∀ b : Bit, b=0 ∨ b=1 from by decide) a with rfl | rfl
    · exact Or.inl (by simpa using ha.symm)
    · exact Or.inr (by simpa using ha.symm)
  · rintro (rfl | rfl)
    · exact ⟨0,zero_smul _ _⟩
    · exact ⟨1,one_smul _ _⟩

theorem coordinateCubic_nonzero_support (i j k : CoordinateIndex)
    (h : coordinateCubic i j k ≠ 0) : coordinateTripleWord i j k ∈ allOneCodeLine := by
  rw [mem_allOneCodeLine]
  by_contra hn
  push_neg at hn
  exact h (coordinateCubic_vanish_of_labels i j k hn.1 hn.2)

end Atlas.Fischer
