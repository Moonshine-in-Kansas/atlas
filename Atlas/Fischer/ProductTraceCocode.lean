import Atlas.Fischer.ProductTraceAutomorphisms
import Atlas.Fischer.ParkerAlgebraRepresentation
import Atlas.Fischer.RationalCocodeAction
import Atlas.Fischer.ParkerStandardOrder

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Actual even cocode characters separate codewords modulo the all-one line. -/
theorem productTrace_evenCocode_separates (w : golay) (h0 : w ≠ 0) (h1 : w ≠ golayOne) :
    ∃ d : Cocode, cocodeParity d = 0 ∧ cocodePairing w d = 1 := by
  let P := Submodule.span Bit ({golayOne} : Set golay)
  have hw : w ∉ P := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a,ha⟩
    have hb : a=0 ∨ a=1 := by exact (show ∀ b : Bit, b=0 ∨ b=1 from by decide) a
    rcases hb with rfl | rfl
    · exact h0 (by simpa using ha.symm)
    · exact h1 (by simpa using ha.symm)
  obtain ⟨l,hl,hP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
  let d := cocodeDualEquiv.symm l
  refine ⟨d,?_,?_⟩
  · change cocodeDualEquiv d golayOne=0
    rw [LinearEquiv.apply_symm_apply]
    have hm : l golayOne ∈ P.map l := Submodule.mem_map.mpr
      ⟨golayOne,Submodule.subset_span (Set.mem_singleton _),rfl⟩
    rw [hP] at hm
    exact hm
  · change cocodeDualEquiv d w=1
    rw [LinearEquiv.apply_symm_apply]
    rcases (show ∀ b : Bit, b=0 ∨ b=1 from by decide) (l w) with h | h
    · exact (hl h).elim
    · exact h

def productTraceCoordinateWord : CoordinateIndex → golay
  | Sum.inl _ => 0
  | Sum.inr O => octadWord O

theorem productTrace_cocode_basis (d : Cocode) (i : CoordinateIndex) :
    (parkerAlgebraRepresentation (parkerCocodeStandard d)).val (coordinateVector i) =
      parkerScalarSign (cocodePairing (productTraceCoordinateWord i) d) • coordinateVector i := by
  change parkerCoordinateAction (parkerCocodeStandard d) (coordinateVector i) = _
  rw [parkerCoordinateAction_basis,parkerCoordinateEquiv_cocode,parkerCoordinateSign_cocode]
  rfl

/-- No tensor or root multiplicativity hypothesis is used: this is the actual
linear cocode action on the retained multiplication table. -/
theorem productTrace_coordinate_vanish_of_labels (i j : CoordinateIndex)
    (h0 : productTraceCoordinateWord i + productTraceCoordinateWord j ≠ 0)
    (h1 : productTraceCoordinateWord i + productTraceCoordinateWord j ≠ golayOne) :
    productTrace (coordinateVector i) (coordinateVector j) = 0 := by
  obtain ⟨d,hd,hp⟩ := productTrace_evenCocode_separates _ h0 h1
  have h := productTrace_algebra_automorphism (parkerAlgebraRepresentation (parkerCocodeStandard d))
    (coordinateVector i) (coordinateVector j)
  rw [productTrace_cocode_basis,productTrace_cocode_basis,
    productTrace_smul_left,productTrace_smul_right,parkerScalarSign_star,
    parkerAlgebraRepresentation_parity,parkerStandardParity_cocode] at h
  change _ = scalarParityAut (cocodeParity d) _ at h
  rw [hd,scalarParityAut_zero,← mul_assoc,← parkerScalarSign_add] at h
  have hp' : cocodePairing (productTraceCoordinateWord i) d +
      cocodePairing (productTraceCoordinateWord j) d = 1 := by
    simpa [cocodePairing] using hp
  rw [hp'] at h
  have hs : parkerScalarSign 1 = (-1 : Scalar) := by simp [parkerScalarSign]
  rw [hs] at h
  linear_combination -(1/2 : Scalar) * h

end Atlas.Fischer
