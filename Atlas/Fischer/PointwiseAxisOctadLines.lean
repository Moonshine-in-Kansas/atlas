import Atlas.Fischer.PointwiseAxisCocode
import Atlas.Fischer.ProductTraceOffDiagonal

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The full cocode acts diagonally on the retained coordinate basis. -/
theorem cocodeCoordinateRepresentation_basis (d : Cocode) (k : CoordinateIndex) :
    cocodeCoordinateRepresentation (Multiplicative.ofAdd d) (coordinateVector k)=
      parkerScalarSign (cocodePairing (productTraceCoordinateWord k) d) • coordinateVector k :=
  productTrace_cocode_basis d k

/-- Commutation with the cocode gives exact eigenvectors for every image octad. -/
theorem pointwiseAxis_octad_eigen (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (d : Cocode) (O : Octad) :
    cocodeCoordinateRepresentation (Multiplicative.ofAdd d) (e.val (xOctad O))=
      parkerScalarSign (cocodePairing (octadWord O) d) • e.val (xOctad O) := by
  rw [← pointwiseAxis_commutes_cocode e he]
  change e.val (cocodeCoordinateRepresentation _ (coordinateVector (.inr O)))=_
  rw [cocodeCoordinateRepresentation_basis,semilinearAlgebraParity_spec]
  change scalarParityAut _ (parkerScalarSign _) • _ = _
  rcases (show ∀ b : Bit, b=0 ∨ b=1 from by decide) (semilinearAlgebraParity e) with h | h
  · rw [h,scalarParityAut_zero]; rfl
  · rw [h,scalarParityAut_one,parkerScalarSign_star]; rfl

/-- Distinct actual octad lines are separated by the even cocode. -/
theorem pointwiseAxis_distinct_octad_pairing (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (O P : Octad) (hOP : O ≠ P) :
    hermitian (xOctad P) (e.val (xOctad O))=0 := by
  have h0 : octadWord P + octadWord O ≠ 0 := by
    intro h
    have hh := congrArg (fun c : golay => c + octadWord O) h
    rw [add_assoc,parkerGolay_add_self,add_zero,zero_add] at hh
    exact hOP (octadWord_injective hh).symm
  have h1 : octadWord P + octadWord O ≠ golayOne :=
    productTraceCoordinateWord_sum_ne_one (.inr P) (.inr O)
  obtain ⟨d,hd,hp⟩ := productTrace_evenCocode_separates _ h0 h1
  have hm := parkerCoordinateAction_hermitian (parkerCocodeStandard d)
    (xOctad P) (e.val (xOctad O))
  change hermitian (cocodeCoordinateRepresentation (Multiplicative.ofAdd d) (xOctad P))
    (cocodeCoordinateRepresentation (Multiplicative.ofAdd d) (e.val (xOctad O)))=_ at hm
  rw [pointwiseAxis_octad_eigen e he] at hm
  change hermitian (cocodeCoordinateRepresentation (Multiplicative.ofAdd d)
    (coordinateVector (.inr P))) _ = _ at hm
  rw [cocodeCoordinateRepresentation_basis,hermitian_smul_left,hermitian_smul_right,
    parkerScalarSign_star,parkerStandardParity_cocode] at hm
  change parkerScalarSign (cocodePairing (octadWord P) d) *
    (parkerScalarSign (cocodePairing (octadWord O) d) * _) =
    scalarParityAut (cocodeParity d) _ at hm
  rw [hd,scalarParityAut_zero,← mul_assoc,← parkerScalarSign_add] at hm
  have hp0 : cocodePairing (octadWord P) d + cocodePairing (octadWord O) d=1 := by
    simpa [cocodePairing] using hp
  rw [hp0] at hm
  norm_num [parkerScalarSign] at hm
  change -hermitian (xOctad P) (e.val (xOctad O)) = hermitian (xOctad P) (e.val (xOctad O)) at hm
  linear_combination (-1/2 : Scalar) * hm

/-- Fixing the point axes eliminates the point component of every image octad. -/
theorem pointwiseAxis_octad_point_zero (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (O : Octad) (i : Omega) :
    e.val (xOctad O) (.inl i)=0 := by
  have h := semilinearAlgebraAutomorphism_hermitian e (u i) (xOctad O)
  rw [he,hermitian_u_xOctad,map_zero] at h
  change hermitian (coordinateVector (.inl i)) _=0 at h
  rw [hermitian_coordinateVector_left] at h
  norm_num [coordinateWeight] at h
  exact h

/-- The image of each actual octad basis vector lies on that same octad line. -/
theorem pointwiseAxis_octad_line (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (O : Octad) :
    e.val (xOctad O)=(e.val (xOctad O) (.inr O)) • xOctad O := by
  classical
  funext k
  cases k with
  | inl i => simp [pointwiseAxis_octad_point_zero e he]
  | inr P =>
    by_cases h : P=O
    · subst P; simp
    · have hh := pointwiseAxis_distinct_octad_pairing e he O P (Ne.symm h)
      change hermitian (coordinateVector (.inr P)) _=0 at hh
      rw [hermitian_coordinateVector_left] at hh
      norm_num [coordinateWeight] at hh
      simp [h,hh]

end Atlas.Fischer
