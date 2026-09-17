import Atlas.Fischer.PointwiseAxisOctadSigns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Diagonal octad action recovers every octad coefficient semilinearly. -/
theorem pointwiseAxis_octad_coordinate_relation (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (D : Octad) (x : Coordinates) :
    e.val (xOctad D) (.inr D) * e.val x (.inr D)=
      scalarParityAut (semilinearAlgebraParity e) (x (.inr D)) := by
  have h := semilinearAlgebraAutomorphism_hermitian e (xOctad D) x
  rw [pointwiseAxis_octad_line e he D,hermitian_smul_left] at h
  change _ * hermitian (coordinateVector (.inr D)) _ = scalarParityAut _
    (hermitian (coordinateVector (.inr D)) _) at h
  rw [hermitian_coordinateVector_left,hermitian_coordinateVector_left] at h
  have hs := congrArg star h
  simpa [coordinateWeight,map_mul,scalarParityAut_star,pointwiseAxis_octad_scalar_real e he D] using hs

end Atlas.Fischer
