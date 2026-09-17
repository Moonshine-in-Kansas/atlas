import Atlas.Fischer.OctadResidualSigns
import Atlas.Fischer.CocodeCoordinates

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The locally reconstructed residual signs are the actual cocode character,
with exactly the prescribed scalar-conjugation parity. -/
theorem octad_residual_cocode (i j : Omega) (hij : i ≠ j)
    (μ : Octad → Bit) (ε : Bit)
    (hadd : ∀ D E (h : (D.val ∩ E.val).card = 4),
      μ (cubicSextetCompletion D E h) = μ D + μ E)
    (hzero : ∀ D, i ∉ D.val → j ∉ D.val → μ D = 0)
    (hboth : ∀ D, i ∈ D.val → j ∈ D.val → μ D = ε) :
    ∃ d : Cocode, cocodeParity d = ε ∧ ∀ D, cocodePairing (octadWord D) d = μ D := by
  obtain ⟨a,b,hab,hμ⟩ := octad_residual_sign_extension i j hij μ ε hadd hzero hboth
  refine ⟨a • coordinateCocode i + b • coordinateCocode j, ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, coordinateCocode_parity, coordinateCocode_parity]
    simpa only [smul_eq_mul, mul_one] using hab
  · intro D
    rw [hμ D]
    change cocodeDualEquiv (a • coordinateCocode i + b • coordinateCocode j) (octadWord D) = _
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    change a * cocodePairing (octadWord D) (coordinateCocode i) +
      b * cocodePairing (octadWord D) (coordinateCocode j) = _
    rw [cocodePairing_coordinate, cocodePairing_coordinate, octadWord_apply]
    rw [octadWord_apply]

end Atlas.Fischer
