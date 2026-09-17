import Atlas.Fischer.DuadPureSummandCoordinates
import Atlas.Fischer.DuadCharacterProducts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Pure shortened-code coordinates recover the second actual character. -/
theorem duadOctadicProduct_right_character {F G : Octad}
    (hFG : (F.val ∩ G.val).card = 2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ χ' : OctadicCharacter F) (ψ ψ' : OctadicCharacter G)
    (he : duadOctadicProduct Q R χ ψ = duadOctadicProduct Q R χ' ψ') : ψ = ψ' := by
  apply LinearMap.ext
  intro b
  by_cases hb : b = 0
  · simp [hb]
  obtain ⟨p, hp, hn⟩ := duadPureSummand_coordinate_exists hFG Q R b hb
  have hp' : rationalCoordinateGolayWord p = (0 : octadShortenedCode F).val + b.val := by
    simpa only [ZeroMemClass.coe_zero, zero_add] using hp
  have h := congrArg (fun x => rationalCoordinateEquiv x p) he
  change rationalCoordinateEquiv (product (octadicRoot Q χ) (octadicRoot R ψ)) p =
    rationalCoordinateEquiv (product (octadicRoot Q χ') (octadicRoot R ψ')) p at h
  rw [duadWordPair_coordinate_isolation hFG Q R χ ψ 0 b p hp',
    duadWordPair_coordinate_isolation hFG Q R χ' ψ' 0 b p hp'] at h
  have hs := mul_right_cancel₀ hn h
  simp only [map_zero, rationalBitSign, ite_true, mul_one] at hs
  apply rationalBitSign_injective
  change (if ψ b = 0 then (1 : ℚ) else -1) = (if ψ' b = 0 then (1 : ℚ) else -1)
  linarith

/-- The 32 by 32 actual product roots have distinct character parameters. -/
theorem duadOctadicProduct_injective {F G : Octad}
    (hFG : (F.val ∩ G.val).card = 2) (Q : OctadCalibration F) (R : OctadCalibration G) :
    Function.Injective (fun v : OctadicCharacter F × OctadicCharacter G =>
      duadOctadicProduct Q R v.1 v.2) := by
  intro v w he
  apply Prod.ext
  · have hGF : (G.val ∩ F.val).card = 2 := by simpa only [Finset.inter_comm] using hFG
    apply duadOctadicProduct_right_character hGF R Q v.2 w.2 v.1 w.1
    simpa only [duadOctadicProduct, product_comm] using he
  · exact duadOctadicProduct_right_character hFG Q R v.1 w.1 v.2 w.2 he

/-- The actual C_p-dual parametrization is injective for every chosen octad pair
and every pair of calibrated Parker sections. -/
theorem duadCharacterProduct_injective (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    Function.Injective (duadCharacterProduct p hp F G hFG Q R) := by
  intro ξ μ he
  apply (duadCharacterEquiv p hp F G hFG).symm.injective
  exact duadOctadicProduct_injective (hFG ▸ hp) Q R he

end Atlas.Fischer
