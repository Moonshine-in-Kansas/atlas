import Atlas.Algebra.GoldenFourFinite
import Atlas.Codes.HexacodeSystematic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- The existing quadratic field of four elements; no new finite field is assumed. -/
abbrev CountingFour := GoldenFour
abbrev CountingHexWord := Fin 6 → CountingFour

def countingLetterEquiv : K ≃ₗ[Bit] CountingFour where
  toFun u := ⟨u.1,u.2⟩
  invFun z := (z.re,z.im)
  left_inv u := rfl
  right_inv z := rfl
  map_add' u v := rfl
  map_smul' a u := rfl

theorem countingLetter_kappa (u : K) :
    countingLetterEquiv (localKappa u)=goldenFourTau*countingLetterEquiv u := by
  revert u
  decide

theorem countingLetter_kappa_inv (u : K) :
    countingLetterEquiv (localKappa⁻¹ u)=goldenFourTau^2*countingLetterEquiv u := by
  have h : ∀ u : K, localKappa⁻¹ u=localKappa (localKappa u) := by decide
  rw [h,countingLetter_kappa,countingLetter_kappa,pow_two,mul_assoc]

/-- Literal source equation hexacode-for-count, now an actual F4-linear map. -/
def countingHexEncoder : (Fin 3 → CountingFour) →ₗ[CountingFour] CountingHexWord where
  toFun x := ![x 0,x 1,x 2,x 0+x 1+x 2,
    x 0+goldenFourTau*x 1+goldenFourTau^2*x 2,
    x 0+goldenFourTau^2*x 1+goldenFourTau*x 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

def countingHexacode : Submodule CountingFour CountingHexWord := countingHexEncoder.range

theorem countingHexEncoder_injective : Function.Injective countingHexEncoder := by
  intro x y h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2

end Atlas.Fischer
