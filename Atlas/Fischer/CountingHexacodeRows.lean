import Atlas.Fischer.CountingHexacodeComparison
import Atlas.Codes.GolayOddCounting

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

def countingRowLetter : Fin 4 ≃ K where
  toFun k := ![0,a,b,c] k
  invFun u := if u=0 then 0 else if u=a then 1 else if u=b then 2 else 3
  left_inv := by decide
  right_inv := by decide

/-- Actual coordinate labels in the source's F4 normalization, preserving tetrads. -/
def countingPointCoordinates : Omega ≃ Fin 6 × CountingFour where
  toFun p := (hexIndexEquiv p.1,
    countingLetterEquiv (countingHexLocal (hexIndexEquiv p.1) (countingRowLetter p.2)))
  invFun p := (hexPos p.1,countingRowLetter.symm
    ((countingHexLocal p.1)⁻¹ (countingLetterEquiv.symm p.2)))
  left_inv p := by
    apply Prod.ext
    · exact hexPos_index p.1
    · change countingRowLetter.symm ((countingHexLocal (hexIndexEquiv p.1)).symm
        (countingLetterEquiv.symm (countingLetterEquiv
          (countingHexLocal (hexIndexEquiv p.1) (countingRowLetter p.2))))) = p.2
      rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply,Equiv.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · exact index_hexPos p.1
    · simp only [index_hexPos]
      change countingLetterEquiv ((countingHexLocal p.1) (countingRowLetter
        (countingRowLetter.symm ((countingHexLocal p.1).symm (countingLetterEquiv.symm p.2)))))=p.2
      rw [Equiv.apply_symm_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

/-- The even-column lift is the pair {0,u}, or its complement, with the exact sign correction. -/
theorem counting_even_column : ∀ (u : K) (r : Bit) (k : Fin 4), u ≠ 0 →
    j u k+r = if r+qK u=0 then
      (if countingRowLetter k=0 ∨ countingRowLetter k=u then 1 else 0)
    else (if countingRowLetter k=0 ∨ countingRowLetter k=u then 0 else 1) := by
  decide

/-- The odd-column lift selects the letter u, or its complement; eta's exceptional
column is retained in the distinguished-column mask. -/
theorem counting_odd_column : ∀ (i : HexIndex) (u : K) (r : Bit) (k : Fin 4),
    j u k+r+eta (i,k) = if r+qK u+(if hexIndexEquiv i=5 then 1 else 0)=0 then
      (if countingRowLetter k=u then 1 else 0)
    else (if countingRowLetter k=u then 0 else 1) := by
  decide

end Atlas.Fischer
