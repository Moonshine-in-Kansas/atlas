import Atlas.Fischer.CountingHexacodeField

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- Explicit local maps, with the six retained tetrads in their original order. -/
def countingHexLocal (i : Fin 6) : KIsometry := ![localU,1,localU,1,localW,localKappa] i

def countingHexCoordinates : HexWord ≃ₗ[Bit] CountingHexWord where
  toFun w i := countingLetterEquiv (countingHexLocal i (w (hexPos i)))
  invFun z p := (countingHexLocal (hexIndexEquiv p))⁻¹
    (countingLetterEquiv.symm (z (hexIndexEquiv p)))
  left_inv w := by
    funext p
    simp only [LinearEquiv.symm_apply_apply,hexPos_index]
    exact LinearEquiv.symm_apply_apply _ _
  right_inv z := by
    funext i
    simp only [index_hexPos]
    change countingLetterEquiv ((countingHexLocal i) ((countingHexLocal i).symm (countingLetterEquiv.symm (z i)))) = z i
    rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  map_add' u v := by funext i; simp only [Pi.add_apply,map_add]
  map_smul' a u := by funext i; simp only [Pi.smul_apply,map_smul,RingHom.id_apply]

/-- The finite local normalization is checked only on the three four-letter inputs. -/
theorem countingHex_systematic_normalization : ∀ x : Fin 3 → K,
    countingHexCoordinates (systematicEncoder x) = countingHexEncoder
      ![countingLetterEquiv (localU (x 0)),countingLetterEquiv (x 1),
        countingLetterEquiv (localU (x 2))] := by
  decide

/-- Exact ambient comparison with the original additive hexacode, not weight recognition. -/
theorem countingHexCoordinates_mem (w : HexWord) :
    w ∈ hexacode ↔ countingHexCoordinates w ∈ countingHexacode := by
  constructor
  · intro hw
    have he : systematicEncoder (hexProjection firstThree ⟨w,hw⟩)=w := systematic_reconstruct ⟨w,hw⟩
    rw [← he,countingHex_systematic_normalization]
    exact ⟨_,rfl⟩
  · rintro ⟨x,hx⟩
    let u : Fin 3 → K := ![localU (countingLetterEquiv.symm (x 0)),
      countingLetterEquiv.symm (x 1),localU (countingLetterEquiv.symm (x 2))]
    have hu : countingHexCoordinates (systematicEncoder u)=countingHexEncoder x := by
      rw [countingHex_systematic_normalization]
      congr 1
      funext i
      have hU : ∀ v : K, localU (localU v)=v := by decide
      fin_cases i
      · change countingLetterEquiv (localU (localU (countingLetterEquiv.symm (x 0))))=x 0
        rw [hU,LinearEquiv.apply_symm_apply]
      · exact LinearEquiv.apply_symm_apply countingLetterEquiv (x 1)
      · change countingLetterEquiv (localU (localU (countingLetterEquiv.symm (x 2))))=x 2
        rw [hU,LinearEquiv.apply_symm_apply]
    have he : systematicEncoder u=w := countingHexCoordinates.injective (hu.trans hx)
    rw [← he]
    exact systematic_mem u

/-- Every source codeword has a unique actual retained hexacode antecedent. -/
def countingHexEquiv : hexacode ≃ {w : CountingHexWord // w ∈ countingHexacode} :=
  Equiv.subtypeEquiv countingHexCoordinates.toEquiv countingHexCoordinates_mem

end Atlas.Fischer
