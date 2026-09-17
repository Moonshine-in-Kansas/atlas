import Atlas.Fischer.CountingHexacodeComparison
import Atlas.Codes.GolayEvenCounting

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem countingHexCoordinates_weight (w : HexWord) :
    hammingNorm (countingHexCoordinates w)=hammingNorm w := by
  have hz (i : Fin 6) : countingHexCoordinates w i=0 ↔ w (hexPos i)=0 := by
    change countingLetterEquiv (countingHexLocal i (w (hexPos i)))=0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff,LinearEquiv.map_eq_zero_iff]
  have he : hammingNorm (countingHexCoordinates w)=hammingNorm (fun i : Fin 6 => w (hexPos i)) := by
    rw [hammingNorm_eq_sum,hammingNorm_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hz]
  exact he.trans (hammingNorm_equiv hexIndexEquiv.symm w)

theorem countingHexacode_card : Nat.card countingHexacode=64 := by
  rw [← Nat.card_congr countingHexEquiv,hexacode_card]

theorem countingHexacode_weight_distribution (k : ℕ) :
    Nat.card {h : countingHexacode // hammingNorm h.val=k}=
      if k=0 then 1 else if k=4 then 45 else if k=6 then 18 else 0 := by
  let e : {h : hexacode // hammingNorm h.val=k} ≃
      {h : countingHexacode // hammingNorm h.val=k} :=
    Equiv.subtypeEquiv countingHexEquiv (by
      intro h
      change hammingNorm h.val=k ↔ hammingNorm (countingHexCoordinates h.val)=k
      rw [countingHexCoordinates_weight])
  rw [← Nat.card_congr e]
  have h := hexacode_weight_distribution k
  simpa [Nat.card_eq_fintype_card,Fintype.card_subtype,hexWeightCount] using h

end Atlas.Fischer
