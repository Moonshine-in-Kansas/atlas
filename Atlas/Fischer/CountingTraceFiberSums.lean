import Atlas.Fischer.CountingFullTraceFibres
import Atlas.Fischer.CountingMaskParameters

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Each even supported trace mask has eight preimages among the actual64
hexacode words. This is a sum identity for arbitrary weights, not only cardinalities. -/
theorem countingRatioMask_sum (g : countingHexacode) (hg : hammingNorm g.val=4)
    (f : P6 → ℕ) :
    (∑ b : countingHexacode, f (countingRatioMask b g))=
      ∑ v : {v : P6 // ∀ i, g.val i=0 → v.val i=0}, 8*f v.val := by
  let r (b : countingHexacode) : {v : P6 // ∀ i, g.val i=0 → v.val i=0} :=
    ⟨countingRatioMask b g,countingRatioMask_zero b g⟩
  have hc (v : {v : P6 // ∀ i, g.val i=0 → v.val i=0}) :
      Fintype.card {b : countingHexacode // r b=v}=8 := by
    have he : ∀ b, r b=v ↔ countingRatioMask b g=v.val := by
      intro b
      exact Subtype.ext_iff
    rw [← Nat.card_eq_fintype_card,Nat.card_congr (Equiv.subtypeEquivRight he)]
    exact countingRatioMask_fiber_card g hg v.val v.property
  change (∑ b : countingHexacode, (fun v => f v.val) (r b))=_
  rw [← Fintype.sum_fiberwise' r (fun v => f v.val)]
  apply Finset.sum_congr rfl
  intro v _
  simp [hc]

end Atlas.Fischer
