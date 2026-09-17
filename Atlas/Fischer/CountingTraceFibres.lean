import Atlas.Fischer.CountingMaskNormalization
import Mathlib.Logic.Equiv.Basic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Each absolute trace value has two preimages in F4, also after nonzero rescaling. -/
theorem countingFieldTrace_fiber_card (g : CountingFour) (hg : g ≠ 0) (v : Bit) :
    Nat.card {z : CountingFour // countingFieldTrace (z/g)=v}=2 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp only [countingFour_div]
  revert g v
  decide

/-- Every prescribed triple of trace coordinates occurs for exactly eight codewords. -/
theorem countingHex_three_trace_fiber_card (g : countingHexacode)
    (e : Fin 3 ↪ Fin 6) (hg : ∀ j, g.val (e j) ≠ 0) (v : Fin 3 → Bit) :
    Nat.card {b : countingHexacode // ∀ j, countingFieldTrace (b.val (e j)/g.val (e j))=v j}=8 := by
  let f : {b : countingHexacode // ∀ j, countingFieldTrace (b.val (e j)/g.val (e j))=v j} ≃
      {x : Fin 3 → CountingFour // ∀ j, countingFieldTrace (x j/g.val (e j))=v j} :=
    Equiv.subtypeEquiv (countingHexTripleEquiv e).toEquiv (fun _ => Iff.rfl)
  rw [Nat.card_congr f,Nat.card_congr (Equiv.subtypePiEquivPi
    (β := fun _ : Fin 3 => CountingFour)
    (p := fun j z => countingFieldTrace (z/g.val (e j))=v j)),Nat.card_pi]
  simp only [countingFieldTrace_fiber_card _ (hg _)]
  decide

end Atlas.Fischer
