import Atlas.Fischer.CountingTraceFibres
import Atlas.Fischer.CountingEvenMasks
import Atlas.Fischer.CountingSupportFibres

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Every even four-bit trace pattern occurs for precisely eight actual source codewords. -/
theorem countingRatioMask_fiber_card (g : countingHexacode) (hg : hammingNorm g.val=4)
    (v : P6) (hv : ∀ i, g.val i=0 → v.val i=0) :
    Nat.card {b : countingHexacode // countingRatioMask b g=v}=8 := by
  have hS : Fintype.card (countingHexSupport g)=4 := by
    rw [Fintype.card_coe,countingHexSupport_card,hg]
  let f : Fin 4 ≃ ↥(countingHexSupport g) := (Fintype.equivFinOfCardEq hS).symm
  let e : Fin 4 ↪ Fin 6 := f.toEmbedding.trans (Function.Embedding.subtype _)
  let e3 : Fin 3 ↪ Fin 6 :=
    ⟨fun j => e ⟨j.val,by omega⟩,by
      intro j k h
      exact Fin.ext (congrArg (fun x : Fin 4 => x.val) (e.injective h))⟩
  have hzero (i : Fin 6) (hi : ∀ j, e j ≠ i) : g.val i=0 := by
    by_contra hn
    have hs : i ∈ countingHexSupport g := by simp [countingHexSupport,hn]
    obtain ⟨j,hj⟩ := f.surjective ⟨i,hs⟩
    exact hi j (congrArg Subtype.val hj)
  have hn : ∀ j, g.val (e3 j) ≠ 0 := by
    intro j
    exact (Finset.mem_filter.mp (f ⟨j.val,by omega⟩).property).2
  have he (b : countingHexacode) : countingRatioMask b g=v ↔
      ∀ j, countingFieldTrace (b.val (e3 j)/g.val (e3 j))=v.val (e3 j) := by
    constructor
    · intro hb j
      exact congrFun (congrArg Subtype.val hb) (e3 j)
    · intro hb
      exact countingEvenMasks_ext e (countingRatioMask b g) v
        (fun i hi => countingRatioMask_zero b g i (hzero i hi))
        (fun i hi => hv i (hzero i hi)) hb
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact countingHex_three_trace_fiber_card g e3 hn (fun j => v.val (e3 j))

end Atlas.Fischer
