import Atlas.Fischer.CountingTypeBTable
import Atlas.Fischer.CountingSupportFibres

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The finite mask space used by the column tables is exactly the retained
parity-code mask space supported on the chosen four columns. -/
def countingSupportedMaskEquiv (h : countingHexacode) :
    {e : P6 // ∀ i, h.val i=0 → e.val i=0} ≃
      {m : Fin 5 → Bit // countingTableMaskSupported (countingHexSupport h) m} :=
  ((parityEquiv 5).symm.toEquiv.subtypeEquiv (by
    intro e
    simp only [countingTableMaskSupported,countingHexSupport,Finset.mem_filter,
      Finset.mem_univ,true_and,not_not,countingTableMask]
    have he : parityEncoder 5 ((parityEquiv 5).symm e)=e.val :=
      congrArg Subtype.val ((parityEquiv 5).apply_symm_apply e)
    change (∀ i, h.val i=0 → e.val i=0) ↔
      ∀ i, h.val i=0 → (parityEncoder 5 ((parityEquiv 5).symm e) i).val=0
    rw [he]
    simp only [ZMod.val_eq_zero]))

theorem countingSupportedMaskEquiv_apply (h : countingHexacode)
    (e : {e : P6 // ∀ i, h.val i=0 → e.val i=0}) (i : Fin 6) :
    countingTableMask (countingSupportedMaskEquiv h e).val i=(e.val.val i).val := by
  change (parityEncoder 5 ((parityEquiv 5).symm e.val) i).val=_
  have he := congrArg Subtype.val ((parityEquiv 5).apply_symm_apply e.val)
  exact congrArg (fun w : Fin 6 → Bit => (w i).val) he

/-- Actual Type B parameters, with the same word and an explicit five-bit even-mask encoding. -/
def countingSourceBMaskEquiv : CountingSourceTypeB ≃
    Σ h : {h : countingHexacode // hammingNorm h.val=4},
      {m : Fin 5 → Bit // countingTableMaskSupported (countingHexSupport h.val) m} :=
  Equiv.sigmaCongrRight (fun h => countingSupportedMaskEquiv h.val)

/-- Exact replacement of the actual supported-mask sum by the thirty-two
five-bit inputs, with the support condition retained as a finite filter. -/
theorem countingSupportedMask_sum (h : countingHexacode) (f : P6 → ℕ) :
    (∑ e : {e : P6 // ∀ i, h.val i=0 → e.val i=0}, f e.val)=
      ∑ m : Fin 5 → Bit, if countingTableMaskSupported (countingHexSupport h) m then
        f (parityEquiv 5 m) else 0 := by
  let e := countingSupportedMaskEquiv h
  calc
    _ = ∑ v : {v : P6 // ∀ i, h.val i=0 → v.val i=0},
        f (parityEquiv 5 (e v).val) := by
      apply Finset.sum_congr rfl
      intro v _
      exact congrArg f ((parityEquiv 5).apply_symm_apply v.val).symm
    _ = ∑ m : {m : Fin 5 → Bit // countingTableMaskSupported (countingHexSupport h) m},
        f (parityEquiv 5 m.val) := Equiv.sum_comp e (fun m => f (parityEquiv 5 m.val))
    _ = ∑ m ∈ Finset.univ.filter (countingTableMaskSupported (countingHexSupport h)),
        f (parityEquiv 5 m) := (Finset.sum_subtype (p := countingTableMaskSupported (countingHexSupport h))
          _ (by intro m; simp) (fun m => f (parityEquiv 5 m))).symm
    _ = _ := Finset.sum_filter _ _

end Atlas.Fischer

