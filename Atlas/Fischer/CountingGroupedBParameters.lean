import Atlas.Fischer.CountingMaskParameters

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev CountingFourSupport := {T : Finset (Fin 6) // T.card=4}
abbrev CountingMaskOn (T : Finset (Fin 6)) := {e : P6 // ∀ i, i ∉ T → e.val i=0}
abbrev CountingWordOn (T : Finset (Fin 6)) := {h : countingHexacode // countingHexSupport h=T}

/-- Actual Type B parameters grouped by support, then mask, then the three
actual source-code words on that support. -/
abbrev CountingGroupedBParameters :=
  Σ T : CountingFourSupport, CountingMaskOn T.val × CountingWordOn T.val

def countingSourceBGroupedEquiv : CountingSourceTypeB ≃ CountingGroupedBParameters where
  toFun t := ⟨⟨countingHexSupport t.1.val,t.1.property⟩,
    (⟨t.2.val,by intro i hi; exact t.2.property i (by simpa [countingHexSupport] using hi)⟩,
      ⟨t.1.val,rfl⟩)⟩
  invFun t := ⟨⟨t.2.2.val,by
      rw [← countingHexSupport_card,t.2.2.property]
      exact t.1.property⟩,
    ⟨t.2.1.val,by
      intro i hi
      change t.2.2.val.val i=0 at hi
      apply t.2.1.property i
      rw [← t.2.2.property]
      simp [countingHexSupport,hi]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨h,hh⟩,⟨e,he⟩⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨T,hT⟩,⟨⟨e,he⟩,⟨h,hh⟩⟩⟩
    cases hh
    rfl

def countingSourceBGrouped (T : CountingFourSupport) (e : CountingMaskOn T.val)
    (h : CountingWordOn T.val) : CountingSourceTypeB :=
  countingSourceBGroupedEquiv.symm ⟨T,(e,h)⟩

/-- Exact source-parameter reindexing, valid for every target weight function. -/
theorem countingSourceBGrouped_sum (f : CountingSourceTypeB → ℕ) :
    (∑ t : CountingSourceTypeB, f t)=
      ∑ T : CountingFourSupport, ∑ e : CountingMaskOn T.val, ∑ h : CountingWordOn T.val,
        f (countingSourceBGrouped T e h) := by
  rw [← Equiv.sum_comp countingSourceBGroupedEquiv.symm f]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro T _
  exact Fintype.sum_prod_type _

/-- The literal finite mask filter is exactly the supported parity-code mask space. -/
def countingMaskOnEquiv (T : Finset (Fin 6)) :
    CountingMaskOn T ≃ {m : Fin 5 → Bit // countingTableMaskSupported T m} :=
  (parityEquiv 5).symm.toEquiv.subtypeEquiv (by
    intro e
    change (∀ i, i ∉ T → e.val i=0) ↔
      ∀ i, i ∉ T → (parityEncoder 5 ((parityEquiv 5).symm e) i).val=0
    have he : parityEncoder 5 ((parityEquiv 5).symm e)=e.val :=
      congrArg Subtype.val ((parityEquiv 5).apply_symm_apply e)
    rw [he]
    simp only [ZMod.val_eq_zero])

theorem countingMaskOn_sum (T : Finset (Fin 6)) (f : P6 → ℕ) :
    (∑ e : CountingMaskOn T, f e.val)=
      ∑ m : Fin 5 → Bit, if countingTableMaskSupported T m then f (parityEquiv 5 m) else 0 := by
  let e := countingMaskOnEquiv T
  calc
    _ = ∑ v : CountingMaskOn T, f (parityEquiv 5 (e v).val) := by
      apply Finset.sum_congr rfl
      intro v _
      exact congrArg f ((parityEquiv 5).apply_symm_apply v.val).symm
    _ = ∑ m : {m : Fin 5 → Bit // countingTableMaskSupported T m}, f (parityEquiv 5 m.val) :=
      Equiv.sum_comp e (fun m => f (parityEquiv 5 m.val))
    _ = ∑ m ∈ Finset.univ.filter (countingTableMaskSupported T), f (parityEquiv 5 m) :=
      (Finset.sum_subtype (p := countingTableMaskSupported T) _ (by intro m; simp)
        (fun m => f (parityEquiv 5 m))).symm
    _ = _ := Finset.sum_filter _ _

end Atlas.Fischer
