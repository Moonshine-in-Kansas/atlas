import Atlas.Fischer.CountingHexacodeTrace
import Atlas.Fischer.CountingSourceParameters
import Atlas.Fischer.CountingPairIntersections

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- The actual even complement mask induced by a hexacode row translation. -/
def countingRatioMask (b g : countingHexacode) : P6 :=
  ⟨fun i => countingFieldTrace (b.val i/g.val i),
    (parityCode_mem 5 _).mpr (countingHexacode_ratio_trace_even b g)⟩

theorem countingRatioMask_zero (b g : countingHexacode) (i : Fin 6) (hi : g.val i=0) :
    (countingRatioMask b g).val i=0 := by simp [countingRatioMask,hi,countingFieldTrace]

/-- Every codeword translation preserves the full source Type B parameter space. -/
def countingSourceBTranslation (b : countingHexacode) : CountingSourceTypeB ≃ CountingSourceTypeB where
  toFun t := ⟨t.1,⟨t.2.val+countingRatioMask b t.1.val,by
    intro i hi
    change t.2.val.val i+(countingRatioMask b t.1.val).val i=0
    rw [t.2.property i hi,countingRatioMask_zero b _ i hi,add_zero]⟩⟩
  invFun t := ⟨t.1,⟨t.2.val+countingRatioMask b t.1.val,by
    intro i hi
    change t.2.val.val i+(countingRatioMask b t.1.val).val i=0
    rw [t.2.property i hi,countingRatioMask_zero b _ i hi,add_zero]⟩⟩
  left_inv t := by
    rcases t with ⟨h,v⟩
    apply congrArg (fun s : {e : P6 // ∀ i : Fin 6, h.val.val i=0 → e.val i=0} => (⟨h,s⟩ : CountingSourceTypeB))
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp [add_assoc]
  right_inv t := by
    rcases t with ⟨h,v⟩
    apply congrArg (fun s : {e : P6 // ∀ i : Fin 6, h.val.val i=0 → e.val i=0} => (⟨h,s⟩ : CountingSourceTypeB))
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp [add_assoc]

/-- The source Type C translation; its distinguished column is unchanged. -/
def countingSourceCTranslation (b : countingHexacode) : CountingSourceTypeC ≃ CountingSourceTypeC :=
  Equiv.prodCongr (Equiv.addRight b) (Equiv.refl (Fin 6))

/-- Normalizing a Type C source to zero uses its own actual codeword. -/
theorem countingSourceCTranslation_normalizes (b : countingHexacode) (j : Fin 6) :
    countingSourceCTranslation (-b) (b,j)=(0,j) := by
  simp [countingSourceCTranslation]

end Atlas.Fischer
