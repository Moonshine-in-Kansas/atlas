import Atlas.Fischer.MarkedPentadFrames

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The standard frame and its two actual switched companions. -/
def markedPentadFrameChoice (S : Finset Omega) (hS : S.card=5) :
    Unit ⊕ Bit → MarkedPentadFrame S
  | .inl _ => ⟨standardCommutingFrame,standardCommutingFrame_isFrame,
      fun i _ => ⟨i,rfl⟩⟩
  | .inr e => ⟨octadicParityFrame (markedPentadOctad S hS) e,
      octadicParityFrame_isFrame _ _,fun i hi =>
        (mem_octadicParityFrame_basic _ _ i).mpr (markedPentadOctad_contains S hS hi)⟩

theorem standard_ne_octadicParityFrame (O : Octad) (e : Bit) :
    standardCommutingFrame ≠ octadicParityFrame O e := by
  intro h
  let i : OctadExterior O := Classical.arbitrary _
  have hi : distinguishedRootElement (.inl i.val) ∈ standardCommutingFrame := ⟨i.val,rfl⟩
  rw [h,mem_octadicParityFrame_basic] at hi
  exact i.prop hi

theorem octadicParityFrame_injective (O : Octad) : Function.Injective (octadicParityFrame O) := by
  intro e f h
  obtain ⟨χ⟩ := octadicParityClass_nonempty O e
  have hχ := (mem_octadicParityFrame_octadic O e χ.val).mpr χ.prop
  rw [h,mem_octadicParityFrame_octadic] at hχ
  exact χ.prop.symm.trans hχ

theorem markedPentadFrameChoice_bijective (S : Finset Omega) (hS : S.card=5) :
    Function.Bijective (markedPentadFrameChoice S hS) := by
  constructor
  · rintro (u | e) (v | f) h
    · cases u; cases v; rfl
    · exact (standard_ne_octadicParityFrame _ _ (congrArg Subtype.val h)).elim
    · exact (standard_ne_octadicParityFrame _ _ (congrArg Subtype.val h).symm).elim
    · exact congrArg Sum.inr (octadicParityFrame_injective _ (congrArg Subtype.val h))
  · intro F
    rcases markedPentadFrame_classification S hS F with h | ⟨e,h⟩
    · exact ⟨.inl (),Subtype.ext h.symm⟩
    · exact ⟨.inr e,Subtype.ext h.symm⟩

/-- Exactly three actual frames pass through a standard marked commuting pentad. -/
theorem markedPentadFrame_card (S : Finset Omega) (hS : S.card=5) :
    Nat.card (MarkedPentadFrame S)=3 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (markedPentadFrameChoice_bijective S hS)),Nat.card_sum]
  norm_num [Bit]

end Atlas.Fischer
