import Atlas.Fischer.OctadicParityClasses
import Atlas.Fischer.CommutingFrameConjugacy

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

abbrev OctadicParityFrameParameter (O : Octad) (e : Bit) :=
  {i : Omega // i ∈ O.val} ⊕ OctadicParityClass O e

def octadicParityFrameParameter (O : Octad) (e : Bit) :
    OctadicParityFrameParameter O e → ReflectingRootParameter
  | .inl i => .inl i.val
  | .inr χ => .inr (.inl ⟨O,χ.val⟩)

theorem octadicParityFrameParameter_injective (O : Octad) (e : Bit) :
    Function.Injective (octadicParityFrameParameter O e) := by
  rintro (i | χ) (j | ψ) h
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
  · cases h
  · cases h
  · apply congrArg Sum.inr
    apply Subtype.ext
    exact Sigma.mk.inj_iff.mp (Sum.inl.inj (Sum.inr.inj h)) |>.2 |> eq_of_heq

/-- The actual eight basic and sixteen octadic involutions of one switched frame. -/
def octadicParityFrame (O : Octad) (e : Bit) : Set rootGeneratedRayGroup :=
  Set.range (fun t : OctadicParityFrameParameter O e =>
    distinguishedRootElement (octadicParityFrameParameter O e t))

theorem octadicParityFrame_card (O : Octad) (e : Bit) :
    Nat.card (octadicParityFrame O e)=24 := by
  have hi := distinguishedRootElement_injective.comp (octadicParityFrameParameter_injective O e)
  change Nat.card (Set.range (distinguishedRootElement ∘ octadicParityFrameParameter O e))=24
  rw [← Nat.card_congr (Equiv.ofInjective _ hi),Nat.card_sum,octadicParityClass_card]
  have hc : Nat.card {i : Omega // i ∈ O.val}=8 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,octad_size O.val O.prop]
  rw [hc]

theorem mem_octadicParityFrame_basic (O : Octad) (e : Bit) (i : Omega) :
    distinguishedRootElement (.inl i) ∈ octadicParityFrame O e ↔ i ∈ O.val := by
  constructor
  · rintro ⟨j | χ,h⟩
    · have hi := Sum.inl.inj (distinguishedRootElement_injective h)
      exact hi ▸ j.prop
    · have h' := distinguishedRootElement_injective h
      cases h'
  · intro hi
    exact ⟨.inl ⟨i,hi⟩,rfl⟩

theorem mem_octadicParityFrame_octadic (O : Octad) (e : Bit) (χ : OctadicCharacter O) :
    distinguishedRootElement (.inr (.inl ⟨O,χ⟩)) ∈ octadicParityFrame O e ↔
      χ (octadShortenedOne O)=e := by
  constructor
  · rintro ⟨i | ψ,h⟩
    · have h' := distinguishedRootElement_injective h
      cases h'
    · have h' : ψ.val=χ := eq_of_heq
        (Sigma.mk.inj_iff.mp (Sum.inl.inj (Sum.inr.inj (distinguishedRootElement_injective h)))).2
      exact h' ▸ ψ.prop
  · intro hχ
    exact ⟨.inr ⟨χ,hχ⟩,rfl⟩

end Atlas.Fischer
