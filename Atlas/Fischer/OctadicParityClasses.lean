import Atlas.Fischer.OctadicPhasePairings
import Atlas.Fischer.RootFamilyParameters

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The two actual character classes, cut out by evaluation on X. -/
abbrev OctadicParityClass (O : Octad) (e : Bit) :=
  {χ : OctadicCharacter O // χ (octadShortenedOne O)=e}

theorem octadicParityClass_card (O : Octad) (e : Bit) :
    Nat.card (OctadicParityClass O e)=16 := by
  have h := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective
    (f := (octadDualConstant O).toAddMonoidHom) (octadDualConstant_surjective O) e)
  change Nat.card (OctadicParityClass O e)=Nat.card (octadDualConstant O).ker at h
  rw [h,Module.natCard_eq_pow_finrank (K := Bit),octadDualConstant_kernel_finrank]
  simp [Bit]

theorem octadicParityClass_nonempty (O : Octad) (e : Bit) :
    Nonempty (OctadicParityClass O e) := by
  obtain ⟨χ,hχ⟩ := octadDualConstant_surjective O e
  exact ⟨χ,hχ⟩

theorem octadicRoot_pairing_ne_zero_iff {O : Octad} (Q : OctadCalibration O)
    (χ ψ : OctadicCharacter O) :
    hermitian (octadicRoot Q χ) (octadicRoot Q ψ)≠0 ↔
      χ (octadShortenedOne O)=ψ (octadShortenedOne O) := by
  rw [octadicRoot_pairing]
  by_cases h : χ=ψ
  · subst ψ; simp
  · simp only [h,ite_false]
    split_ifs <;> simp_all

end Atlas.Fischer
