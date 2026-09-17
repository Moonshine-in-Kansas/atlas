import Atlas.Fischer.OctadAffineEvaluations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Restrict the actual Golay cocode character to the actual octad-shortened code. -/
def octadCocodeRestriction (O : Octad) :
    Cocode →ₗ[Bit] Module.Dual Bit (octadShortenedCode O) :=
  (octadShortenedCode O).subtype.dualMap.comp cocodeDualEquiv.toLinearMap

@[simp] theorem octadCocodeRestriction_apply (O : Octad) (d : Cocode)
    (c : octadShortenedCode O) : octadCocodeRestriction O d c = cocodePairing c.val d := rfl

theorem octadCocodeRestriction_surjective (O : Octad) :
    Function.Surjective (octadCocodeRestriction O) :=
  (LinearMap.dualMap_surjective_of_injective (octadShortenedCode O).injective_subtype).comp
    cocodeDualEquiv.surjective

/-- The annihilator N_O in the actual cocode. -/
def octadCocodeAnnihilator (O : Octad) : Submodule Bit Cocode :=
  (octadCocodeRestriction O).ker

theorem mem_octadCocodeAnnihilator (O : Octad) (d : Cocode) :
    d ∈ octadCocodeAnnihilator O ↔
      ∀ c : octadShortenedCode O, cocodePairing c.val d = 0 := by
  change octadCocodeRestriction O d = 0 ↔ _
  exact LinearMap.ext_iff

theorem octadCocodeAnnihilator_finrank (O : Octad) :
    Module.finrank Bit (octadCocodeAnnihilator O) = 7 := by
  have h := (octadCocodeRestriction O).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (octadCocodeRestriction_surjective O),finrank_top,
    Subspace.dual_finrank_eq,octadShortenedCode_finrank,cocode_finrank] at h
  change Module.finrank Bit (octadCocodeRestriction O).ker = 7
  omega

theorem octadCocodeAnnihilator_card (O : Octad) :
    Nat.card (octadCocodeAnnihilator O) = 128 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit),octadCocodeAnnihilator_finrank]
  simp [Bit]

theorem octadCharacters_card (O : Octad) :
    Nat.card (Module.Dual Bit (octadShortenedCode O)) = 32 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit),Subspace.dual_finrank_eq,
    octadShortenedCode_finrank]
  simp [Bit]

/-- The sixteen evaluation characters are exactly those nontrivial on X. -/
theorem octadEvaluation_range (O : Octad) (l : Module.Dual Bit (octadShortenedCode O)) :
    (∃ i : OctadExterior O, octadEvaluation O i = l) ↔ l (octadShortenedOne O) = 1 := by
  constructor
  · rintro ⟨i,rfl⟩
    exact octadEvaluation_one O i
  · intro h
    obtain ⟨i,hi⟩ := (octadAffineEvaluation_bijective O).surjective ⟨l,h⟩
    exact ⟨i,congrArg Subtype.val hi⟩

end Atlas.Fischer
