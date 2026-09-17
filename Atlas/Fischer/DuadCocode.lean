import Atlas.Fischer.DuadShortenedCode
import Atlas.Fischer.OctadCocode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Restrict the actual Golay cocode character to the actual duad-shortened code. -/
def duadCocodeRestriction (p : Finset Omega) :
    Cocode →ₗ[Bit] Module.Dual Bit (duadShortenedCode p) :=
  (duadShortenedCode p).subtype.dualMap.comp cocodeDualEquiv.toLinearMap

@[simp] theorem duadCocodeRestriction_apply (p : Finset Omega) (d : Cocode)
    (c : duadShortenedCode p) : duadCocodeRestriction p d c = cocodePairing c.val d := rfl

theorem duadCocodeRestriction_surjective (p : Finset Omega) :
    Function.Surjective (duadCocodeRestriction p) :=
  (LinearMap.dualMap_surjective_of_injective (duadShortenedCode p).injective_subtype).comp
    cocodeDualEquiv.surjective

/-- The annihilator ann(C_p) in the actual cocode. -/
def duadCocodeAnnihilator (p : Finset Omega) : Submodule Bit Cocode :=
  (duadCocodeRestriction p).ker

theorem mem_duadCocodeAnnihilator (p : Finset Omega) (d : Cocode) :
    d ∈ duadCocodeAnnihilator p ↔
      ∀ c : duadShortenedCode p, cocodePairing c.val d = 0 := by
  change duadCocodeRestriction p d = 0 ↔ _
  exact LinearMap.ext_iff

theorem duadCocodeAnnihilator_finrank (p : Finset Omega) (hp : p.card=2) :
    Module.finrank Bit (duadCocodeAnnihilator p) = 2 := by
  have h := (duadCocodeRestriction p).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (duadCocodeRestriction_surjective p),finrank_top,
    Subspace.dual_finrank_eq,duadShortenedCode_finrank p hp,cocode_finrank] at h
  change Module.finrank Bit (duadCocodeRestriction p).ker = 2
  omega

theorem duadCocodeAnnihilator_card (p : Finset Omega) (hp : p.card=2) :
    Nat.card (duadCocodeAnnihilator p) = 4 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit),duadCocodeAnnihilator_finrank p hp]
  simp [Bit]

theorem duadCharacters_card (p : Finset Omega) (hp : p.card=2) :
    Nat.card (Module.Dual Bit (duadShortenedCode p)) = 1024 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit),Subspace.dual_finrank_eq,
    duadShortenedCode_finrank p hp]
  simp [Bit]

/-- Translation of a duad character by the actual restricted cocode pairing. -/
def duadCocodeCharacterAction (p : Finset Omega) (d : Cocode)
    (χ : Module.Dual Bit (duadShortenedCode p)) : Module.Dual Bit (duadShortenedCode p) :=
  χ + duadCocodeRestriction p d

theorem duadCocodeCharacterAction_transitive (p : Finset Omega)
    (χ ψ : Module.Dual Bit (duadShortenedCode p)) :
    ∃ d : Cocode, duadCocodeCharacterAction p d χ=ψ := by
  obtain ⟨d,hd⟩ := duadCocodeRestriction_surjective p (ψ-χ)
  exact ⟨d,by simp [duadCocodeCharacterAction,hd]⟩

theorem duadCocodeCharacterAction_kernel (p : Finset Omega) (d : Cocode) :
    (∀ χ, duadCocodeCharacterAction p d χ=χ) ↔ d ∈ duadCocodeAnnihilator p := by
  constructor
  · intro h
    have hz := h 0
    simpa [duadCocodeCharacterAction,duadCocodeAnnihilator] using hz
  · intro h χ
    have hz : duadCocodeRestriction p d=0 := h
    simp [duadCocodeCharacterAction,hz]

end Atlas.Fischer

