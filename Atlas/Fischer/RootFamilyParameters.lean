import Atlas.Fischer.DuadCharacterProducts
import Atlas.Fischer.OctadicReflectingRoots
import Atlas.Fischer.OctadicRootFibres
import Atlas.Fischer.RootRays
import Mathlib.Data.Finset.Powerset

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev RootDuad := {p : Finset Omega // p.card = 2}
abbrev OctadicRootParameter := Σ O : Octad, OctadicCharacter O
abbrev DuadicRootParameter := Σ p : RootDuad, Module.Dual Bit (duadShortenedCode p.val)

instance octadicRootCharacters_finite (O : Octad) : Finite (OctadicCharacter O) :=
  Nat.finite_of_card_ne_zero (by rw [octadCharacters_card]; decide)

instance duadicRootCharacters_finite (p : RootDuad) :
    Finite (Module.Dual Bit (duadShortenedCode p.val)) :=
  Nat.finite_of_card_ne_zero (by rw [duadCharacters_card p.val p.property]; decide)

/-- A disjoint parameter type, not an assertion that its images are distinct rays. -/
abbrev ReflectingRootParameter := Omega ⊕ (OctadicRootParameter ⊕ DuadicRootParameter)

/-- Fix only the retained octad pair and calibrations in the existing product model. -/
def chosenDuadicRoot (p : RootDuad) (ξ : Module.Dual Bit (duadShortenedCode p.val)) : Coordinates :=
  duadCharacterProduct p.val p.property
    (duadChosenOctadPair p.val p.property).1 (duadChosenOctadPair p.val p.property).2
    (duadChosenOctadPair_intersection p.val p.property)
    (chosenOctadCalibration _) (chosenOctadCalibration _) ξ

def reflectingRootParameterVector : ReflectingRootParameter → Coordinates
  | .inl i => basicAxis i
  | .inr (.inl t) => octadicRoot (chosenOctadCalibration t.1) t.2
  | .inr (.inr t) => chosenDuadicRoot t.1 t.2

def reflectingRootParameterRay (t : ReflectingRootParameter) : Finset Coordinates :=
  rootRay (reflectingRootParameterVector t)

theorem reflectingRootParameter_isReflectingRoot (t : ReflectingRootParameter) :
    IsReflectingRoot (reflectingRootParameterVector t) := by
  rcases t with i | (t | t)
  · exact basicAxis_isReflectingRoot i
  · exact octadicRoot_isReflectingRoot _ _
  · exact duadCharacterProduct_isReflectingRoot _ _ _ _ _ _ _ _

theorem reflectingRootParameterRay_card (t : ReflectingRootParameter) :
    (reflectingRootParameterRay t).card = 3 :=
  rootRay_card _ (reflectingRootParameter_isReflectingRoot t).1

theorem basicRootParameter_card : Nat.card Omega = 24 := by
  norm_num [Omega, HexIndex, Nat.card_eq_fintype_card]

theorem rootDuad_card : Nat.card RootDuad = 276 := by
  let e : RootDuad ≃ {p : Finset Omega // p ∈ Finset.univ.powersetCard 2} :=
    Equiv.subtypeEquivRight (fun p => by simp)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard]
  norm_num [Omega, HexIndex, Nat.choose_two_right]

theorem octadicRootParameter_card : Nat.card OctadicRootParameter = 24288 := by
  letI : ∀ O : Octad, Fintype (OctadicCharacter O) := fun _ => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have h (O : Octad) : Fintype.card (OctadicCharacter O) = 32 := by
    rw [← Nat.card_eq_fintype_card]; exact octadCharacters_card O
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  norm_num [Octad, octads_card]

theorem duadicRootParameter_card : Nat.card DuadicRootParameter = 282624 := by
  letI : Fintype RootDuad := Fintype.ofFinite _
  letI : ∀ p : RootDuad, Fintype (Module.Dual Bit (duadShortenedCode p.val)) :=
    fun _ => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have h (p : RootDuad) : Fintype.card (Module.Dual Bit (duadShortenedCode p.val)) = 1024 := by
    rw [← Nat.card_eq_fintype_card]; exact duadCharacters_card p.val p.property
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, rootDuad_card]

theorem reflectingRootParameter_card : Nat.card ReflectingRootParameter = 306936 := by
  rw [Nat.card_sum, Nat.card_sum, octadicRootParameter_card, duadicRootParameter_card]
  norm_num [Omega, HexIndex, Nat.card_eq_fintype_card]

end Atlas.Fischer
