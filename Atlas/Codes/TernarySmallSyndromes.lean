import Atlas.Codes.TernarySyndromeSupports
import Atlas.Codes.TernaryGolayTriads

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

instance : Finite TernaryAffineSyndrome := Nat.finite_of_card_ne_zero (by rw [ternaryAffineSyndrome_card]; decide)
instance : Fintype TernaryAffineSyndrome := Fintype.ofFinite _

def ternarySingletonSyndrome (i : Fin 12) : TernaryAffineSyndrome :=
  ⟨ternarySyndromeClass (Pi.single i 1), by simp [ternaryWordSum]⟩

theorem ternarySupport_singleton (i : Fin 12) :
    ternarySupport (Pi.single i 1) = {i} := by
  ext j
  simp [ternarySupport, Pi.single_apply]

theorem ternarySingletonSyndrome_injective : Function.Injective ternarySingletonSyndrome := by
  intro i j h
  have hw := ternarySyndrome_small_support (Pi.single i 1) (Pi.single j 1)
    (by rw [ternarySupport_singleton, ternarySupport_singleton]; simp)
    (congrArg Subtype.val h)
  have hs := congrArg ternarySupport hw
  simpa only [ternarySupport_singleton, Finset.singleton_inj] using hs

def ternarySingletonSyndromes : Finset TernaryAffineSyndrome :=
  Finset.univ.image ternarySingletonSyndrome

theorem ternarySingletonSyndromes_card : ternarySingletonSyndromes.card = 12 := by
  rw [ternarySingletonSyndromes, Finset.card_image_of_injective _ ternarySingletonSyndrome_injective]
  simp

def ternaryPairs : Finset (Finset (Fin 12)) := Finset.univ.powersetCard 2

abbrev TernaryPair := ↥ternaryPairs

theorem ternaryPairs_card : ternaryPairs.card = 66 := by
  rw [ternaryPairs, Finset.card_powersetCard]
  decide

def ternaryPairWord (s : Finset (Fin 12)) : TernaryWord := -ternaryTriadWord s

theorem ternaryPairWord_support (s : Finset (Fin 12)) :
    ternarySupport (ternaryPairWord s) = s := by
  ext i
  simp [ternaryPairWord, ternaryTriadWord, ternarySupport]

def ternaryPairSyndrome (s : TernaryPair) : TernaryAffineSyndrome :=
  ⟨ternarySyndromeClass (ternaryPairWord s.val), by
    have hs := (Finset.mem_powersetCard.mp s.property).2
    simp [ternaryWordSum, ternaryPairWord, ternaryTriadWord, hs]
    decide⟩

theorem ternaryPairSyndrome_injective : Function.Injective ternaryPairSyndrome := by
  intro s t h
  have hs := (Finset.mem_powersetCard.mp s.property).2
  have ht := (Finset.mem_powersetCard.mp t.property).2
  have hw := ternarySyndrome_small_support (ternaryPairWord s.val) (ternaryPairWord t.val)
    (by rw [ternaryPairWord_support, ternaryPairWord_support, hs, ht]; decide)
    (congrArg Subtype.val h)
  apply Subtype.ext
  simpa only [ternaryPairWord_support] using congrArg ternarySupport hw

def ternaryPairSyndromes : Finset TernaryAffineSyndrome := Finset.univ.image ternaryPairSyndrome

theorem ternaryPairSyndromes_card : ternaryPairSyndromes.card = 66 := by
  rw [ternaryPairSyndromes, Finset.card_image_of_injective _ ternaryPairSyndrome_injective]
  simpa using ternaryPairs_card

theorem ternarySmallSyndromes_disjoint : Disjoint ternarySingletonSyndromes ternaryPairSyndromes := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hd
  have hsc := (Finset.mem_powersetCard.mp s.property).2
  have hw := ternarySyndrome_small_support (ternaryPairWord s.val) (Pi.single i 1)
    (by rw [ternaryPairWord_support, hsc, ternarySupport_singleton]; simp)
    (congrArg Subtype.val hs)
  have hh := congrArg (fun w => (ternarySupport w).card) hw
  rw [ternaryPairWord_support, hsc, ternarySupport_singleton] at hh
  simpa using hh

end Atlas.Codes
