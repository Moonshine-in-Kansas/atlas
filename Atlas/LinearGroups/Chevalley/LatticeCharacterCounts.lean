import Atlas.GroupTheory.CyclicCharacters
import Atlas.LinearGroups.Chevalley.Integral.MinusculeAQuotient
import Atlas.LinearGroups.Chevalley.Integral.MinusculeBQuotient
import Atlas.LinearGroups.Chevalley.Integral.MinusculeCQuotient
import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Quotient
import Atlas.LinearGroups.Chevalley.Integral.E7Minuscule.Quotient
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDEvenCharacter
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDOddCharacter

/-! Actual-lattice character counts. No finite-group center claim. -/
namespace Atlas.Chevalley
open Integral Minuscule
variable (K : Type*) [Field K] [Fintype K]

theorem typeA_weightRootCharacters_card (r : ℕ) :
    Nat.card (Multiplicative
      (WeightLattice (TypeAData.pairing (r+1)) ⧸ rootLattice (TypeAData.pairing (r+1)))
        →* Kˣ) = Nat.gcd (r+1) (Fintype.card K - 1) :=
  Atlas.GroupTheory.characters_card_of_addEquiv_zmod (r+1)
    (TypeA.weightRootQuotientEquiv r).toAddEquiv K

theorem typeB_weightRootCharacters_card (n : ℕ) :
    Nat.card (Multiplicative
      (WeightLattice (ClassicalData.pairingB (n+1)) ⧸
        rootLattice (ClassicalData.pairingB (n+1))) →* Kˣ) =
      Nat.gcd 2 (Fintype.card K - 1) :=
  Atlas.GroupTheory.characters_card_of_addEquiv_zmod 2
    (TypeB.weightRootQuotientEquiv n).toAddEquiv K

theorem typeC_weightRootCharacters_card (n : ℕ) :
    Nat.card (Multiplicative
      (WeightLattice (ClassicalData.pairingC (n+1)) ⧸
        rootLattice (ClassicalData.pairingC (n+1))) →* Kˣ) =
      Nat.gcd 2 (Fintype.card K - 1) :=
  Atlas.GroupTheory.characters_card_of_addEquiv_zmod 2
    (TypeC.weightRootQuotientEquiv n).toAddEquiv K

theorem E6_weightRootCharacters_card :
    Nat.card (Multiplicative (E6Minuscule.Weight ⧸ rootLattice E6Data.pairing) →* Kˣ) =
      Nat.gcd 3 (Fintype.card K - 1) :=
  Atlas.GroupTheory.characters_card_of_addEquiv_zmod 3
    E6Minuscule.weightRootQuotientEquiv.toAddEquiv K

theorem E7_weightRootCharacters_card :
    Nat.card (Multiplicative (E7Minuscule.Weight ⧸ rootLattice E7Data.pairing) →* Kˣ) =
      Nat.gcd 2 (Fintype.card K - 1) :=
  Atlas.GroupTheory.characters_card_of_addEquiv_zmod 2
    E7Minuscule.weightRootQuotientEquiv.toAddEquiv K

theorem typeD_odd_weightRootCharacters_card (n : ℕ) (hn : Odd (n+2)) :
    Nat.card (Multiplicative (TypeD.WeightRootQuotient n) →* Kˣ) =
      Nat.gcd 4 (Fintype.card K - 1) :=
  Atlas.GroupTheory.characters_card_of_addEquiv_zmod 4
    (TypeD.oddWeightRootEquiv n hn) K

theorem typeD_even_weightRootCharacters_card (n : ℕ) (hn : Even (n+2)) :
    Nat.card (Multiplicative (TypeD.WeightRootQuotient n) →* Kˣ) =
      Nat.gcd 2 (Fintype.card K - 1) ^ 2 := by
  simpa only [pow_two] using Atlas.GroupTheory.characters_card_of_addEquiv_zmod_prod 2 2
    (TypeD.evenWeightRootEquiv n hn) K

end Atlas.Chevalley
