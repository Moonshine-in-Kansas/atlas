import Atlas.LinearGroups.Chevalley.Integral.BoundedDiamond
import Atlas.LinearGroups.Chevalley.RootData.ClassicalPairingBounds
import Atlas.LinearGroups.Chevalley.RootData.F4PairingBounds
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC

/-! Actual B/C/F4 providers using proved coordinate bounds.
No target-group hypotheses are inserted. -/
noncomputable section
namespace Atlas.Chevalley
open Integral
open Classical

private theorem pairingIn_int_eq {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) [P.IsCrystallographic] (a b : ι) :
    P.pairingIn ℤ a b = P.pairing a b := by simpa using P.algebraMap_pairingIn ℤ a b

namespace ClassicalData

theorem boundedPairingsB (n : ℕ) : BoundedPairings (pairingB n) := by
  intro a b
  simpa only [pairingIn_int_eq] using pairingB_bounds n a b

theorem boundedPairingsC (n : ℕ) : BoundedPairings (pairingC n) := by
  intro a b
  simpa only [pairingIn_int_eq] using pairingC_bounds n a b

theorem simpleDiamondProductsB (n : ℕ) : SimpleDiamondProducts (pairingB (n+1)) (baseB n) :=
  simpleDiamondProducts_of_boundedPairings (pairingB (n+1)) (boundedPairingsB (n+1)) (baseB n)

theorem simpleDiamondProductsC (n : ℕ) : SimpleDiamondProducts (pairingC (n+1)) (baseC n) :=
  simpleDiamondProducts_of_boundedPairings (pairingC (n+1)) (boundedPairingsC (n+1)) (baseC n)

theorem opposite_simple_commuteB (n : ℕ) (R : Type*) [CommRing R]
    (i j : (baseB n).support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX (pairingB (n+1)) (baseB n) R i s)
      (adjointY (pairingB (n+1)) (baseB n) R j t) :=
  adjointX_commute_adjointY_of_diamond (pairingB (n+1)) (baseB n)
    (simpleDiamondProductsB n) R i j hij s t

theorem opposite_simple_commuteC (n : ℕ) (R : Type*) [CommRing R]
    (i j : (baseC n).support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX (pairingC (n+1)) (baseC n) R i s)
      (adjointY (pairingC (n+1)) (baseC n) R j t) :=
  adjointX_commute_adjointY_of_diamond (pairingC (n+1)) (baseC n)
    (simpleDiamondProductsC n) R i j hij s t
end ClassicalData

namespace F4Data

theorem boundedPairings : BoundedPairings pairing := by
  intro a b
  simpa only [pairingIn_int_eq] using pairing_bounds a b

theorem simpleDiamondProducts : SimpleDiamondProducts pairing base :=
  simpleDiamondProducts_of_boundedPairings pairing boundedPairings base

theorem opposite_simple_commute (R : Type*) [CommRing R]
    (i j : base.support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX pairing base R i s) (adjointY pairing base R j t) :=
  adjointX_commute_adjointY_of_diamond pairing base simpleDiamondProducts R i j hij s t
end F4Data
end Atlas.Chevalley
