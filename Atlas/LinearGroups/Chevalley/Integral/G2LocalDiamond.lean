import Atlas.LinearGroups.Chevalley.Integral.LocalDiamondCommutation
import Atlas.LinearGroups.Chevalley.RootData.G2

/-! A kernel-checked finite calculation on the actual twelve roots: a full
simple-root diamond does not occur in G2. No chain-table evaluation is needed.
The finite arithmetic theorem uses ordinary kernel decide. -/
namespace Atlas.Chevalley.G2Table
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem no_simple_diamond : ∀ (i j : Fin 2) (k : Root), i ≠ j →
    ¬ ((∃ l : Root, coordinates k + coordinates (simpleIndex i) = coordinates l) ∧
       (∃ m : Root, coordinates k - coordinates (simpleIndex j) = coordinates m) ∧
       (∃ n : Root, coordinates k + coordinates (simpleIndex i) -
          coordinates (simpleIndex j) = coordinates n)) := by decide +kernel

end Atlas.Chevalley.G2Table
noncomputable section
namespace Atlas.Chevalley.G2Data
open Integral
open Classical

theorem simpleDiamondProducts : Integral.SimpleDiamondProducts pairing base := by
  intro i j hij k l m hplus hminus hlast
  obtain ⟨i, rfl⟩ := baseIndexEquiv.surjective i
  obtain ⟨j, rfl⟩ := baseIndexEquiv.surjective j
  have hne : i ≠ j := fun h => hij (congrArg baseIndexEquiv h)
  obtain ⟨n, hn⟩ := hlast
  have hp : G2Table.coordinates k + G2Table.coordinates (G2Table.simpleIndex i) =
      G2Table.coordinates l := hplus
  have hm : G2Table.coordinates k - G2Table.coordinates (G2Table.simpleIndex j) =
      G2Table.coordinates m := hminus
  have hn' : G2Table.coordinates k + G2Table.coordinates (G2Table.simpleIndex i) -
      G2Table.coordinates (G2Table.simpleIndex j) = G2Table.coordinates n := hn.symm
  exact (G2Table.no_simple_diamond i j k hne ⟨⟨l, hp⟩, ⟨m, hm⟩, ⟨n, hn'⟩⟩).elim

theorem opposite_simple_commute (R : Type*) [CommRing R]
    (i j : base.support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX pairing base R i s) (adjointY pairing base R j t) :=
  adjointX_commute_adjointY_of_diamond pairing base simpleDiamondProducts R i j hij s t

end Atlas.Chevalley.G2Data
