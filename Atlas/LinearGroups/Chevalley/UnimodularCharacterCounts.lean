import Atlas.LinearGroups.Chevalley.RootData.ExceptionalWeightLattices
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.SetTheory.Cardinal.Finite

/-! The actual exceptional weight/root quotients have one character.
This is not an identification of a finite Chevalley group center. -/
noncomputable section
namespace Atlas.Chevalley
open Integral.Minuscule

theorem weightRootCharacters_card_of_top
    {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) (h : rootLattice P = ⊤)
    (G : Type*) [Monoid G] :
    Nat.card (Multiplicative (WeightLattice P ⧸ rootLattice P) →* G) = 1 := by
  rw [h]
  exact Nat.card_unique

theorem E8_weightRootCharacters_card (G : Type*) [Monoid G] :
    Nat.card (Multiplicative
      (WeightLattice E8Data.pairing ⧸ rootLattice E8Data.pairing) →* G) = 1 :=
  weightRootCharacters_card_of_top E8Data.pairing E8Data.rootLattice_eq_top G

theorem F4_weightRootCharacters_card (G : Type*) [Monoid G] :
    Nat.card (Multiplicative
      (WeightLattice F4Data.pairing ⧸ rootLattice F4Data.pairing) →* G) = 1 :=
  weightRootCharacters_card_of_top F4Data.pairing F4Data.rootLattice_eq_top G

theorem G2_weightRootCharacters_card (G : Type*) [Monoid G] :
    Nat.card (Multiplicative
      (WeightLattice G2Data.pairing ⧸ rootLattice G2Data.pairing) →* G) = 1 :=
  weightRootCharacters_card_of_top G2Data.pairing G2Data.rootLattice_eq_top G

end Atlas.Chevalley
