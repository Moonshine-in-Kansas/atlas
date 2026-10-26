import Atlas.LinearGroups.Chevalley.Integral.SimplyLacedDiamond
import Atlas.LinearGroups.Chevalley.RootData.A
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesD
import Atlas.LinearGroups.Chevalley.RootData.E6
import Atlas.LinearGroups.Chevalley.RootData.E7
import Atlas.LinearGroups.Chevalley.RootData.E8

/-! Concrete simply-laced diamond adapters. These use actual installed
integral root pairings and bases, with no field irreducibility assumption. -/
noncomputable section
namespace Atlas.Chevalley
open Integral
open Classical

private theorem integer_pairingIn_eq {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) [P.IsCrystallographic] (i j : ι) :
    P.pairingIn ℤ i j = P.pairing i j := by
  simpa using P.algebraMap_pairingIn ℤ i j

namespace TypeAData

theorem pairingIn_symmetric (n : ℕ) (i j : Root n) :
    (pairing n).pairingIn ℤ i j = (pairing n).pairingIn ℤ j i := by
  rw [integer_pairingIn_eq, integer_pairingIn_eq]
  change coroot j (root i) = coroot i (root j)
  simp only [coroot_apply, root, Pi.sub_apply, Pi.single_apply]
  simp only [eq_comm]
  ring

theorem simpleDiamondProducts (r : ℕ) :
    Integral.SimpleDiamondProducts (pairing (r + 1)) (base r) :=
  Integral.simpleDiamondProducts_of_symmetric (pairing (r + 1))
    (pairingIn_symmetric (r + 1)) (base r)

/-- Actual A_r root/base model, including every rank accepted by the existing provider. -/
theorem opposite_simple_commute (r : ℕ) (R : Type*) [CommRing R]
    (i j : (base r).support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX (pairing (r+1)) (base r) R i s)
      (adjointY (pairing (r+1)) (base r) R j t) :=
  adjointX_commute_adjointY_of_diamond (pairing (r+1)) (base r)
    (simpleDiamondProducts r) R i j hij s t
end TypeAData

namespace ClassicalData

theorem pairingD_pairingIn_symmetric (n : ℕ) (i j : DRoot n) :
    (pairingD n).pairingIn ℤ i j = (pairingD n).pairingIn ℤ j i := by
  rw [integer_pairingIn_eq, integer_pairingIn_eq]
  have hi : dot i.val i.val = 2 := by simpa using i.property
  have hj : dot j.val j.val = 2 := by simpa using j.property
  change coroot j i.val = coroot i j.val
  simp only [coroot_apply, corootScale, hi, hj]
  norm_num
  exact dot_comm _ _

theorem simpleDiamondProductsD (n : ℕ) :
    Integral.SimpleDiamondProducts (pairingD (n + 2)) (baseD n) :=
  Integral.simpleDiamondProducts_of_symmetric (pairingD (n + 2))
    (pairingD_pairingIn_symmetric (n + 2)) (baseD n)

/-- Includes actual D_(n+2) and its low-rank reducible root datum, since no
connectedness or irreducibility hypothesis is needed for this local identity. -/
theorem opposite_simple_commuteD (n : ℕ) (R : Type*) [CommRing R]
    (i j : (baseD n).support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX (pairingD (n+2)) (baseD n) R i s)
      (adjointY (pairingD (n+2)) (baseD n) R j t) :=
  adjointX_commute_adjointY_of_diamond (pairingD (n+2)) (baseD n)
    (simpleDiamondProductsD n) R i j hij s t
end ClassicalData

namespace FiniteSimplyLaced.Data

theorem pairingIn_symmetric {r N : ℕ} [NeZero r] (d : FiniteSimplyLaced.Data r N) (i j : Fin N) :
    d.pairing.pairingIn ℤ i j = d.pairing.pairingIn ℤ j i := by
  rw [integer_pairingIn_eq, integer_pairingIn_eq]
  change d.form (d.root j) (d.root i) = d.form (d.root i) (d.root j)
  exact d.form_symm _ _

theorem simpleDiamondProducts {r N : ℕ} [NeZero r] (d : FiniteSimplyLaced.Data r N) :
    Integral.SimpleDiamondProducts d.pairing d.base :=
  Integral.simpleDiamondProducts_of_symmetric d.pairing d.pairingIn_symmetric d.base
end FiniteSimplyLaced.Data

namespace E6Data
local instance : Fintype Root := Fintype.ofFinite _

theorem pairingIn_symmetric (i j : Root) : pairing.pairingIn ℤ i j = pairing.pairingIn ℤ j i := by
  rw [integer_pairingIn_eq, integer_pairingIn_eq]
  change polar j.val i.val = polar i.val j.val
  exact polar_symm _ _

theorem simpleDiamondProducts : Integral.SimpleDiamondProducts pairing base :=
  Integral.simpleDiamondProducts_of_symmetric pairing pairingIn_symmetric base

theorem opposite_simple_commute (R : Type*) [CommRing R]
    (i j : base.support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX pairing base R i s) (adjointY pairing base R j t) :=
  adjointX_commute_adjointY_of_diamond pairing base simpleDiamondProducts R i j hij s t
end E6Data
namespace E7Data
theorem pairingIn_symmetric (i j : Root) : pairing.pairingIn ℤ i j = pairing.pairingIn ℤ j i :=
  datum.pairingIn_symmetric i j
theorem simpleDiamondProducts : Integral.SimpleDiamondProducts pairing base :=
  datum.simpleDiamondProducts
theorem opposite_simple_commute (R : Type*) [CommRing R]
    (i j : base.support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX pairing base R i s) (adjointY pairing base R j t) :=
  adjointX_commute_adjointY_of_diamond pairing base simpleDiamondProducts R i j hij s t
end E7Data
namespace E8Data
theorem pairingIn_symmetric (i j : Root) : pairing.pairingIn ℤ i j = pairing.pairingIn ℤ j i :=
  datum.pairingIn_symmetric i j
theorem simpleDiamondProducts : Integral.SimpleDiamondProducts pairing base :=
  datum.simpleDiamondProducts
theorem opposite_simple_commute (R : Type*) [CommRing R]
    (i j : base.support) (hij : i ≠ j) (s t : R) :
    Commute (adjointX pairing base R i s) (adjointY pairing base R j t) :=
  adjointX_commute_adjointY_of_diamond pairing base simpleDiamondProducts R i j hij s t
end E8Data

end Atlas.Chevalley
