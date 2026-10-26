import Atlas.LinearGroups.Chevalley.Integral.RankTwo.B2Correspondence
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2WeylCorrespondence

/-! UNCHECKED successor to B2Correspondence. Reindex integral divided powers,
then compare the actual exponentials over every commutative ring. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData C2IntegerTemplate
open scoped Matrix
local instance b2TransportRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance b2TransportBaseDecidableEq : DecidableEq (baseB 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseB 1).support})
local instance c2TransportBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem b2_opposition_entry (i j : Fin 10) :
    (RootPairing.GeckConstruction.ω (baseB 1) :
      Matrix ((baseB 1).support ⊕ BRoot 2) ((baseB 1).support ⊕ BRoot 2) ℤ)
      (b2IndexEquiv i) (b2IndexEquiv j) = omega i j := by
  have hn (k : Fin 8) :
      (pairingB (1+1)).reflectionPerm (bLabelEquiv k) (bLabelEquiv k) =
        bLabelEquiv (oppositeLabel k) := b_reflection_self_label k

  fin_cases i <;> fin_cases j <;>
    norm_num [b2IndexEquiv, c2_sum_split,
      RootPairing.GeckConstruction.ω, b_neg_label, b_reflection_self_label,
      bLabelEquiv.injective.eq_iff, oppositeLabel, omega, Matrix.fromBlocks, hn] <;> decide

theorem b2_divided_entry (k : Fin 2) (n : ℕ) (i j : Fin 10) :
    raisingDividedPower (pairingB 2) (baseB 1)
      (baseBIndexEquiv 1 (bSimplePermutation k)) n (b2IndexEquiv i) (b2IndexEquiv j) =
    (b2ActualRaising k ^ n) i j / (n.factorial : ℤ) := by
  let E := Matrix.reindexAlgEquiv ℤ ℤ b2IndexEquiv.symm
  have hE : E (raising (pairingB 2) (baseB 1)
      (baseBIndexEquiv 1 (bSimplePermutation k))) = b2ActualRaising k := rfl
  have hp := E.map_pow (raising (pairingB 2) (baseB 1)
    (baseBIndexEquiv 1 (bSimplePermutation k))) n
  change E (raising (pairingB 2) (baseB 1)
      (baseBIndexEquiv 1 (bSimplePermutation k)) ^ n) =
    E (raising (pairingB 2) (baseB 1)
      (baseBIndexEquiv 1 (bSimplePermutation k))) ^ n at hp
  rw [hE] at hp
  have he := congrArg (fun A => A i j) hp
  change (raising (pairingB 2) (baseB 1)
    (baseBIndexEquiv 1 (bSimplePermutation k)) ^ n)
      (b2IndexEquiv i) (b2IndexEquiv j) = (b2ActualRaising k ^ n) i j at he
  unfold raisingDividedPower
  exact congrArg (fun z : ℤ => z / (n.factorial : ℤ)) he

theorem b2_c2_divided_entry (k : Fin 2) (n : ℕ) (i j : Fin 10) :
    raisingDividedPower (pairingB 2) (baseB 1)
      (baseBIndexEquiv 1 (bSimplePermutation k)) n (b2IndexEquiv i) (b2IndexEquiv j) =
    raisingDividedPower (pairingC 2) (baseC 1)
      (baseCIndexEquiv 1 k) n (c2IndexEquiv i) (c2IndexEquiv j) := by
  rw [b2_divided_entry, c2_divided_entry, b2ActualRaising_eq_c2]

variable (R : Type*) [CommRing R]

def b2Reindex :
    Matrix ((baseB 1).support ⊕ BRoot 2) ((baseB 1).support ⊕ BRoot 2) R ≃ₐ[R]
      Matrix (Fin 10) (Fin 10) R :=
  Matrix.reindexAlgEquiv R R b2IndexEquiv.symm

/-- This is a permutation of the ten integral Geck coordinates, valid also mod2. -/
def b2c2MatrixEquiv :
    Matrix ((baseB 1).support ⊕ BRoot 2) ((baseB 1).support ⊕ BRoot 2) R ≃ₐ[R]
      Matrix ((baseC 1).support ⊕ BRoot 2) ((baseC 1).support ⊕ BRoot 2) R :=
  (b2Reindex R).trans (c2Reindex R).symm

theorem b2_c2_raising_reindex (k : Fin 2) (t : R) :
    b2Reindex R (raisingExponential (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t) =
    c2Reindex R (raisingExponential (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 k) t) := by
  ext i j
  change raisingExponential (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t (b2IndexEquiv i) (b2IndexEquiv j) =
    raisingExponential (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 k) t (c2IndexEquiv i) (c2IndexEquiv j)
  simp only [raisingExponential, Matrix.sum_apply, Matrix.smul_apply,
    raisingDividedOver, Matrix.map_apply, b2_c2_divided_entry]

theorem b2_c2_opposition_reindex :
    b2Reindex R (oppositionOver (pairingB 2) (baseB 1) R) =
    c2Reindex R (oppositionOver (pairingC 2) (baseC 1) R) := by
  ext i j
  change (Int.castRingHom R) ((RootPairing.GeckConstruction.ω (baseB 1))
      (b2IndexEquiv i) (b2IndexEquiv j)) =
    (Int.castRingHom R) ((RootPairing.GeckConstruction.ω (baseC 1))
      (c2IndexEquiv i) (c2IndexEquiv j))
  rw [b2_opposition_entry, c2_opposition_entry]

theorem b2c2MatrixEquiv_raising (k : Fin 2) (t : R) :
    b2c2MatrixEquiv R (raisingExponential (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t) =
    raisingExponential (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t := by
  simp only [b2c2MatrixEquiv, AlgEquiv.trans_apply,
    b2_c2_raising_reindex, AlgEquiv.symm_apply_apply]

theorem b2c2MatrixEquiv_opposition :
    b2c2MatrixEquiv R (oppositionOver (pairingB 2) (baseB 1) R) =
    oppositionOver (pairingC 2) (baseC 1) R := by
  simp only [b2c2MatrixEquiv, AlgEquiv.trans_apply,
    b2_c2_opposition_reindex, AlgEquiv.symm_apply_apply]

/-- Both actual lowering units are the same opposition conjugation. -/
theorem b2c2MatrixEquiv_lowering (k : Fin 2) (t : R) :
    b2c2MatrixEquiv R (loweringRootElement (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t).val =
    (loweringRootElement (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t).val := by
  change b2c2MatrixEquiv R (oppositionOver (pairingB 2) (baseB 1) R *
    raisingExponential (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t *
    oppositionOver (pairingB 2) (baseB 1) R) =
    oppositionOver (pairingC 2) (baseC 1) R *
      raisingExponential (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t *
      oppositionOver (pairingC 2) (baseC 1) R
  rw [map_mul, map_mul, b2c2MatrixEquiv_opposition, b2c2MatrixEquiv_raising]

end Atlas.Chevalley.Integral.RankTwo
