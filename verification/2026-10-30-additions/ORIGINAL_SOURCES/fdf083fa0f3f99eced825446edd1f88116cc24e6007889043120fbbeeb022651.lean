import Atlas.LinearGroups.Chevalley.G2BinaryAdjointMatrices
import Atlas.LinearGroups.Chevalley.Models
import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralSimple0
import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralSimple1
import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralSimple2
import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralSimple3

/-! Match the literal integral matrices to the existing Geck operators.
All division is in the integral divided powers before scalar reduction.
-/
noncomputable section
namespace Atlas.Chevalley.Comparison.G2
open Classical Integral G2Data
open scoped Matrix
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def flatReindex (R : Type*) [CommRing R] :
    Matrix (base.support ⊕ Fin 12) (base.support ⊕ Fin 12) R ≃+*
      Matrix (Fin 14) (Fin 14) R :=
  (G2Binary.reindex R).trans (Matrix.reindexRingEquiv R finSumFinEquiv)

theorem flatReindex_smul {R : Type*} [CommRing R] (t : R)
    (A : Matrix (base.support ⊕ Fin 12) (base.support ⊕ Fin 12) R) :
    flatReindex R (t • A) = t • flatReindex R A := rfl

theorem flatReindex_map {R : Type*} [CommRing R]
    (A : Matrix (base.support ⊕ Fin 12) (base.support ⊕ Fin 12) ℤ) :
    flatReindex R (A.map (Int.castRingHom R)) =
      (flatReindex ℤ A).map (Int.castRingHom R) := rfl

private theorem explicit_raising : ∀ i : Fin 2,
    Matrix.reindexRingEquiv ℤ finSumFinEquiv (G2Binary.E i) =
      geckMatrix (Fin.castAdd 2 i) := by
  decide +kernel

theorem flatReindex_raising (i : Fin 2) :
    flatReindex ℤ (raising pairing base (baseIndexEquiv i)) =
      geckMatrix (Fin.castAdd 2 i) := by
  change Matrix.reindexRingEquiv ℤ finSumFinEquiv
    (G2Binary.reindex ℤ (raising pairing base (baseIndexEquiv i))) = _
  rw [G2Binary.reindex_raising]
  exact explicit_raising i

private theorem explicit_lowering : ∀ i : Fin 2,
    Matrix.reindexRingEquiv ℤ finSumFinEquiv
      (G2Binary.W ℤ * G2Binary.E i * G2Binary.W ℤ) =
        geckMatrix (Fin.natAdd 2 i) := by
  decide +kernel

theorem flatReindex_lowering (i : Fin 2) :
    flatReindex ℤ (lowering pairing base (baseIndexEquiv i)) =
      geckMatrix (Fin.natAdd 2 i) := by
  have h := oppositionOver_raisingOver pairing base ℤ (baseIndexEquiv i)
  simp only [raisingOver, loweringOver, Int.castRingHom_int, RingHom.coe_id,
    Matrix.map_id] at h
  rw [← h]
  change Matrix.reindexRingEquiv ℤ finSumFinEquiv
    (G2Binary.reindex ℤ (oppositionOver pairing base ℤ *
      raising pairing base (baseIndexEquiv i) * oppositionOver pairing base ℤ)) = _
  rw [map_mul (G2Binary.reindex ℤ), map_mul (G2Binary.reindex ℤ),
    G2Binary.reindex_opposition, G2Binary.reindex_raising]
  exact explicit_lowering i

def geckDivided (i : Fin 4) (n : Fin 4) : Matrix (Fin 14) (Fin 14) ℤ :=
  ![1, geckMatrix i, geckSecondMatrix i, geckThirdMatrix i] n

theorem factorial_geckDivided (i n : Fin 4) :
    (n.val.factorial : ℤ) • geckDivided i n = geckMatrix i ^ n.val := by
  fin_cases i <;> fin_cases n <;> decide +kernel

theorem flatReindex_raisingDivided (i : Fin 2) (n : Fin 4) :
    flatReindex ℤ (raisingDividedPower pairing base (baseIndexEquiv i) n.val) =
      geckDivided (Fin.castAdd 2 i) n := by
  have hn : (n.val.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n.val
  apply smul_right_injective (M := Matrix (Fin 14) (Fin 14) ℤ) hn
  change (n.val.factorial : ℤ) •
      flatReindex ℤ (raisingDividedPower pairing base (baseIndexEquiv i) n.val) =
    (n.val.factorial : ℤ) • geckDivided (Fin.castAdd 2 i) n
  rw [← flatReindex_smul, factorial_smul_raisingDividedPower,
    map_pow, flatReindex_raising, factorial_geckDivided]

theorem flatReindex_loweringDivided (i : Fin 2) (n : Fin 4) :
    flatReindex ℤ (loweringDividedPower pairing base (baseIndexEquiv i) n.val) =
      geckDivided (Fin.natAdd 2 i) n := by
  have hn : (n.val.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n.val
  apply smul_right_injective (M := Matrix (Fin 14) (Fin 14) ℤ) hn
  change (n.val.factorial : ℤ) •
      flatReindex ℤ (loweringDividedPower pairing base (baseIndexEquiv i) n.val) =
    (n.val.factorial : ℤ) • geckDivided (Fin.natAdd 2 i) n
  rw [← flatReindex_smul, factorial_smul_loweringDividedPower,
    map_pow, flatReindex_lowering, factorial_geckDivided]

def geckExponential (R : Type*) [CommRing R] (i : Fin 4) (t : R) :
    Matrix (Fin 14) (Fin 14) R :=
  1 + t • (geckMatrix i).map (Int.castRingHom R) +
    t^2 • (geckSecondMatrix i).map (Int.castRingHom R) +
    t^3 • (geckThirdMatrix i).map (Int.castRingHom R)

theorem flatReindex_raisingExponential (R : Type*) [CommRing R] (i : Fin 2) (t : R) :
    flatReindex R (raisingExponential pairing base R (baseIndexEquiv i) t) =
      geckExponential R (Fin.castAdd 2 i) t := by
  simp only [raisingExponential, raisingDividedOver, map_sum, flatReindex_smul,
    flatReindex_map]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  erw [flatReindex_raisingDivided i 0, flatReindex_raisingDivided i 1,
    flatReindex_raisingDivided i 2, flatReindex_raisingDivided i 3]
  simp [geckDivided, geckExponential]

theorem flatReindex_loweringExponential (R : Type*) [CommRing R] (i : Fin 2) (t : R) :
    flatReindex R (loweringExponential pairing base R (baseIndexEquiv i) t) =
      geckExponential R (Fin.natAdd 2 i) t := by
  simp only [loweringExponential, map_sum, flatReindex_smul, flatReindex_map]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  erw [flatReindex_loweringDivided i 0, flatReindex_loweringDivided i 1,
    flatReindex_loweringDivided i 2, flatReindex_loweringDivided i 3]
  simp [geckDivided, geckExponential]

def matrixHom (R : Type*) [CommRing R] : Model .G2 R →*
    Matrix (Fin 14) (Fin 14) R :=
  (flatReindex R).toMonoidHom.comp
    ((Units.coeHom (Matrix (base.support ⊕ Fin 12) (base.support ⊕ Fin 12) R)).comp
      (adjointSubgroup pairing base R).subtype)

theorem matrixHom_injective (R : Type*) [CommRing R] :
    Function.Injective (matrixHom R) := by
  intro g h he
  exact Subtype.ext (Units.ext ((flatReindex R).injective he))

theorem matrixHom_X (R : Type*) [CommRing R] (i : Fin 2) (t : R) :
    matrixHom R (modelX .G2 R i t) = geckExponential R (Fin.castAdd 2 i) t :=
  flatReindex_raisingExponential R i t

theorem matrixHom_Y (R : Type*) [CommRing R] (i : Fin 2) (t : R) :
    matrixHom R (modelY .G2 R i t) = geckExponential R (Fin.natAdd 2 i) t := by
  change flatReindex R (loweringRootElement pairing base R (baseIndexEquiv i) t).val = _
  rw [loweringRootElement_val]
  exact flatReindex_loweringExponential R i t

end Atlas.Chevalley.Comparison.G2
