import Atlas.LinearGroups.Chevalley.Adjoint
import Atlas.LinearGroups.Chevalley.RootData.F4
import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralOperatorData
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

/-! Actual F4 Geck matrices. Root-string coefficients are proved from
the actual forty-eight roots; no matrix is identified by numerical order.
-/
noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Classical Integral F4Data
open scoped Matrix
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
abbrev I := Fin 4 ⊕ Fin 48

def opposite (j : Fin 48) : Fin 48 :=
  ![3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12,19,18,17,16,23,22,21,20,25,24,27,26,29,28,31,30,47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,32] j

def cBot (i : Fin 4) (j : Fin 48) : ℕ :=
  ![![1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,0,0,1,0,0,1,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0],
    ![0,0,0,0,1,0,1,0,0,1,0,1,1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0],
    ![0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,2,0,2,0,2,0,1,1,1,1,1,1,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0],
    ![0,2,0,0,0,2,0,0,0,2,0,0,0,0,0,2,0,0,0,2,0,0,0,2,1,0,0,1,0,1,0,1,0,1,1,1,1,1,1,0,0,0,0,1,0,1,1,1]] i j

private theorem root_coordinates (j : Fin 48) : pairing.root j = F4Table.coordinates j := rfl
private theorem simple_val (i : Fin 4) :
    (baseIndexEquiv i).val = F4Table.simpleIndex i := rfl

private theorem root_sub_mem (i j : Fin 48) (n : ℕ) :
    pairing.root j - n • pairing.root i ∈ Set.range pairing.root ↔
      ∃ k : Fin 48, F4Table.coordinates k = F4Table.coordinates j - n • F4Table.coordinates i := by
  rfl

theorem chain_bot (i : Fin 4) (j : Fin 48) :
    pairing.chainBotCoeff (F4Table.simpleIndex i) j = cBot i j := by
  by_cases hz : cBot i j = 0
  · rw [hz]
    apply pairing.chainBotCoeff_eq_zero_iff.mpr
    right
    have hn : ¬ ∃ k : Fin 48, F4Table.coordinates k =
        F4Table.coordinates j - 1 • F4Table.coordinates (F4Table.simpleIndex i) := by
      fin_cases i <;> fin_cases j <;> norm_num [cBot] at hz <;> decide +kernel
    simpa only [one_smul] using (root_sub_mem (F4Table.simpleIndex i) j 1).not.mpr hn
  · have hd : pairing.root (F4Table.simpleIndex i) - pairing.root j ∈
        Set.range pairing.root := by
      have h : ∃ k : Fin 48, F4Table.coordinates k =
          F4Table.coordinates (F4Table.simpleIndex i) - 1 • F4Table.coordinates j := by
        fin_cases i <;> fin_cases j <;> norm_num [cBot] at hz <;> decide +kernel
      simpa only [one_smul] using (root_sub_mem j (F4Table.simpleIndex i) 1).mpr h
    have hi := pairing.linearIndependent_of_sub_mem_range_root' hd
    have hlo : cBot i j ≤ pairing.chainBotCoeff (F4Table.simpleIndex i) j := by
      apply (pairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hi).mp
      apply (root_sub_mem (F4Table.simpleIndex i) j (cBot i j)).mpr
      fin_cases i <;> fin_cases j <;> decide +kernel
    have hhi : ¬ cBot i j + 1 ≤ pairing.chainBotCoeff (F4Table.simpleIndex i) j := by
      rw [← pairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hi]
      apply (root_sub_mem (F4Table.simpleIndex i) j (cBot i j + 1)).not.mpr
      fin_cases i <;> fin_cases j <;> decide +kernel
    omega

private theorem neg_label (j : Fin 48) :
    pairing.reflectionPerm j j = opposite j := by
  apply pairing.root.injective
  simp only [pairing.root_reflectionPerm, pairing.reflection_apply_self, root_coordinates]
  fin_cases j <;> ext k <;> fin_cases k <;> decide +kernel

def coordinateEquiv : I ≃ (base.support ⊕ Fin 48) :=
  Equiv.sumCongr baseIndexEquiv (Equiv.refl _)

def reindex (R : Type*) [CommRing R] :
    Matrix (base.support ⊕ Fin 48) (base.support ⊕ Fin 48) R ≃+* Matrix I I R :=
  Matrix.reindexRingEquiv R coordinateEquiv.symm

private theorem reindex_apply {R : Type*} [CommRing R]
    (A : Matrix (base.support ⊕ Fin 48) (base.support ⊕ Fin 48) R) (a c : I) :
    reindex R A a c = A (coordinateEquiv a) (coordinateEquiv c) := rfl

/-- A computable integer matrix; it has not yet been reduced in characteristic2. -/
def E (k : Fin 4) : Matrix I I ℤ :=
  Matrix.fromBlocks 0
    (fun a j => if a = k ∧ j = opposite (F4Table.simpleIndex k) then 1 else 0)
    (fun a j => if a = F4Table.simpleIndex k then |F4Table.cartan k j| else 0)
    (fun a j => if F4Table.coordinates a = F4Table.coordinates (F4Table.simpleIndex k) +
      F4Table.coordinates j then (cBot k j : ℤ) + 1 else 0)

theorem reindex_raising (k : Fin 4) :
    reindex ℤ (raising pairing base (baseIndexEquiv k)) = E k := by
  ext (a | a) (c | c) <;>
    simp [reindex_apply, coordinateEquiv, raising, RootPairing.GeckConstruction.e,
      E, Matrix.fromBlocks, simple_val, neg_label, baseIndexEquiv.injective.eq_iff,
      base_cartan, root_coordinates, chain_bot]

def W (R : Type*) [CommRing R] : Matrix I I R :=
  Matrix.fromBlocks 1 0 0 (fun a c => if a = opposite c then 1 else 0)

theorem reindex_opposition (R : Type*) [CommRing R] :
    reindex R (oppositionOver pairing base R) = W R := by
  ext (a | a) (c | c) <;>
    simp [reindex_apply, coordinateEquiv, oppositionOver, RootPairing.GeckConstruction.ω,
      W, Matrix.fromBlocks, Matrix.one_apply, neg_label, baseIndexEquiv.injective.eq_iff]

def divided (k : Fin 4) (n : ℕ) : Matrix I I ℤ :=
  fun a c => (E k ^ n) a c / (n.factorial : ℤ)

theorem reindex_divided (R : Type*) [CommRing R] (k : Fin 4) (n : ℕ) :
    reindex R (raisingDividedOver pairing base R (baseIndexEquiv k) n) =
      (divided k n).map (Int.castRingHom R) := by
  ext a c
  have h := congrFun (congrFun ((reindex ℤ).map_pow
    (raising pairing base (baseIndexEquiv k)) n) a) c
  rw [reindex_raising] at h
  change (raising pairing base (baseIndexEquiv k) ^ n)
      (coordinateEquiv a) (coordinateEquiv c) = (E k ^ n) a c at h
  change (((raising pairing base (baseIndexEquiv k) ^ n)
      (coordinateEquiv a) (coordinateEquiv c) / (n.factorial : ℤ) : ℤ) : R) = _
  rw [h]
  rfl


/-- The final numeric indexing preserves the four Cartan coordinates followed
by the existing forty-eight Albert root labels. -/
def coordinateEquiv52 : Fin 52 ≃ (base.support ⊕ Fin 48) :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm.trans coordinateEquiv

def reindex52 (R : Type*) [CommRing R] :
    Matrix (base.support ⊕ Fin 48) (base.support ⊕ Fin 48) R ≃+*
      Matrix (Fin 52) (Fin 52) R :=
  Matrix.reindexRingEquiv R coordinateEquiv52.symm

end Atlas.Chevalley.Comparison.F4
