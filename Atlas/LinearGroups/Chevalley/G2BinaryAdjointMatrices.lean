import Atlas.LinearGroups.Chevalley.Adjoint
import Atlas.LinearGroups.Chevalley.RootData.G2
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Actual integral Geck matrices for the binary G2 exception. The root-string
coefficients are derived from the twelve actual roots, before reduction mod2. -/
noncomputable section
namespace Atlas.Chevalley.G2Binary
open Classical Integral G2Data
open scoped Matrix
abbrev K := ZMod 2
abbrev I := Fin 2 ⊕ Fin 12
abbrev G := Adjoint pairing base K

def opposite (j : Fin 12) : Fin 12 :=
  ![2, 5, 0, 6, 9, 1, 3, 10, 11, 4, 7, 8] j

def cBot (i : Fin 2) (j : Fin 12) : ℕ :=
  ![![0,0,0,0,1,1,1,1,0,0,0,0],
    ![0,0,3,3,1,0,0,0,2,2,0,1]] i j

private theorem root_coordinates (j : Fin 12) : pairing.root j = G2Table.coordinates j := rfl
private theorem simple_val (i : Fin 2) :
    (baseIndexEquiv i).val = G2Table.simpleIndex i := rfl

private theorem root_sub_mem (i j : Fin 12) (n : ℕ) :
    pairing.root j - n • pairing.root i ∈ Set.range pairing.root ↔
      ∃ k : Fin 12, G2Table.coordinates k = G2Table.coordinates j - n • G2Table.coordinates i := by
  rfl

theorem chain_bot (i : Fin 2) (j : Fin 12) :
    pairing.chainBotCoeff (G2Table.simpleIndex i) j = cBot i j := by
  by_cases hz : cBot i j = 0
  · rw [hz]
    apply pairing.chainBotCoeff_eq_zero_iff.mpr
    right
    have hn : ¬ ∃ k : Fin 12, G2Table.coordinates k =
        G2Table.coordinates j - 1 • G2Table.coordinates (G2Table.simpleIndex i) := by
      fin_cases i <;> fin_cases j <;> norm_num [cBot] at hz <;> decide +kernel
    simpa only [one_smul] using (root_sub_mem (G2Table.simpleIndex i) j 1).not.mpr hn
  · have hd : pairing.root (G2Table.simpleIndex i) - pairing.root j ∈
        Set.range pairing.root := by
      have h : ∃ k : Fin 12, G2Table.coordinates k =
          G2Table.coordinates (G2Table.simpleIndex i) - 1 • G2Table.coordinates j := by
        fin_cases i <;> fin_cases j <;> norm_num [cBot] at hz <;> decide +kernel
      simpa only [one_smul] using (root_sub_mem j (G2Table.simpleIndex i) 1).mpr h
    have hi := pairing.linearIndependent_of_sub_mem_range_root' hd
    have hlo : cBot i j ≤ pairing.chainBotCoeff (G2Table.simpleIndex i) j := by
      apply (pairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hi).mp
      apply (root_sub_mem (G2Table.simpleIndex i) j (cBot i j)).mpr
      fin_cases i <;> fin_cases j <;> decide +kernel
    have hhi : ¬ cBot i j + 1 ≤ pairing.chainBotCoeff (G2Table.simpleIndex i) j := by
      rw [← pairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hi]
      apply (root_sub_mem (G2Table.simpleIndex i) j (cBot i j + 1)).not.mpr
      fin_cases i <;> fin_cases j <;> decide +kernel
    omega

private theorem neg_label (j : Fin 12) :
    pairing.reflectionPerm j j = opposite j := by
  apply pairing.root.injective
  simp only [pairing.root_reflectionPerm, pairing.reflection_apply_self, root_coordinates]
  fin_cases j <;> ext k <;> fin_cases k <;> decide +kernel

def coordinateEquiv : I ≃ (base.support ⊕ Fin 12) :=
  Equiv.sumCongr baseIndexEquiv (Equiv.refl _)

def reindex (R : Type*) [CommRing R] :
    Matrix (base.support ⊕ Fin 12) (base.support ⊕ Fin 12) R ≃+* Matrix I I R :=
  Matrix.reindexRingEquiv R coordinateEquiv.symm

private theorem reindex_apply {R : Type*} [CommRing R]
    (A : Matrix (base.support ⊕ Fin 12) (base.support ⊕ Fin 12) R) (a c : I) :
    reindex R A a c = A (coordinateEquiv a) (coordinateEquiv c) := rfl

/-- A computable integer matrix; it has not yet been reduced in characteristic2. -/
def E (k : Fin 2) : Matrix I I ℤ :=
  Matrix.fromBlocks 0
    (fun a j => if a = k ∧ j = opposite (G2Table.simpleIndex k) then 1 else 0)
    (fun a j => if a = G2Table.simpleIndex k then |G2Table.cartan k j| else 0)
    (fun a j => if G2Table.coordinates a = G2Table.coordinates (G2Table.simpleIndex k) +
      G2Table.coordinates j then (cBot k j : ℤ) + 1 else 0)

theorem reindex_raising (k : Fin 2) :
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

def divided (k : Fin 2) (n : ℕ) : Matrix I I ℤ :=
  fun a c => (E k ^ n) a c / (n.factorial : ℤ)

theorem reindex_divided (R : Type*) [CommRing R] (k : Fin 2) (n : ℕ) :
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

def X (k : Fin 2) (t : K) : Matrix I I K :=
  ∑ n ∈ Finset.range 4, t ^ n • (divided k n).map (Int.castRingHom K)
def Y (k : Fin 2) (t : K) : Matrix I I K := W K * X k t * W K

private theorem reindex_smul (t : K)
    (A : Matrix (base.support ⊕ Fin 12) (base.support ⊕ Fin 12) K) :
    reindex K (t • A) = t • reindex K A := rfl

theorem reindex_exponential (k : Fin 2) (t : K) :
    reindex K (raisingExponential pairing base K (baseIndexEquiv k) t) = X k t := by
  simp only [raisingExponential, map_sum, reindex_smul, reindex_divided, X]

set_option maxHeartbeats 1000000 in
def matrixHom : G →* Matrix I I K :=
  (reindex K).toMonoidHom.comp
    ((Units.coeHom (Matrix (base.support ⊕ Fin 12) (base.support ⊕ Fin 12) K)).comp
      (adjointSubgroup pairing base K).subtype)

theorem matrix_X (k : Fin 2) (t : K) :
    matrixHom (adjointX pairing base K (baseIndexEquiv k) t) = X k t :=
  reindex_exponential k t

theorem matrix_Y (k : Fin 2) (t : K) :
    matrixHom (adjointY pairing base K (baseIndexEquiv k) t) = Y k t := by
  change reindex K (oppositionOver pairing base K *
    raisingExponential pairing base K (baseIndexEquiv k) t *
    oppositionOver pairing base K) = _
  rw [map_mul, map_mul, reindex_opposition, reindex_exponential]
  rfl

end Atlas.Chevalley.G2Binary
