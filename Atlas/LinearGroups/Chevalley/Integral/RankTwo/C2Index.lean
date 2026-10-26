import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic
import Mathlib.Tactic

/-! Actual B2 root labels, also used by the flipped C2 datum.
Root exhaustion, indexing and actual root-string coefficients. This does not identify the
explicit template matrices with the actual Geck matrices. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData
open scoped Matrix

/-- Labels are in the underlying B lattice. In C these represent their coroots. -/
def labelCoordinates (i : Fin 8) : Fin 2 → ℤ :=
  ![ ![1,-1], ![0,1], ![1,1], ![1,0],
     ![-1,1], ![0,-1], ![-1,-1], ![-1,0] ] i

def label (i : Fin 8) : BRoot 2 :=
  ⟨labelCoordinates i, by
    fin_cases i <;>
      norm_num [labelCoordinates, dot, Fin.sum_univ_succ]⟩

theorem label_injective : Function.Injective label := by
  have hc : Function.Injective labelCoordinates := by decide
  intro i j h
  exact hc (congrArg Subtype.val h)

/-- Exhaustion of the actual root subtype, not a separately postulated root set. -/
theorem label_surjective : Function.Surjective label := by
  intro a
  rcases coordinate_cases a 0 with h0 | h0 | h0 <;>
    rcases coordinate_cases a 1 with h1 | h1 | h1
  · refine ⟨6, Subtype.ext ?_⟩
    funext j
    fin_cases j <;> simp [label, labelCoordinates, h0, h1]
  · refine ⟨7, Subtype.ext ?_⟩
    funext j
    fin_cases j <;> simp [label, labelCoordinates, h0, h1]
  · refine ⟨4, Subtype.ext ?_⟩
    funext j
    fin_cases j <;> simp [label, labelCoordinates, h0, h1]
  · refine ⟨5, Subtype.ext ?_⟩
    funext j
    fin_cases j <;> simp [label, labelCoordinates, h0, h1]
  · have hn := a.property
    norm_num [dot, Fin.sum_univ_succ, h0, h1] at hn
  · refine ⟨1, Subtype.ext ?_⟩
    funext j
    fin_cases j <;> simp [label, labelCoordinates, h0, h1]
  · refine ⟨0, Subtype.ext ?_⟩
    funext j
    fin_cases j <;> simp [label, labelCoordinates, h0, h1]
  · refine ⟨3, Subtype.ext ?_⟩
    funext j
    fin_cases j <;> simp [label, labelCoordinates, h0, h1]
  · refine ⟨2, Subtype.ext ?_⟩
    funext j
    fin_cases j <;> simp [label, labelCoordinates, h0, h1]

def labelEquiv : Fin 8 ≃ BRoot 2 :=
  Equiv.ofBijective label ⟨label_injective, label_surjective⟩

end Atlas.Chevalley.Integral.RankTwo

namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData

/-- Actual C2 Geck coordinates: Cartan coordinates first, then all eight roots. -/
def c2IndexEquiv : Fin 10 ≃ ((baseC 1).support ⊕ BRoot 2) :=
  (finSumFinEquiv : Fin 2 ⊕ Fin 8 ≃ Fin 10).symm.trans
    (Equiv.sumCongr (baseCIndexEquiv 1) labelEquiv)

/-- C2 terminal short/long operators in the exact template indexing. -/
def c2ActualRaising (k : Fin 2) : Matrix (Fin 10) (Fin 10) ℤ :=
  fun i j => RootPairing.GeckConstruction.e (P := pairingC 2) (b := baseC 1)
    (baseCIndexEquiv 1 k) (c2IndexEquiv i) (c2IndexEquiv j)

end Atlas.Chevalley.Integral.RankTwo

namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData
open scoped Matrix

/-- Literal roots of the flipped datum, expressed in the coordinate dual. -/
def cCoordinates (i : Fin 8) : Fin 2 → ℤ :=
  ![ ![1,-1], ![0,2], ![1,1], ![2,0],
     ![-1,1], ![0,-2], ![-1,-1], ![-2,0] ] i

theorem c_root_label (i : Fin 8) :
    (pairingC 2).root (label i) = functional (cCoordinates i) := by
  change coroot (label i) = functional (cCoordinates i)
  ext x
  fin_cases i <;>
    norm_num [label, labelCoordinates, cCoordinates, coroot, corootScale,
      functional_apply, dot, Fin.sum_univ_succ] <;> ring

theorem functional_mem_c_root_range (v : Fin 2 → ℤ) :
    functional v ∈ Set.range (pairingC 2).root ↔
      ∃ k : Fin 8, cCoordinates k = v := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨k, rfl⟩ := label_surjective a
    rw [c_root_label] at ha
    exact ⟨k, by simpa using congrArg (functionalCoordinates 2) ha⟩
  · rintro ⟨k, rfl⟩
    exact ⟨label k, c_root_label k⟩

theorem c_root_sub_mem (i j : Fin 8) (n : ℕ) :
    (pairingC 2).root (label j) - n • (pairingC 2).root (label i)
      ∈ Set.range (pairingC 2).root ↔
    ∃ k : Fin 8, cCoordinates k = cCoordinates j - n • cCoordinates i := by
  rw [c_root_label, c_root_label]
  have he : functional (cCoordinates j) - n • functional (cCoordinates i) =
      functional (cCoordinates j - n • cCoordinates i) := by
    ext x
    simp [functional_apply, dot, Fin.sum_univ_succ, nsmul_eq_mul]
    <;> ring
  rw [he, functional_mem_c_root_range]

/-- The displayed endpoint table is checked arithmetically below, and only then
identified with the actual noncomputable root-string coefficients. -/
def simpleLabelIndex (i : Fin 2) : Fin 8 := ⟨i.val, by omega⟩

def cBot (i : Fin 2) (j : Fin 8) : ℕ :=
  ![ ![0,0,1,2,0,2,1,0], ![0,0,1,0,1,0,0,0] ] i j

theorem c_chain_bot (i : Fin 2) (j : Fin 8) :
    (pairingC 2).chainBotCoeff (label (simpleLabelIndex i)) (label j) = cBot i j := by
  by_cases hz : cBot i j = 0
  · rw [hz]
    apply (pairingC 2).chainBotCoeff_eq_zero_iff.mpr
    right
    have hn : ¬ ∃ k : Fin 8,
        cCoordinates k = cCoordinates j - 1 • cCoordinates (simpleLabelIndex i) := by
      fin_cases i <;> fin_cases j <;>
        norm_num [cBot] at hz <;> decide
    simpa only [one_smul] using (c_root_sub_mem (simpleLabelIndex i) j 1).not.mpr hn
  · have hdiff : (pairingC 2).root (label (simpleLabelIndex i)) -
        (pairingC 2).root (label j) ∈ Set.range (pairingC 2).root := by
      have hd : ∃ k : Fin 8,
          cCoordinates k = cCoordinates (simpleLabelIndex i) - 1 • cCoordinates j := by
        fin_cases i <;> fin_cases j <;>
          norm_num [cBot] at hz <;> decide
      simpa only [one_smul] using (c_root_sub_mem j (simpleLabelIndex i) 1).mpr hd
    have hi := (pairingC 2).linearIndependent_of_sub_mem_range_root' hdiff
    have hlo : cBot i j ≤ (pairingC 2).chainBotCoeff (label (simpleLabelIndex i)) (label j) := by
      apply ((pairingC 2).root_sub_nsmul_mem_range_iff_le_chainBotCoeff hi).mp
      apply (c_root_sub_mem (simpleLabelIndex i) j (cBot i j)).mpr
      fin_cases i <;> fin_cases j <;> decide
    have hhi : ¬ cBot i j + 1 ≤
        (pairingC 2).chainBotCoeff (label (simpleLabelIndex i)) (label j) := by
      rw [← (pairingC 2).root_sub_nsmul_mem_range_iff_le_chainBotCoeff hi]
      apply (c_root_sub_mem (simpleLabelIndex i) j (cBot i j + 1)).not.mpr
      fin_cases i <;> fin_cases j <;> decide
    omega

end Atlas.Chevalley.Integral.RankTwo

namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData
open scoped Matrix

theorem c_simple_label (i : Fin 2) :
    (baseCIndexEquiv 1 i).val = label (simpleLabelIndex i) := by
  change simpleB 1 i = label (simpleLabelIndex i)
  fin_cases i <;> apply Subtype.ext <;> decide


def oppositeLabel (i : Fin 8) : Fin 8 := ![4,5,6,7,0,1,2,3] i

theorem c_neg_label (i : Fin 8) :
    let _ := (pairingC 2).indexNeg;
    -(label i) = label (oppositeLabel i) := by
  letI := (pairingC 2).indexNeg
  apply (pairingC 2).root.injective
  have he : (pairingC 2).root (-(label i)) = -(pairingC 2).root (label i) := by
    simp [RootPairing.indexNeg_neg]
  rw [he, c_root_label, c_root_label]
  fin_cases i <;> ext x <;> fin_cases x <;> decide

/-- Explicit relabelling from C2 table coordinates to the B2 short/long order. -/
def bLabelPermutation : Equiv.Perm (Fin 8) where
  toFun i := ![1,0,3,2,5,4,7,6] i
  invFun i := ![1,0,3,2,5,4,7,6] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def bLabelEquiv : Fin 8 ≃ BRoot 2 := bLabelPermutation.trans labelEquiv

def bSimplePermutation : Equiv.Perm (Fin 2) where
  toFun i := ![1,0] i
  invFun i := ![1,0] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def b2IndexEquiv : Fin 10 ≃ ((baseB 1).support ⊕ BRoot 2) :=
  (finSumFinEquiv : Fin 2 ⊕ Fin 8 ≃ Fin 10).symm.trans
    (Equiv.sumCongr (bSimplePermutation.trans (baseBIndexEquiv 1)) bLabelEquiv)

/-- B2 pulled operator index0 is short, index1 long, as in the C2 template. -/
def b2ActualRaising (k : Fin 2) : Matrix (Fin 10) (Fin 10) ℤ :=
  fun i j => RootPairing.GeckConstruction.e (P := pairingB 2) (b := baseB 1)
    (baseBIndexEquiv 1 (bSimplePermutation k)) (b2IndexEquiv i) (b2IndexEquiv j)

end Atlas.Chevalley.Integral.RankTwo
