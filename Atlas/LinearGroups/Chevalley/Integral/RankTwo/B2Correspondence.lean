import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2Correspondence

/-! UNCHECKED finite-coordinate B2/C2 comparison. The ambient lattices are not
identified by GL2(Z); only the actual eight roots and two Cartan coordinates
are reindexed. No coefficient-ring division is used. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData C2IntegerTemplate
open scoped Matrix
local instance b2CorrespondenceRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance b2CorrespondenceBaseDecidableEq : DecidableEq (baseB 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseB 1).support})
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def bCoordinates (i : Fin 8) : Fin 2 → ℤ := labelCoordinates (bLabelPermutation i)

theorem bLabelEquiv_apply (i : Fin 8) : bLabelEquiv i = label (bLabelPermutation i) := rfl

theorem b_root_label (i : Fin 8) :
    (pairingB 2).root (bLabelEquiv i) = bCoordinates i := rfl

theorem coordinates_mem_b_root_range (v : Fin 2 → ℤ) :
    v ∈ Set.range (pairingB 2).root ↔ ∃ k : Fin 8, bCoordinates k = v := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨k,rfl⟩ := bLabelEquiv.surjective a
    exact ⟨k,ha⟩
  · rintro ⟨k,rfl⟩
    exact ⟨bLabelEquiv k,rfl⟩

theorem b_root_sub_mem (i j : Fin 8) (n : ℕ) :
    (pairingB 2).root (bLabelEquiv j) - n • (pairingB 2).root (bLabelEquiv i)
      ∈ Set.range (pairingB 2).root ↔
    ∃ k : Fin 8, bCoordinates k = bCoordinates j - n • bCoordinates i :=
  coordinates_mem_b_root_range _

/-- The same cBot table, now derived for the actual swapped B2 roots. -/
theorem b_chain_bot (i : Fin 2) (j : Fin 8) :
    (pairingB 2).chainBotCoeff (bLabelEquiv (simpleLabelIndex i)) (bLabelEquiv j) =
      cBot i j := by
  by_cases hz : cBot i j = 0
  · rw [hz]
    apply (pairingB 2).chainBotCoeff_eq_zero_iff.mpr
    right
    have hn : ¬ ∃ k : Fin 8,
        bCoordinates k = bCoordinates j - 1 • bCoordinates (simpleLabelIndex i) := by
      fin_cases i <;> fin_cases j <;> norm_num [cBot] at hz <;> decide
    simpa only [one_smul] using (b_root_sub_mem (simpleLabelIndex i) j 1).not.mpr hn
  · have hdiff : (pairingB 2).root (bLabelEquiv (simpleLabelIndex i)) -
        (pairingB 2).root (bLabelEquiv j) ∈ Set.range (pairingB 2).root := by
      have hd : ∃ k : Fin 8,
          bCoordinates k = bCoordinates (simpleLabelIndex i) - 1 • bCoordinates j := by
        fin_cases i <;> fin_cases j <;> norm_num [cBot] at hz <;> decide
      simpa only [one_smul] using (b_root_sub_mem j (simpleLabelIndex i) 1).mpr hd
    have hi := (pairingB 2).linearIndependent_of_sub_mem_range_root' hdiff
    have hlo : cBot i j ≤
        (pairingB 2).chainBotCoeff (bLabelEquiv (simpleLabelIndex i)) (bLabelEquiv j) := by
      apply ((pairingB 2).root_sub_nsmul_mem_range_iff_le_chainBotCoeff hi).mp
      apply (b_root_sub_mem (simpleLabelIndex i) j (cBot i j)).mpr
      fin_cases i <;> fin_cases j <;> decide
    have hhi : ¬ cBot i j + 1 ≤
        (pairingB 2).chainBotCoeff (bLabelEquiv (simpleLabelIndex i)) (bLabelEquiv j) := by
      rw [← (pairingB 2).root_sub_nsmul_mem_range_iff_le_chainBotCoeff hi]
      apply (b_root_sub_mem (simpleLabelIndex i) j (cBot i j + 1)).not.mpr
      fin_cases i <;> fin_cases j <;> decide
    omega

theorem b_simple_label (i : Fin 2) :
    (baseBIndexEquiv 1 (bSimplePermutation i)).val = bLabelEquiv (simpleLabelIndex i) := by
  change simpleB 1 (bSimplePermutation i) = label (bLabelPermutation (simpleLabelIndex i))
  fin_cases i <;> apply Subtype.ext <;> decide

theorem b_neg_label (i : Fin 8) :
    let _ := (pairingB 2).indexNeg;
    -(bLabelEquiv i) = bLabelEquiv (oppositeLabel i) := by
  letI := (pairingB 2).indexNeg
  apply (pairingB 2).root.injective
  have he : (pairingB 2).root (-(bLabelEquiv i)) = -(pairingB 2).root (bLabelEquiv i) := by
    simp [RootPairing.indexNeg_neg]
  rw [he, b_root_label, b_root_label]
  fin_cases i <;> ext j <;> fin_cases j <;> decide

theorem b_reflection_self_label (i : Fin 8) :
    (pairingB 2).reflectionPerm (bLabelEquiv i) (bLabelEquiv i) =
      bLabelEquiv (oppositeLabel i) := by
  simpa only [RootPairing.indexNeg_neg] using b_neg_label i

theorem b_swapped_cartan (i j : Fin 2) :
    (baseB 1).cartanMatrix (baseBIndexEquiv 1 (bSimplePermutation i))
      (baseBIndexEquiv 1 (bSimplePermutation j)) = CartanMatrix.C 2 i j := by
  rw [baseB_cartan]
  fin_cases i <;> fin_cases j <;> decide

theorem b_chain_bot_zero (j : Fin 8) :
    (pairingB 2).chainBotCoeff (bLabelEquiv 0) (bLabelEquiv j) = cBot 0 j :=
  b_chain_bot 0 j

theorem b_chain_bot_one (j : Fin 8) :
    (pairingB 2).chainBotCoeff (bLabelEquiv 1) (bLabelEquiv j) = cBot 1 j :=
  b_chain_bot 1 j

/-- After actual root and Cartan-coordinate permutation the raising matrices agree. -/
theorem b2ActualRaising_zero : b2ActualRaising 0 = (ea : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [b2ActualRaising, b2IndexEquiv, c2_sum_split,
      RootPairing.GeckConstruction.e, b_simple_label, b_neg_label,
      b_reflection_self_label, bLabelEquiv.injective.eq_iff,
      b_chain_bot_zero, b_chain_bot_one, cBot, b_swapped_cartan,
      CartanMatrix.C, CartanMatrix.B, b_root_label, bCoordinates,
      bLabelPermutation, labelCoordinates, oppositeLabel, simpleLabelIndex,
      ea, Matrix.fromBlocks, funext_iff, Fin.forall_fin_succ] <;> decide

theorem b2ActualRaising_one : b2ActualRaising 1 = (eb : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [b2ActualRaising, b2IndexEquiv, c2_sum_split,
      RootPairing.GeckConstruction.e, b_simple_label, b_neg_label,
      b_reflection_self_label, bLabelEquiv.injective.eq_iff,
      b_chain_bot_zero, b_chain_bot_one, cBot, b_swapped_cartan,
      CartanMatrix.C, CartanMatrix.B, b_root_label, bCoordinates,
      bLabelPermutation, labelCoordinates, oppositeLabel, simpleLabelIndex,
      eb, Matrix.fromBlocks, funext_iff, Fin.forall_fin_succ] <;> decide

/-- Same actual integral raising operators; no ambient root-lattice equivalence. -/
theorem b2ActualRaising_eq_c2 (i : Fin 2) : b2ActualRaising i = c2ActualRaising i := by
  fin_cases i
  · exact b2ActualRaising_zero.trans c2ActualRaising_zero.symm
  · exact b2ActualRaising_one.trans c2ActualRaising_one.symm

end Atlas.Chevalley.Integral.RankTwo
