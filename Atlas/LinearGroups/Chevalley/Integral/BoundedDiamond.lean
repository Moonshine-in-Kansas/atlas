/-
Adapted from mathlib RootSystem/GeckConstruction/Lemmas.lean and Finite/G2.lean.
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in mathlib's LICENSE.
Authors: Oliver Nash; explicit local-bound adaptation by ATLAS contributors.
-/
import Atlas.LinearGroups.Chevalley.Integral.LocalDiamondCommutation
import Atlas.LinearGroups.Chevalley.Integral.DiamondLengthObstruction

/-! Explicit local-bound replacement. Pairing bounds are explicit integer
inequalities, not the IsNotG2 class (which would import irreducibility).
The hard local configuration is excluded by invariant-form balance rather
than a global theorem about the number of root lengths. -/
noncomputable section
namespace Atlas.Chevalley.Integral
open RootPairing Set
open FaithfulSMul (algebraMap_injective)
variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]

def BoundedPairings : Prop := ∀ i j : ι, -2 ≤ P.pairingIn ℤ i j ∧ P.pairingIn ℤ i j ≤ 2

variable (hb : BoundedPairings P)
include hb

lemma bounded_chain_length (i j : ι) : P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 2 := by
  by_cases h : LinearIndependent ℤ ![P.root i, P.root j]
  · have hp := (hb (P.chainTopIdx i j) i).2
    have he := P.chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h
    omega
  · simp [P.chainTopCoeff_of_not_linearIndependent h, P.chainBotCoeff_of_not_linearIndependent h]

lemma bounded_pairing_nonpos_of_add {i j : ι} (h : P.root i + P.root j ∈ range P.root) :
    P.pairingIn ℤ i j ≤ 0 := by
  have aux₁ := P.linearIndependent_of_add_mem_range_root' (add_comm (P.root i) (P.root j) ▸ h)
  have aux₂ := bounded_chain_length P hb j i
  have aux₃ : 1 ≤ P.chainTopCoeff j i := by
    rwa [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff aux₁, one_smul]
  rw [← P.chainBotCoeff_sub_chainTopCoeff aux₁]
  omega

lemma bounded_pairing_nonneg_of_sub {i j : ι} (h : P.root i - P.root j ∈ range P.root) :
    0 ≤ P.pairingIn ℤ i j := by
  have h' : P.root i + P.root (P.reflectionPerm j j) ∈ range P.root := by
    simpa [← sub_eq_add_neg] using h
  simpa using bounded_pairing_nonpos_of_add P hb h'

lemma bounded_chainBot_if {i j : ι} (h : P.root i + P.root j ∈ range P.root) :
    P.chainBotCoeff i j = if P.pairingIn ℤ i j = 0 then 1 else 0 := by
  have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  have aux₁ := P.linearIndependent_of_add_mem_range_root' h
  have aux₂ := bounded_chain_length P hb i j
  have aux₃ := P.one_le_chainTopCoeff_of_root_add_mem h
  rcases eq_or_ne (P.chainBotCoeff i j) (P.chainTopCoeff i j) with aux₄ | aux₄ <;>
    simp_rw [P.pairingIn_eq_zero_iff (i := i) (j := j),
      ← P.chainBotCoeff_sub_chainTopCoeff aux₁, sub_eq_zero, Nat.cast_inj, aux₄, reduceIte] <;>
    omega

variable {b : P.Base} {i j k l m : ι}
include hb
private lemma diamond_aux0
    (hik_mem : P.root k + P.root i ∈ range P.root) :
    P.pairingIn ℤ k i = 0 ∨ (P.pairingIn ℤ k i < 0 ∧ P.chainBotCoeff i k = 0) := by
  have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  have := bounded_pairing_nonpos_of_add P hb hik_mem
  rw [add_comm] at hik_mem
  rw [bounded_chainBot_if P hb hik_mem, ite_eq_right_iff, P.pairingIn_eq_zero_iff (i := i)]
  lia

variable (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j)
  (h₁ : P.root k + P.root i = P.root l)
  (h₂ : P.root k - P.root j = P.root m)
  (h₃ : P.root k + P.root i - P.root j ∈ range P.root)
include hi hj hij h₁ h₂ h₃
private lemma diamond_aux1
    (hki : P.pairingIn ℤ k i = 0) :
    have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
    letI := P.indexNeg
    P.root i + P.root m ∈ range P.root → P.root j + P.root (-l) ∈ range P.root →
      P.root j + P.root (-k) ∈ range P.root →
      (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
        (P.chainBotCoeff j (-l) + 1) * (P.chainBotCoeff i k + 1) := by
  intro _ him_mem hjl_mem hjk_mem
  /- Setup some typeclasses and name the 6th root `n`. -/
  let := P.indexNeg
  have : IsAddTorsionFree M := .of_isTorsionFree ℤ M
  obtain ⟨n, hn⟩ := h₃
  /- Establish basic relationships about roots and their sums / differences. -/
  have hnk_ne : n ≠ k := by rintro rfl; simp [sub_eq_zero, hij, add_sub_assoc] at hn
  have hkj_ne : k ≠ j ∧ P.root k ≠ -P.root j := (IsReduced.linearIndependent_iff _).mp <|
    P.linearIndependent_of_sub_mem_range_root <| h₂ ▸ mem_range_self m
  have hnk_notMem : P.root n - P.root k ∉ range P.root := by
    convert! b.sub_notMem_range_root hi hj using 2; rw [hn]; module
  /- Calculate some auxiliary relationships between root pairings. -/
  have aux₀ : P.pairingIn ℤ j i = - P.pairingIn ℤ m i := by
    suffices P.pairing j i = - P.pairing m i from
      algebraMap_injective ℤ ℤ <| by simpa only [algebraMap_pairingIn, map_neg]
    replace hki : P.pairing k i = 0 := by rw [← P.algebraMap_pairingIn ℤ, hki, map_zero]
    simp only [← root_coroot_eq_pairing, ← h₂]
    simp [hki]
  have aux₁ : P.pairingIn ℤ j i = 0 := by
    refine le_antisymm (b.pairingIn_le_zero_of_ne hij.symm hj hi) ?_
    rw [aux₀, neg_nonneg]
    refine bounded_pairing_nonpos_of_add P hb ⟨n, ?_⟩
    rw [hn, ← h₂]
    abel
  /- Calculate the pairings between four key root pairs. -/
  have key₁ : P.pairingIn ℤ i k = 0 := by rwa [pairingIn_eq_zero_iff]
  have key₂ : P.pairingIn ℤ i m = 0 := P.pairingIn_eq_zero_iff.mp <| by simpa [aux₁] using aux₀
  have key₃ : P.pairingIn ℤ j k = 2 := by
    suffices 2 ≤ P.pairingIn ℤ j k by have := hb j k; grind
    have hn₁ : P.pairingIn ℤ n k = 2 + P.pairingIn ℤ i k - P.pairingIn ℤ j k := by
      apply algebraMap_injective ℤ ℤ
      simp only [map_add, map_sub, algebraMap_pairingIn, ← root_coroot_eq_pairing, hn]
      simp
    have hn₂ : P.pairingIn ℤ n k ≤ 0 := by
      by_contra! contra; exact hnk_notMem <| P.root_sub_root_mem_of_pairingIn_pos contra hnk_ne
    lia
  have key₄ : P.pairingIn ℤ l j = 1 := by
    have hij : P.pairing i j = 0 := by
      rw [pairing_eq_zero_iff, ← P.algebraMap_pairingIn ℤ, aux₁, map_zero]
    have hkj : P.pairing k j = 1 := by
      rw [← P.algebraMap_pairingIn ℤ]
      have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' j k (by grind) (by grind)
      aesop
    apply algebraMap_injective ℤ ℤ
    rw [algebraMap_pairingIn, ← root_coroot_eq_pairing, ← h₁]
    simp [hkj, hij]
  replace key₄ : P.pairingIn ℤ j l ≠ 0 := by rw [ne_eq, P.pairingIn_eq_zero_iff]; lia
  /- Calculate the value of each of the four terms in the goal. -/
  have hik_mem : P.root i + P.root k ∈ range P.root := ⟨l, by rw [← h₁, add_comm]⟩
  simp only [bounded_chainBot_if P hb, hik_mem, him_mem, hjl_mem, hjk_mem]
  simp [key₁, key₂, key₃, key₄]

private lemma diamond_aux2
    (hki' : P.pairingIn ℤ k i < 0) (hkj' : 0 < P.pairingIn ℤ k j) :
    have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
    letI := P.indexNeg
    P.root i + P.root m ∈ range P.root → P.root j + P.root (-l) ∈ range P.root →
      P.root j + P.root (-k) ∈ range P.root →
      ¬ (P.chainBotCoeff i m = 1 ∧ P.chainBotCoeff j (-l) = 0) := by
  intro _ him_mem hjl_mem hjk_mem
  let := P.indexNeg
  /- Setup some typeclasses. -/
  have : IsAddTorsionFree M := .of_isTorsionFree ℤ M
  /- Establish basic relationships about roots and their sums / differences. -/
  have hkj_ne : k ≠ j ∧ P.root k ≠ -P.root j := (IsReduced.linearIndependent_iff _).mp <|
    P.linearIndependent_of_sub_mem_range_root <| h₂ ▸ mem_range_self m
  have hlj_mem : P.root l - P.root j ∈ range P.root := by rwa [← h₁]
  /- It is sufficient to prove that two key pairings vanish. -/
  suffices ¬ (P.pairingIn ℤ m i = 0 ∧ P.pairingIn ℤ l j ≠ 0) by
    contrapose this
    rcases ne_or_eq (P.pairingIn ℤ m i) 0 with hmi | hmi
    · simpa [hmi, this.1, P.pairingIn_eq_zero_iff (i := i)] using bounded_chainBot_if P hb him_mem
    refine ⟨hmi, fun hlj ↦ ?_⟩
    rw [bounded_chainBot_if P hb hjl_mem] at this
    simp [P.pairingIn_eq_zero_iff (i := j), hlj] at this
  /- Assume for contradiction that the two pairings do not vanish. -/
  rintro ⟨hmi, hlj⟩
  /- Use the assumptions to calculate various relationships between root pairings. -/
  have aux₀ : P.pairingIn ℤ j i = P.pairingIn ℤ k i := by
    suffices P.pairing j i = P.pairing k i from
      algebraMap_injective ℤ ℤ <| by simpa only [algebraMap_pairingIn]
    replace h₂ : P.root k = P.root j + P.root m := (add_eq_of_eq_sub' h₂.symm).symm
    simpa [← P.root_coroot_eq_pairing k, h₂, ← P.algebraMap_pairingIn ℤ]
  obtain ⟨aux₁, aux₂⟩ : P.pairingIn ℤ i j = -1 ∧ P.pairingIn ℤ k j = 2 := by
    suffices 0 < - P.pairingIn ℤ i j ∧ - P.pairingIn ℤ i j < P.pairingIn ℤ k j ∧
      P.pairingIn ℤ k j ≤ 2 by lia
    refine ⟨?_, ?_, ?_⟩
    · rwa [neg_pos, P.pairingIn_lt_zero_iff, aux₀]
    · suffices P.pairingIn ℤ l j = P.pairingIn ℤ i j + P.pairingIn ℤ k j by
        have := bounded_pairing_nonneg_of_sub P hb hlj_mem; lia
      suffices P.pairing l j = P.pairing i j + P.pairing k j from
        algebraMap_injective ℤ ℤ <| by simpa only [algebraMap_pairingIn, map_add]
      simp [← P.root_coroot_eq_pairing l, ← h₁, add_comm]
    · have := hb k j
      grind
  /- Local replacement: no global two-root-length or irreducibility theorem. -/
  exact diamond_length_obstruction P i j k aux₁ aux₂ aux₀
    (fun h => hkj_ne.1 (P.root.injective h)) hkj_ne.2

theorem diamond_products_bounded :
    (P.chainBotCoeff i m + 1) * (P.chainTopCoeff j k + 1) =
      (P.chainTopCoeff j l + 1) * (P.chainBotCoeff i k + 1) := by
  /- Setup some typeclasses. -/
  let := P.indexNeg
  suffices (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
      (P.chainBotCoeff j (-l) + 1) * (P.chainBotCoeff i k + 1) by simpa
  /- Establish basic relationships about roots and their sums / differences. -/
  have him_mem : P.root i + P.root m ∈ range P.root := by rw [← h₂]; convert! h₃ using 1; abel
  have hik_mem : P.root k + P.root i ∈ range P.root := h₁ ▸ mem_range_self l
  have hjk_mem : P.root j + P.root (-k) ∈ range P.root := by
    convert! mem_range_self (-m) using 1; simpa [sub_eq_add_neg] using congr(-$h₂)
  have hjl_mem : P.root j + P.root (-l) ∈ range P.root := by
    rw [h₁, ← neg_mem_range_root_iff] at h₃; convert! h₃ using 1; simp [sub_eq_add_neg]
  have h₁' : P.root (-k) - P.root i = P.root (-l) := by
    simp only [root_reflectionPerm, reflection_apply_self, indexNeg_neg]; rw [← h₁]; abel
  have h₂' : P.root (-k) + P.root j = P.root (-m) := by
    simp only [root_reflectionPerm, reflection_apply_self, indexNeg_neg]; rw [← h₂]; abel
  have h₃' : P.root (-k) + P.root j - P.root i ∈ range P.root := by grind
  /- Proceed to the main argument, following Geck's case splits. It's all just bookkeeping. -/
  rcases diamond_aux0 P hb hik_mem with hki | ⟨hki, hik⟩
  · /- Geck "Case 1" -/
    exact diamond_aux1 P hb hi hj hij h₁ h₂ h₃ hki him_mem hjl_mem hjk_mem
  rw [add_comm] at hik_mem hjk_mem
  rcases diamond_aux0 P hb hjk_mem with hkj | ⟨hkj, hjk⟩
  · /- Geck "Case 2" -/
    simpa only [neg_neg] using (diamond_aux1 P hb hj hi hij.symm h₂' h₁' h₃' hkj hjl_mem
      (by simpa only [neg_neg]) (by simpa only [neg_neg])).symm
  /- Geck "Case 3" -/
  suffices P.chainBotCoeff i m = P.chainBotCoeff j (-l) by rw [hik, hjk, this]
  have aux₁ : ¬ (P.chainBotCoeff i m = 1 ∧ P.chainBotCoeff j (-l) = 0) :=
    diamond_aux2 P hb hi hj hij h₁ h₂ h₃ hki (by simpa using hkj) him_mem hjl_mem <| by rwa [add_comm]
  have aux₂ : ¬(P.chainBotCoeff j (-l) = 1 ∧ P.chainBotCoeff i m = 0) := by
    simpa using diamond_aux2 P hb hj hi hij.symm h₂' h₁' h₃' hkj (by simpa)
      hjl_mem (by simpa only [neg_neg]) (by simpa only [neg_neg])
  have aux₃ : P.chainBotCoeff i m = 0 ∨ P.chainBotCoeff i m = 1 := by
    have := bounded_chainBot_if P hb him_mem
    split at this <;> simp [this]
  have aux₄ : P.chainBotCoeff j (-l) = 0 ∨ P.chainBotCoeff j (-l) = 1 := by
    have := bounded_chainBot_if P hb hjl_mem
    split at this <;> simp only [this, true_or, or_true]
  lia


omit hi hj hij h₁ h₂ h₃ in
/-- Actual local diamond property under explicit bounds, ready for concrete
B/C/F4 providers. No irreducibility predicate is among the hypotheses. -/
theorem simpleDiamondProducts_of_boundedPairings (b : P.Base) : SimpleDiamondProducts P b := by
  intro i j hij k l m h₁ h₂ h₃
  exact diamond_products_bounded P hb i.property j.property
    (fun h => hij (Subtype.ext h)) h₁ h₂ h₃

end Atlas.Chevalley.Integral
