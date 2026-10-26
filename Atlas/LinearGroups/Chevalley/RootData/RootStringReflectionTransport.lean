import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionGeneration
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Tactic.FinCases

/-! Source candidate: root-string bottom coefficients are invariant under
simultaneous reflection of the two root labels. No constructed group occurs. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Set
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]

private theorem reflection_pair_independent (k i j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    LinearIndependent ℤ ![P.root (P.reflectionPerm k i), P.root (P.reflectionPerm k j)] := by
  have hmap := h.map' (P.reflection k).toLinearMap
    (LinearMap.ker_eq_bot.mpr (P.reflection k).injective)
  have hvec : (P.reflection k).toLinearMap ∘ ![P.root i, P.root j] =
      ![P.root (P.reflectionPerm k i), P.root (P.reflectionPerm k j)] := by
    funext t
    fin_cases t <;> simp [P.root_reflectionPerm]
  simpa only [hvec] using hmap

private theorem reflection_mem_root_range (k : ι) (x : M) :
    P.reflection k x ∈ range P.root ↔ x ∈ range P.root := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨P.reflectionPerm k j, ?_⟩
    rw [P.root_reflectionPerm, hj, P.reflection_same]
  · rintro ⟨j, rfl⟩
    exact ⟨P.reflectionPerm k j, P.root_reflectionPerm k j⟩

/-- This includes the parallel pairs, where both coefficients have the
same pinned junk value zero. -/
theorem chainBotCoeff_reflection_both (k i j : ι) :
    P.chainBotCoeff (P.reflectionPerm k i) (P.reflectionPerm k j) =
      P.chainBotCoeff i j := by
  by_cases h : LinearIndependent ℤ ![P.root i, P.root j]
  · rw [P.chainBotCoeff_eq_sSup (reflection_pair_independent P k i j h),
      P.chainBotCoeff_eq_sSup h]
    congr 1
    ext n
    change P.root (P.reflectionPerm k j) - n • P.root (P.reflectionPerm k i) ∈
        range P.root ↔ P.root j - n • P.root i ∈ range P.root
    rw [P.root_reflectionPerm, P.root_reflectionPerm, ← map_nsmul, ← map_sub]
    exact reflection_mem_root_range P k _
  · have hn : ¬ LinearIndependent ℤ
        ![P.root (P.reflectionPerm k i), P.root (P.reflectionPerm k j)] := by
      intro hr
      have hh := reflection_pair_independent P k (P.reflectionPerm k i)
        (P.reflectionPerm k j) hr
      apply h
      simpa only [P.reflectionPerm_self] using hh
    rw [P.chainBotCoeff_of_not_linearIndependent hn,
      P.chainBotCoeff_of_not_linearIndependent h]

theorem chainBotCoeff_reflection_right (k i j : ι) :
    P.chainBotCoeff i (P.reflectionPerm k j) =
      P.chainBotCoeff (P.reflectionPerm k i) j := by
  simpa only [P.reflectionPerm_self] using
    chainBotCoeff_reflection_both P k (P.reflectionPerm k i) j

variable (b : P.Base)

theorem a2_reflected_simple_labels (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    P.reflectionPerm i j = P.reflectionPerm j i := by
  have hpij : P.pairingIn ℤ i j = -1 := hij
  have hpji : P.pairingIn ℤ j i = -1 := hji
  apply P.root.injective
  simp only [P.root_reflectionPerm, P.reflection_apply_root' ℤ,
    hpij, hpji, neg_one_smul, sub_neg_eq_add, add_comm]

theorem reflectionPerm_a2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    P.reflectionPerm i * P.reflectionPerm j * P.reflectionPerm i =
      P.reflectionPerm j * P.reflectionPerm i * P.reflectionPerm j := by
  calc
    _ = P.reflectionPerm (P.reflectionPerm i j) :=
      (reflectionPerm_conjugate P j i).symm
    _ = P.reflectionPerm (P.reflectionPerm j i) :=
      congrArg P.reflectionPerm (a2_reflected_simple_labels P b i j hij hji)
    _ = _ := reflectionPerm_conjugate P i j

end Atlas.Chevalley.RootData
