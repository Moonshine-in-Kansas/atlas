import Atlas.LinearGroups.Chevalley.RootData.SupportedRootWordLabels
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionBraids
import Atlas.LinearGroups.Chevalley.RootData.TwoDescentSuffixDihedral
import Atlas.LinearGroups.Chevalley.RootData.SimpleCartanCases

/-! Exhaustive positive-root enumeration inside two actual simple directions.
The literal alternating words have 2, 3, 4 or 6 labels. Inversion counts rule
out any additional positive roots in the same simple-coordinate support. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Every positive root supported on {i,j} appears in the length-2 word. -/
theorem rankTwo_rootWordLabels_two (i j : b.support)
    (hij : b.cartanMatrix i j = 0) (hji : b.cartanMatrix j i = 0) :
    IsReducedRootWord P b [i, j] ∧
      ∀ β, β ∈ rootWordLabels P b [i, j] ↔
        b.IsPos β ∧ (rootSimpleCoefficients P b β).support ⊆ {i, j} := by
  have hpij : P.pairing i.val j.val = 0 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, show P.pairingIn ℤ i.val j.val = 0 from hij]
    simp
  have hpji : P.pairing j.val i.val = 0 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, show P.pairingIn ℤ j.val i.val = 0 from hji]
    simp
  have hri : (rootWeylWord P b [i, j]).val i.val = P.reflectionPerm i.val i.val := by
    apply P.root.injective
    simp only [rootWeylWord_val, simpleReflectionWord_cons, simpleReflectionWord_nil,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root_reflectionPerm,
      P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same, hpij, hpji]
    module
  have hrj : (rootWeylWord P b [i, j]).val j.val = P.reflectionPerm j.val j.val := by
    apply P.root.injective
    simp only [rootWeylWord_val, simpleReflectionWord_cons, simpleReflectionWord_nil,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root_reflectionPerm,
      P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same, hpij, hpji]
    module
  have hi : ¬ b.IsPos ((rootWeylWord P b [i, j]).val i.val) := by
    rw [hri]
    exact not_isPos_reflection_simple P b i
  have hj : ¬ b.IsPos ((rootWeylWord P b [i, j]).val j.val) := by
    rw [hrj]
    exact not_isPos_reflection_simple P b j
  have hd : rootWeylLength P b
      (rootWeylWord P b [i, j] * rootWeylWord P b [i, j]) + 2 =
      rootWeylLength P b (rootWeylWord P b [i, j]) := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using
      rootWeylLength_two_descents_two P b (rootWeylWord P b [i, j]) i j hij hji hi hj
  rw [rootWeylWord_two_mul_self P b i j hij hji, rootWeylLength_one, zero_add] at hd
  have hred : IsReducedRootWord P b [i, j] := by
    simpa only [IsReducedRootWord, List.length_cons, List.length_nil] using hd.symm
  refine ⟨hred, rootWordLabels_mem_iff_positive_supported P b {i, j} [i, j] ?_ hred ?_⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · have he : k = j := Finset.mem_singleton.mp hk
      subst k
      exact hj

/-- Every positive root supported on {i,j} appears in the length-3 word. -/
theorem rankTwo_rootWordLabels_three (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    IsReducedRootWord P b [i, j, i] ∧
      ∀ β, β ∈ rootWordLabels P b [i, j, i] ↔
        b.IsPos β ∧ (rootSimpleCoefficients P b β).support ⊆ {i, j} := by
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, show P.pairingIn ℤ i.val j.val = -1 from hij]
    simp
  have hpji : P.pairing j.val i.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, show P.pairingIn ℤ j.val i.val = -1 from hji]
    simp
  have hri : (rootWeylWord P b [i, j, i]).val i.val = P.reflectionPerm j.val j.val := by
    apply P.root.injective
    simp only [rootWeylWord_val, simpleReflectionWord_cons, simpleReflectionWord_nil,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root_reflectionPerm,
      P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same, hpij, hpji]
    module
  have hrj : (rootWeylWord P b [i, j, i]).val j.val = P.reflectionPerm i.val i.val := by
    apply P.root.injective
    simp only [rootWeylWord_val, simpleReflectionWord_cons, simpleReflectionWord_nil,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root_reflectionPerm,
      P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same, hpij, hpji]
    module
  have hi : ¬ b.IsPos ((rootWeylWord P b [i, j, i]).val i.val) := by
    rw [hri]
    exact not_isPos_reflection_simple P b j
  have hj : ¬ b.IsPos ((rootWeylWord P b [i, j, i]).val j.val) := by
    rw [hrj]
    exact not_isPos_reflection_simple P b i
  have hd : rootWeylLength P b
      (rootWeylWord P b [i, j, i] * rootWeylWord P b [i, j, i]) + 3 =
      rootWeylLength P b (rootWeylWord P b [i, j, i]) := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using
      rootWeylLength_two_descents_three P b (rootWeylWord P b [i, j, i]) i j hij hji hi hj
  rw [rootWeylWord_three_mul_self P b i j, rootWeylLength_one, zero_add] at hd
  have hred : IsReducedRootWord P b [i, j, i] := by
    simpa only [IsReducedRootWord, List.length_cons, List.length_nil] using hd.symm
  refine ⟨hred, rootWordLabels_mem_iff_positive_supported P b {i, j} [i, j, i] ?_ hred ?_⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simp
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · have he : k = j := Finset.mem_singleton.mp hk
      subst k
      exact hj

/-- Every positive root supported on {i,j} appears in the length-4 word. -/
theorem rankTwo_rootWordLabels_four (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    IsReducedRootWord P b [i, j, i, j] ∧
      ∀ β, β ∈ rootWordLabels P b [i, j, i, j] ↔
        b.IsPos β ∧ (rootSimpleCoefficients P b β).support ⊆ {i, j} := by
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, show P.pairingIn ℤ i.val j.val = -1 from hij]
    simp
  have hpji : P.pairing j.val i.val = -2 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, show P.pairingIn ℤ j.val i.val = -2 from hji]
    simp
  have hri : (rootWeylWord P b [i, j, i, j]).val i.val = P.reflectionPerm i.val i.val := by
    apply P.root.injective
    simp only [rootWeylWord_val, simpleReflectionWord_cons, simpleReflectionWord_nil,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root_reflectionPerm,
      P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same, hpij, hpji]
    module
  have hrj : (rootWeylWord P b [i, j, i, j]).val j.val = P.reflectionPerm j.val j.val := by
    apply P.root.injective
    simp only [rootWeylWord_val, simpleReflectionWord_cons, simpleReflectionWord_nil,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root_reflectionPerm,
      P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same, hpij, hpji]
    module
  have hi : ¬ b.IsPos ((rootWeylWord P b [i, j, i, j]).val i.val) := by
    rw [hri]
    exact not_isPos_reflection_simple P b i
  have hj : ¬ b.IsPos ((rootWeylWord P b [i, j, i, j]).val j.val) := by
    rw [hrj]
    exact not_isPos_reflection_simple P b j
  have hd : rootWeylLength P b
      (rootWeylWord P b [i, j, i, j] * rootWeylWord P b [i, j, i, j]) + 4 =
      rootWeylLength P b (rootWeylWord P b [i, j, i, j]) := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using
      rootWeylLength_two_descents_four P b (rootWeylWord P b [i, j, i, j]) i j hij hji hi hj
  rw [rootWeylWord_four_mul_self P b i j hij hji, rootWeylLength_one, zero_add] at hd
  have hred : IsReducedRootWord P b [i, j, i, j] := by
    simpa only [IsReducedRootWord, List.length_cons, List.length_nil] using hd.symm
  refine ⟨hred, rootWordLabels_mem_iff_positive_supported P b {i, j} [i, j, i, j] ?_ hred ?_⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · have he : k = j := Finset.mem_singleton.mp hk
      subst k
      exact hj

/-- Every positive root supported on {i,j} appears in the length-6 word. -/
theorem rankTwo_rootWordLabels_six (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    IsReducedRootWord P b [i, j, i, j, i, j] ∧
      ∀ β, β ∈ rootWordLabels P b [i, j, i, j, i, j] ↔
        b.IsPos β ∧ (rootSimpleCoefficients P b β).support ⊆ {i, j} := by
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, show P.pairingIn ℤ i.val j.val = -1 from hij]
    simp
  have hpji : P.pairing j.val i.val = -3 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, show P.pairingIn ℤ j.val i.val = -3 from hji]
    simp
  have hri : (rootWeylWord P b [i, j, i, j, i, j]).val i.val = P.reflectionPerm i.val i.val := by
    apply P.root.injective
    simp only [rootWeylWord_val, simpleReflectionWord_cons, simpleReflectionWord_nil,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root_reflectionPerm,
      P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same, hpij, hpji]
    module
  have hrj : (rootWeylWord P b [i, j, i, j, i, j]).val j.val = P.reflectionPerm j.val j.val := by
    apply P.root.injective
    simp only [rootWeylWord_val, simpleReflectionWord_cons, simpleReflectionWord_nil,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root_reflectionPerm,
      P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing,
      P.pairing_same, hpij, hpji]
    module
  have hi : ¬ b.IsPos ((rootWeylWord P b [i, j, i, j, i, j]).val i.val) := by
    rw [hri]
    exact not_isPos_reflection_simple P b i
  have hj : ¬ b.IsPos ((rootWeylWord P b [i, j, i, j, i, j]).val j.val) := by
    rw [hrj]
    exact not_isPos_reflection_simple P b j
  have hd : rootWeylLength P b
      (rootWeylWord P b [i, j, i, j, i, j] * rootWeylWord P b [i, j, i, j, i, j]) + 6 =
      rootWeylLength P b (rootWeylWord P b [i, j, i, j, i, j]) := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using
      rootWeylLength_two_descents_six P b (rootWeylWord P b [i, j, i, j, i, j]) i j hij hji hi hj
  rw [rootWeylWord_six_mul_self P b i j hij hji, rootWeylLength_one, zero_add] at hd
  have hred : IsReducedRootWord P b [i, j, i, j, i, j] := by
    simpa only [IsReducedRootWord, List.length_cons, List.length_nil] using hd.symm
  refine ⟨hred, rootWordLabels_mem_iff_positive_supported P b {i, j} [i, j, i, j, i, j] ?_ hred ?_⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · have he : k = j := Finset.mem_singleton.mp hk
      subst k
      exact hj

/-- Every pair of distinct actual simple roots has an exhaustive positive-root
list of length 2, 3, 4 or 6, with long/short order changed when necessary. -/
theorem exists_rankTwo_rootWordLabels (i j : b.support) (hij : i ≠ j) :
    ∃ l : List b.support,
      (l.length = 2 ∨ l.length = 3 ∨ l.length = 4 ∨ l.length = 6) ∧
      IsReducedRootWord P b l ∧
      ∀ β, β ∈ rootWordLabels P b l ↔
        b.IsPos β ∧ (rootSimpleCoefficients P b β).support ⊆ {i, j} := by
  rcases cartanMatrix_pair_cases_of_ne P b i j hij with
    ⟨hab, hba⟩ | ⟨hab, hba⟩ | ⟨hab, hba⟩ |
    ⟨hab, hba⟩ | ⟨hab, hba⟩ | ⟨hab, hba⟩
  · exact ⟨[i, j], by simp, rankTwo_rootWordLabels_two P b i j hab hba⟩
  · exact ⟨[i, j, i], by simp, rankTwo_rootWordLabels_three P b i j hab hba⟩
  · exact ⟨[i, j, i, j], by simp, rankTwo_rootWordLabels_four P b i j hab hba⟩
  · refine ⟨[j, i, j, i], by simp, ?_⟩
    simpa only [Finset.pair_comm] using rankTwo_rootWordLabels_four P b j i hba hab
  · exact ⟨[i, j, i, j, i, j], by simp, rankTwo_rootWordLabels_six P b i j hab hba⟩
  · refine ⟨[j, i, j, i, j, i], by simp, ?_⟩
    simpa only [Finset.pair_comm] using rankTwo_rootWordLabels_six P b j i hba hab

end Atlas.Chevalley.RootData
