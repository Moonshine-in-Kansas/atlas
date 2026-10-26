import Atlas.LinearGroups.Chevalley.RootData.G2ParabolicRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.ParabolicPoincareFactor

/-! The actual G2 Poincare sum is [2]_q [6]_q, obtained from its six-point
orbit and rank-one stabilizer. No Weyl group order or degree formula is assumed. -/
noncomputable section
namespace Atlas.Chevalley.G2Parabolic
open Classical RootData

private theorem word_in_rankOne_values (l : List G2Data.base.support)
    (hl : ∀ i ∈ l, i ∈ J) :
    rootWeylWord G2Data.pairing G2Data.base l = 1 ∨
      rootWeylWord G2Data.pairing G2Data.base l =
        simpleWeylReflection G2Data.pairing G2Data.base (simple 1) := by
  induction l with
  | nil => exact Or.inl rfl
  | cons i l ih =>
    have hi : i = simple 1 := Finset.mem_singleton.mp (hl i List.mem_cons_self)
    subst i
    rcases ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) with h | h
    · right
      change simpleWeylReflection G2Data.pairing G2Data.base (simple 1) *
        rootWeylWord G2Data.pairing G2Data.base l = _
      rw [h, mul_one]
    · left
      change simpleWeylReflection G2Data.pairing G2Data.base (simple 1) *
        rootWeylWord G2Data.pairing G2Data.base l = _
      rw [h, simpleWeylReflection_mul_self]

def rankOneMap (k : Fin 2) : rootParabolicSubgroup G2Data.pairing G2Data.base J :=
  if k = 0 then ⟨1, (rootParabolicSubgroup G2Data.pairing G2Data.base J).one_mem⟩
  else ⟨simpleWeylReflection G2Data.pairing G2Data.base (simple 1),
    Subgroup.subset_closure ⟨simple 1, Finset.mem_singleton_self _, rfl⟩⟩

theorem rankOneMap_length (k : Fin 2) :
    rootWeylLength G2Data.pairing G2Data.base (rankOneMap k).val = k.val := by
  fin_cases k
  · change rootWeylLength G2Data.pairing G2Data.base 1 = 0
    exact rootWeylLength_one G2Data.pairing G2Data.base
  · change rootWeylLength G2Data.pairing G2Data.base
      (simpleWeylReflection G2Data.pairing G2Data.base (simple 1)) = 1
    have h := rootWeylLength_mul_simple_of_positive G2Data.pairing G2Data.base 1
      (simple 1) (G2Data.base.isPos_of_mem_support (simple 1).property)
    simpa only [one_mul, rootWeylLength_one, Nat.zero_add] using h

theorem rankOneMap_bijective : Function.Bijective rankOneMap := by
  constructor
  · intro k l h
    apply Fin.ext
    have he := congrArg (fun v : rootParabolicSubgroup G2Data.pairing G2Data.base J =>
      rootWeylLength G2Data.pairing G2Data.base v.val) h
    simpa only [rankOneMap_length] using he
  · intro v
    obtain ⟨l, hl, he⟩ :=
      (rootParabolic_mem_iff_word G2Data.pairing G2Data.base J v.val).mp v.property
    rcases word_in_rankOne_values l hl with h | h
    · refine ⟨0, Subtype.ext ?_⟩
      change 1 = v.val
      exact h.symm.trans he
    · refine ⟨1, Subtype.ext ?_⟩
      change simpleWeylReflection G2Data.pairing G2Data.base (simple 1) = v.val
      exact h.symm.trans he

def rankOneEquiv : Fin 2 ≃ rootParabolicSubgroup G2Data.pairing G2Data.base J :=
  Equiv.ofBijective rankOneMap rankOneMap_bijective

local instance : Fintype W := Fintype.ofFinite _
local instance : Fintype (rootParabolicRepresentatives G2Data.pairing G2Data.base J) := by
  unfold rootParabolicRepresentatives
  exact Fintype.ofFinite _
local instance : Fintype (rootParabolicSubgroup G2Data.pairing G2Data.base J) := Fintype.ofFinite _

theorem representatives_length_sum (q : ℕ) :
    (∑ x : rootParabolicRepresentatives G2Data.pairing G2Data.base J,
      q ^ rootWeylLength G2Data.pairing G2Data.base x.val) =
        ∑ k : Fin 6, q ^ k.val := by
  rw [← representativeEquiv.sum_comp
    (fun x => q ^ rootWeylLength G2Data.pairing G2Data.base x.val)]
  simp only [representativeEquiv_length]

theorem rankOne_length_sum (q : ℕ) :
    (∑ v : rootParabolicSubgroup G2Data.pairing G2Data.base J,
      q ^ rootWeylLength G2Data.pairing G2Data.base v.val) =
        ∑ k : Fin 2, q ^ k.val := by
  rw [← rankOneEquiv.sum_comp
    (fun v => q ^ rootWeylLength G2Data.pairing G2Data.base v.val)]
  change (∑ k : Fin 2,
    q ^ rootWeylLength G2Data.pairing G2Data.base (rankOneMap k).val) = _
  simp only [rankOneMap_length]

/-- The two G2 degree factors are derived from actual root-permutation cosets. -/
theorem rootWeylPoincareEval_g2 (q : ℕ) :
    rootWeylPoincareEval G2Data.pairing G2Data.base q =
      (∑ k : Fin 2, q ^ k.val) * (∑ k : Fin 6, q ^ k.val) := by
  rw [rootWeylPoincareEval_parabolic_factor G2Data.pairing G2Data.base J,
    representatives_length_sum, rankOne_length_sum, mul_comm]

end Atlas.Chevalley.G2Parabolic
