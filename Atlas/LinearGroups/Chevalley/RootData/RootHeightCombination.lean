import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionExchange

/-! Integral root-height and word-transport identities for rank-two descent.
These concern the actual root pairing, without a Coxeter presentation. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Height is additive on any integral combination which is again a root. -/
theorem root_height_zsmul_add (i j k : ι) (a c : ℤ)
    (hk : P.root k = a • P.root i + c • P.root j) :
    b.height k = a * b.height i + c * b.height j := by
  obtain ⟨f, _, _, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, _, _, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l ∈ b.support, (a • f + c • g) l • P.root l := by
    simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc,
      Finset.sum_add_distrib, ← Finset.smul_sum, ← hf, ← hg, hk]
  simp only [RootPairing.Base.height_eq_sum hf, RootPairing.Base.height_eq_sum hg,
    RootPairing.Base.height_eq_sum hfg, Pi.add_apply, Pi.smul_apply,
    Finset.sum_add_distrib, Finset.smul_sum, smul_eq_mul, Finset.mul_sum]

/-- Every actual simple-reflection word preserves integral root relations. -/
theorem simpleReflectionWord_root_zsmul_add (l : List b.support) (i j k : ι) (a c : ℤ)
    (hk : P.root k = a • P.root i + c • P.root j) :
    P.root (simpleReflectionWord P b l k) =
      a • P.root (simpleReflectionWord P b l i) +
        c • P.root (simpleReflectionWord P b l j) := by
  induction l with
  | nil => simpa only [simpleReflectionWord_nil, Equiv.Perm.one_apply] using hk
  | cons t l ih =>
    simp only [simpleReflectionWord_cons, Equiv.Perm.mul_apply, P.root_reflectionPerm]
    rw [ih, map_add, map_smul, map_smul]

/-- A nonzero positive combination of two roots with negative images also
has negative image under the same actual word. -/
theorem simpleReflectionWord_not_isPos_of_combination
    (l : List b.support) (i j k : ι) (a c : ℤ)
    (hk : P.root k = a • P.root i + c • P.root j)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : 0 < a + c)
    (hi : ¬ b.IsPos (simpleReflectionWord P b l i))
    (hj : ¬ b.IsPos (simpleReflectionWord P b l j)) :
    ¬ b.IsPos (simpleReflectionWord P b l k) := by
  have he := root_height_zsmul_add P b
    (simpleReflectionWord P b l i) (simpleReflectionWord P b l j)
    (simpleReflectionWord P b l k) a c
    (simpleReflectionWord_root_zsmul_add P b l i j k a c hk)
  rw [b.isPos_iff] at hi hj ⊢
  have hni := b.height_ne_zero (simpleReflectionWord P b l i)
  have hnj := b.height_ne_zero (simpleReflectionWord P b l j)
  have hai : b.height (simpleReflectionWord P b l i) ≤ -1 := by omega
  have hcj : b.height (simpleReflectionWord P b l j) ≤ -1 := by omega
  have h1 := mul_le_mul_of_nonneg_left hai ha
  have h2 := mul_le_mul_of_nonneg_left hcj hc
  nlinarith

end Atlas.Chevalley.RootData
