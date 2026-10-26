import Atlas.LinearGroups.Chevalley.Integral.WeylTransportedHeight

/-! The same integral divided powers decrease transported height when the
transformed simple root is negative. All division occurs over the integers
in the established divided-power construction, before arbitrary base change. -/
noncomputable section
namespace Atlas.Chevalley.Integral
open RootData

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

theorem raisingDividedOver_eq_zero_of_neg_wordHeight_le
    (l : List b.support) (i : b.support)
    (hi : ¬ b.IsPos (simpleReflectionWord P b l i.val))
    (n : ℕ) (hn : 0 < n) (row col : b.support ⊕ ι)
    (hheight : -geckWordHeight P b l row ≤ -geckWordHeight P b l col) :
    raisingDividedOver P b R i n row col = 0 := by
  have hd0 : ¬ 0 < b.height (simpleReflectionWord P b l i.val) := by
    simpa only [b.isPos_iff] using hi
  have hdn := b.height_ne_zero (simpleReflectionWord P b l i.val)
  have hd : b.height (simpleReflectionWord P b l i.val) < 0 := by omega
  have hz : raisingDividedPower P b i n row col = 0 := by
    by_contra hne
    have he := raisingDividedPower_wordHeight_weightedSupport P b l i n row col hne
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hnd := mul_neg_of_pos_of_neg hn' hd
    omega
  simp only [raisingDividedOver, Matrix.map_apply, hz, map_zero]

theorem raisingExponential_neg_wordHeightUnitriangular
    (l : List b.support) (i : b.support)
    (hi : ¬ b.IsPos (simpleReflectionWord P b l i.val)) (t : R) :
    Atlas.Matrix.HeightUnitriangular (fun a => -geckWordHeight P b l a)
      (raisingExponential P b R i t) := by
  intro row col hheight
  have h1 := raisingDividedOver_eq_zero_of_neg_wordHeight_le P b R l i hi 1
    (by decide) row col hheight
  have h2 := raisingDividedOver_eq_zero_of_neg_wordHeight_le P b R l i hi 2
    (by decide) row col hheight
  have h3 := raisingDividedOver_eq_zero_of_neg_wordHeight_le P b R l i hi 3
    (by decide) row col hheight
  rw [raisingDividedOver_one] at h1
  simp [raisingExponential_expansion, Matrix.add_apply, Matrix.smul_apply, h1, h2, h3]

end Atlas.Chevalley.Integral
