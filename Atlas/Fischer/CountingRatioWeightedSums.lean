import Atlas.Fischer.CountingRatioTableCases

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
attribute [local instance] Classical.propDecidable

/-- The constant-ratio rows of the source table hold for arbitrary weights. -/
theorem countingRatioOnes_constant_sum (g h : countingHexacode)
    (hh : hammingNorm h.val=4) (r : CountingFour) (hr0 : r≠0)
    (hr : ∀ i ∈ countingHexSupport g ∩ countingHexSupport h, h.val i/g.val i=r)
    (f : Finset (Fin 6) → ℕ) :
    (∑ w : {w : countingHexacode // countingHexSupport w=countingHexSupport h},
      f (countingRatioOnes g w.val))=
        f (countingHexSupport g ∩ countingHexSupport h)+2*f ∅ := by
  rw [← Equiv.sum_comp (countingSupportScalarEquiv h hh) (fun w => f (countingRatioOnes g w.val))]
  have he (a : {a : CountingFour // a≠0}) :
      countingRatioOnes g ((countingSupportScalarEquiv h hh) a).val=
        if a.val*r=1 then countingHexSupport g ∩ countingHexSupport h else ∅ :=
    countingRatioOnes_constant g h a.val a.property r hr
  simp_rw [he,apply_ite]
  rw [Finset.sum_ite]
  obtain ⟨hc1,hc2⟩ := countingRatio_scalar_multiplicities r hr0
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype] at hc1 hc2
  simp only [Finset.sum_const,hc1,hc2,nsmul_eq_mul,one_mul]
  simp

/-- The three overlap-three words are parametrized by their unique matching column. -/
def countingRatioSingletonEquiv (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hh : hammingNorm h.val=4)
    (hi : (countingHexSupport g ∩ countingHexSupport h).card=3) :
    ↥(countingHexSupport g ∩ countingHexSupport h) ≃
      {w : countingHexacode // countingHexSupport w=countingHexSupport h} :=
  Equiv.ofBijective (fun i => ⟨(g.val i.val/h.val i.val) • h,
    countingHexSupport_smul h _ (div_ne_zero
      ((countingHexSupport_mem g _).mp (Finset.mem_inter.mp i.property).1)
      ((countingHexSupport_mem h _).mp (Finset.mem_inter.mp i.property).2))⟩) (by
    have hinj : Function.Injective (fun i : ↥(countingHexSupport g ∩ countingHexSupport h) =>
        h.val i.val/g.val i.val) := by
      intro i j he
      exact (countingNonzeroRatio_bijective g h hg hh hi).injective (Subtype.ext he)
    have he (i : ↥(countingHexSupport g ∩ countingHexSupport h)) :
        countingRatioOnes g ((g.val i.val/h.val i.val) • h)={i.val} :=
      countingRatioOnes_singleton g h hinj i
    constructor
    · intro i j hij
      apply Subtype.ext
      apply Finset.singleton_injective
      exact (he i).symm.trans ((congrArg (fun w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} => countingRatioOnes g w.val) hij).trans (he j))
    · intro w
      obtain ⟨a,ha⟩ := (countingSupportScalarEquiv h hh).surjective w
      obtain ⟨i,hi0,_⟩ := countingRatioOnes_three_singleton g h hg hh hi a.val a.property
      have hai := (countingRatioOnes_singleton_iff g h hinj i a.val a.property).mp hi0
      refine ⟨i,?_⟩
      apply Subtype.ext
      change (g.val i.val/h.val i.val) • h=w.val
      rw [← hai]
      exact congrArg Subtype.val ha)

theorem countingRatioSingletonEquiv_ratio (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hh : hammingNorm h.val=4)
    (hi : (countingHexSupport g ∩ countingHexSupport h).card=3)
    (i : ↥(countingHexSupport g ∩ countingHexSupport h)) :
    countingRatioOnes g (countingRatioSingletonEquiv g h hg hh hi i).val={i.val} := by
  change countingRatioOnes g ((g.val i.val/h.val i.val) • h)={i.val}
  apply countingRatioOnes_singleton
  intro j k he
  exact (countingNonzeroRatio_bijective g h hg hh hi).injective (Subtype.ext he)

/-- The overlap-three row has exactly one actual word for each singleton,
with arbitrary weights retained. -/
theorem countingRatioOnes_three_sum (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hh : hammingNorm h.val=4)
    (hi : (countingHexSupport g ∩ countingHexSupport h).card=3)
    (f : Finset (Fin 6) → ℕ) :
    (∑ w : {w : countingHexacode // countingHexSupport w=countingHexSupport h},
      f (countingRatioOnes g w.val))=
        ∑ i ∈ countingHexSupport g ∩ countingHexSupport h, f {i} := by
  rw [← Equiv.sum_comp (countingRatioSingletonEquiv g h hg hh hi)
    (fun w => f (countingRatioOnes g w.val))]
  simp_rw [countingRatioSingletonEquiv_ratio]
  rw [Finset.sum_coe_sort_eq_attach]
  exact Finset.sum_attach _ (fun i => f {i})

/-- Every pair of actual weight-four supports is in one of the three ratio rows. -/
theorem countingRatioOnes_sum (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hh : hammingNorm h.val=4)
    (f : Finset (Fin 6) → ℕ) :
    (∑ w : {w : countingHexacode // countingHexSupport w=countingHexSupport h},
      f (countingRatioOnes g w.val))=
      if (countingHexSupport g ∩ countingHexSupport h).card=3 then
        ∑ i ∈ countingHexSupport g ∩ countingHexSupport h, f {i}
      else f (countingHexSupport g ∩ countingHexSupport h)+2*f ∅ := by
  by_cases hi : (countingHexSupport g ∩ countingHexSupport h).card=3
  · rw [if_pos hi]
    exact countingRatioOnes_three_sum g h hg hh hi f
  rw [if_neg hi]
  have hcg : (countingHexSupport g).card=4 := hg
  have hch : (countingHexSupport h).card=4 := hh
  have hub : (countingHexSupport g ∪ countingHexSupport h).card≤6 :=
    (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
  have hib : (countingHexSupport g ∩ countingHexSupport h).card≤4 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by rw [hcg])
  have hsum := Finset.card_inter_add_card_union (countingHexSupport g) (countingHexSupport h)
  have hcases : (countingHexSupport g ∩ countingHexSupport h).card=2 ∨
      (countingHexSupport g ∩ countingHexSupport h).card=4 := by omega
  obtain ⟨r,hr0,hr⟩ : ∃ r : CountingFour, r≠0 ∧
      ∀ i ∈ countingHexSupport g ∩ countingHexSupport h, h.val i/g.val i=r := by
    rcases hcases with hc | hc
    · exact countingHex_ratios_two_constant g h hc
    · have hsg : countingHexSupport g ∩ countingHexSupport h=countingHexSupport g :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hc,hcg])
      have hsh : countingHexSupport g ∩ countingHexSupport h=countingHexSupport h :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hc,hch])
      exact countingHex_ratios_same_support g h hg (hsg.symm.trans hsh)
  exact countingRatioOnes_constant_sum g h hh r hr0 hr f

end Atlas.Fischer

