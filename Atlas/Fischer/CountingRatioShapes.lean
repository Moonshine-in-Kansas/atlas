import Atlas.Fischer.CountingSupportFibres
import Atlas.Fischer.CountingHexacodeScalarFibres

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem countingHexSupport_mem (h : countingHexacode) (i : Fin 6) :
    i ∈ countingHexSupport h ↔ h.val i ≠ 0 := by simp [countingHexSupport]

theorem countingHexSupport_smul (h : countingHexacode) (a : CountingFour) (ha : a ≠ 0) :
    countingHexSupport (a • h)=countingHexSupport h := by
  ext i
  simp [countingHexSupport,ha]

/-- Distinct support words with a common zero cannot repeat a ratio at two
common nonzero columns. This is the source's distance-four obstruction. -/
theorem countingHex_ratios_injective (g h : countingHexacode)
    (hne : countingHexSupport g ≠ countingHexSupport h)
    (k : Fin 6) (hgk : g.val k=0) (hhk : h.val k=0) :
    Function.Injective (fun i : ↥(countingHexSupport g ∩ countingHexSupport h) =>
      h.val i.val/g.val i.val) := by
  intro i j hr
  by_contra hij
  have hgn (a : ↥(countingHexSupport g ∩ countingHexSupport h)) : g.val a.val ≠ 0 :=
    (countingHexSupport_mem g a.val).mp (Finset.mem_inter.mp a.property).1
  have hhn (a : ↥(countingHexSupport g ∩ countingHexSupport h)) : h.val a.val ≠ 0 :=
    (countingHexSupport_mem h a.val).mp (Finset.mem_inter.mp a.property).2
  have hijv : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  have hik : i.val ≠ k := fun he => hgn i (he ▸ hgk)
  have hjk : j.val ≠ k := fun he => hgn j (he ▸ hgk)
  have he := countingHex_equal_ratios g h i.val j.val k hijv hik hjk (hgn i) (hgn j) hgk hhk hr
  have ha : h.val i.val/g.val i.val ≠ 0 := div_ne_zero (hhn i) (hgn i)
  exact hne (by rw [he,countingHexSupport_smul g _ ha])

/-- For overlap two, the two ratios coincide by full Hermitian orthogonality. -/
theorem countingHex_ratios_overlap_two (g h : countingHexacode) (i j : Fin 6)
    (hij : i ≠ j) (hs : countingHexSupport g ∩ countingHexSupport h={i,j}) :
    h.val i/g.val i=h.val j/g.val j := by
  have hout (k : Fin 6) (hk : k ∉ countingHexSupport g ∩ countingHexSupport h) :
      h.val k/g.val k=0 := by
    by_cases hg : g.val k=0
    · simp [hg]
    · have hh : h.val k=0 := by
        by_contra hh
        exact hk (Finset.mem_inter.mpr ⟨(countingHexSupport_mem _ _).mpr hg,
          (countingHexSupport_mem _ _).mpr hh⟩)
      simp [hh]
  have he : (∑ k : Fin 6, h.val k/g.val k)=
      ∑ k ∈ countingHexSupport g ∩ countingHexSupport h, h.val k/g.val k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    exact hout k hk
  have hz := countingHex_ratio_sum h g
  rw [he,hs] at hz
  simp only [Finset.sum_insert,Finset.mem_singleton,hij,not_false_eq_true,
    Finset.sum_singleton] at hz
  have hchar : ∀ x y : CountingFour, x+y=0 → x=y := by decide
  exact hchar _ _ hz


/-- The ratio at a common nonzero column, as an actual nonzero field element. -/
def countingNonzeroRatio (g h : countingHexacode)
    (i : ↥(countingHexSupport g ∩ countingHexSupport h)) : {a : CountingFour // a ≠ 0} :=
  ⟨h.val i.val/g.val i.val,div_ne_zero
    ((countingHexSupport_mem h _).mp (Finset.mem_inter.mp i.property).2)
    ((countingHexSupport_mem g _).mp (Finset.mem_inter.mp i.property).1)⟩

/-- In the overlap-three case the three ratios are exactly all three nonzero letters. -/
theorem countingNonzeroRatio_bijective (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hh : hammingNorm h.val=4)
    (hi : (countingHexSupport g ∩ countingHexSupport h).card=3) :
    Function.Bijective (countingNonzeroRatio g h) := by
  have hne : countingHexSupport g ≠ countingHexSupport h := by
    intro he
    rw [← he,Finset.inter_self,countingHexSupport_card,hg] at hi
    contradiction
  have hu : (countingHexSupport g ∪ countingHexSupport h).card=5 := by
    have hc := Finset.card_union_add_card_inter (countingHexSupport g) (countingHexSupport h)
    rw [countingHexSupport_card,countingHexSupport_card,hg,hh,hi] at hc
    omega
  have hkex : ∃ k : Fin 6, k ∉ countingHexSupport g ∪ countingHexSupport h := by
    by_contra he
    push_neg at he
    have huall : countingHexSupport g ∪ countingHexSupport h=Finset.univ := Finset.eq_univ_of_forall he
    rw [huall] at hu
    norm_num at hu
  obtain ⟨k,hk⟩ := hkex
  have hgk : g.val k=0 := by
    by_contra he
    exact hk (Finset.mem_union_left _ ((countingHexSupport_mem g k).mpr he))
  have hhk : h.val k=0 := by
    by_contra he
    exact hk (Finset.mem_union_right _ ((countingHexSupport_mem h k).mpr he))
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,?_⟩
  · intro i j he
    exact countingHex_ratios_injective g h hne k hgk hhk (congrArg Subtype.val he)
  · rw [Fintype.card_coe,hi,Fintype.card_subtype]
    rw [Finset.filter_ne',Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,
      Atlas.Algebra.goldenFour_card]

end Atlas.Fischer

