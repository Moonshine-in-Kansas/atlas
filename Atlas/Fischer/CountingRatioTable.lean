import Atlas.Fischer.CountingRatioShapes

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
attribute [local instance] Classical.propDecidable

/-- Scalar parametrization of all three actual words on a weight-four support. -/
def countingSupportScalarEquiv (h : countingHexacode) (hh : hammingNorm h.val=4) :
    {a : CountingFour // a ≠ 0} ≃
      {w : countingHexacode // countingHexSupport w=countingHexSupport h} :=
  Equiv.ofBijective (fun a => ⟨a.val • h,countingHexSupport_smul h a.val a.property⟩) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_,?_⟩
    · intro a b he
      have hn : h ≠ 0 := by intro hz; subst h; simp at hh
      apply Subtype.ext
      exact smul_left_injective CountingFour hn (congrArg Subtype.val he)
    · rw [Fintype.card_subtype,Finset.filter_ne',
        Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,goldenFour_card]
      rw [← Nat.card_eq_fintype_card,countingHexSupport_fiber_card _
        (by rw [countingHexSupport_card,hh])])

/-- The source table set Z: columns where both words are nonzero and their ratio is one. -/
def countingRatioOnes (g h : countingHexacode) : Finset (Fin 6) :=
  (countingHexSupport g ∩ countingHexSupport h).filter (fun i => h.val i/g.val i=1)

/-- For a constant nonzero ratio on the overlap, scalar multiplication gives the
whole overlap for one scalar and the empty set for the other two. -/
theorem countingRatioOnes_constant (g h : countingHexacode) (a : CountingFour) (ha : a ≠ 0)
    (r : CountingFour) (hr : ∀ i ∈ countingHexSupport g ∩ countingHexSupport h,
      h.val i/g.val i=r) :
    countingRatioOnes g (a • h)=
      if a*r=1 then countingHexSupport g ∩ countingHexSupport h else ∅ := by
  ext i
  simp only [countingRatioOnes,countingHexSupport_smul h a ha,Finset.mem_filter,
    Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,mul_div_assoc]
  by_cases hi : i ∈ countingHexSupport g ∩ countingHexSupport h
  · rw [hr i hi]
    by_cases he : a*r=1 <;> simp [hi,he]
  · by_cases he : a*r=1 <;> simp [hi,he]

/-- The two scalar multiplicities in each constant-ratio row are one and two. -/
theorem countingRatio_scalar_multiplicities (r : CountingFour) (hr : r ≠ 0) :
    Nat.card {a : {a : CountingFour // a ≠ 0} // a.val*r=1}=1 ∧
      Nat.card {a : {a : CountingFour // a ≠ 0} // a.val*r ≠ 1}=2 := by
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  revert r
  decide

/-- With distinct ratios, a matching scalar selects exactly its matching column. -/
theorem countingRatioOnes_singleton (g h : countingHexacode)
    (hinj : Function.Injective (fun i : ↥(countingHexSupport g ∩ countingHexSupport h) =>
      h.val i.val/g.val i.val))
    (i : ↥(countingHexSupport g ∩ countingHexSupport h)) :
    countingRatioOnes g ((g.val i.val/h.val i.val) • h)={i.val} := by
  have hg := (countingHexSupport_mem g i.val).mp (Finset.mem_inter.mp i.property).1
  have hh := (countingHexSupport_mem h i.val).mp (Finset.mem_inter.mp i.property).2
  have ha : g.val i.val/h.val i.val ≠ 0 := div_ne_zero hg hh
  ext j
  simp only [countingRatioOnes,countingHexSupport_smul h _ ha,Finset.mem_filter,
    Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,mul_div_assoc,Finset.mem_singleton]
  constructor
  · rintro ⟨hj,he⟩
    have hm : (g.val i.val/h.val i.val)*(h.val i.val/g.val i.val)=1 := by field_simp
    have hr : h.val j/g.val j=h.val i.val/g.val i.val :=
      mul_left_cancel₀ ha (he.trans hm.symm)
    exact congrArg Subtype.val (hinj (a₁ := ⟨j,hj⟩) (a₂ := i) hr)
  · intro hj
    subst j
    refine ⟨i.property,?_⟩
    field_simp


/-- The complete 1/2 multiplicity assertion among the three actual words on a
fixed four-support, when their common-column ratio is constant. -/
theorem countingRatioOnes_constant_card (g h : countingHexacode)
    (hh : hammingNorm h.val=4) (hn : (countingHexSupport g ∩ countingHexSupport h).Nonempty)
    (r : CountingFour) (hr0 : r ≠ 0)
    (hr : ∀ i ∈ countingHexSupport g ∩ countingHexSupport h, h.val i/g.val i=r) :
    Nat.card {w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} //
      countingRatioOnes g w.val=countingHexSupport g ∩ countingHexSupport h}=1 ∧
    Nat.card {w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} //
      countingRatioOnes g w.val=∅}=2 := by
  have hi : countingHexSupport g ∩ countingHexSupport h ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hn
  let f := countingSupportScalarEquiv h hh
  have he (a : {a : CountingFour // a ≠ 0}) :
      countingRatioOnes g (f a).val=
        if a.val*r=1 then countingHexSupport g ∩ countingHexSupport h else ∅ :=
    countingRatioOnes_constant g h a.val a.property r hr
  have f1 : {a : {a : CountingFour // a ≠ 0} // a.val*r=1} ≃
      {w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} //
        countingRatioOnes g w.val=countingHexSupport g ∩ countingHexSupport h} :=
    Equiv.subtypeEquiv f (by intro a; rw [he]; by_cases h : a.val*r=1 <;> simp [h,hi,Ne.symm hi])
  have f2 : {a : {a : CountingFour // a ≠ 0} // a.val*r ≠ 1} ≃
      {w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} //
        countingRatioOnes g w.val=∅} :=
    Equiv.subtypeEquiv f (by intro a; rw [he]; split_ifs <;> simp_all)
  rw [← Nat.card_congr f1,← Nat.card_congr f2]
  exact countingRatio_scalar_multiplicities r hr0


/-- Same-support words have one constant nonzero ratio. -/
theorem countingHex_ratios_same_support (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hs : countingHexSupport g=countingHexSupport h) :
    ∃ r : CountingFour, r ≠ 0 ∧ ∀ i ∈ countingHexSupport g ∩ countingHexSupport h,
      h.val i/g.val i=r := by
  obtain ⟨a,ha⟩ := (countingSupportScalarEquiv g hg).surjective ⟨h,hs.symm⟩
  have he : a.val • g=h := congrArg Subtype.val ha
  refine ⟨a.val,a.property,?_⟩
  intro i hi
  have hn := (countingHexSupport_mem g i).mp (Finset.mem_inter.mp hi).1
  rw [← he]
  change (a.val*g.val i)/g.val i=a.val
  rw [mul_div_assoc,div_self hn,mul_one]

/-- The full constant-ratio description for every overlap-two pair. -/
theorem countingHex_ratios_two_constant (g h : countingHexacode)
    (hs : (countingHexSupport g ∩ countingHexSupport h).card=2) :
    ∃ r : CountingFour, r ≠ 0 ∧ ∀ i ∈ countingHexSupport g ∩ countingHexSupport h,
      h.val i/g.val i=r := by
  obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp hs
  have hi : i ∈ countingHexSupport g ∩ countingHexSupport h := by rw [he]; simp
  have hgn := (countingHexSupport_mem g i).mp (Finset.mem_inter.mp hi).1
  have hhn := (countingHexSupport_mem h i).mp (Finset.mem_inter.mp hi).2
  refine ⟨h.val i/g.val i,div_ne_zero hhn hgn,?_⟩
  intro k hk
  rw [he] at hk
  simp only [Finset.mem_insert,Finset.mem_singleton] at hk
  rcases hk with hk | hk
  · rw [hk]
  · rw [hk]
    exact (countingHex_ratios_overlap_two g h i j hij he).symm


/-- Every scalar multiple in the overlap-three row selects exactly one column. -/
theorem countingRatioOnes_three_singleton (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hh : hammingNorm h.val=4)
    (hi : (countingHexSupport g ∩ countingHexSupport h).card=3)
    (a : CountingFour) (ha : a ≠ 0) :
    ∃! i : ↥(countingHexSupport g ∩ countingHexSupport h),
      countingRatioOnes g (a • h)={i.val} := by
  have hb := countingNonzeroRatio_bijective g h hg hh hi
  obtain ⟨i,he⟩ := hb.surjective ⟨a⁻¹,inv_ne_zero ha⟩
  have hr : h.val i.val/g.val i.val=a⁻¹ := congrArg Subtype.val he
  have heq : g.val i.val/h.val i.val=a := by
    have hinv := congrArg (fun z : CountingFour => z⁻¹) hr
    simpa only [inv_div,inv_inv] using hinv
  have hinj : Function.Injective (fun j : ↥(countingHexSupport g ∩ countingHexSupport h) =>
      h.val j.val/g.val j.val) := by
    intro j k he
    exact hb.injective (Subtype.ext he)
  refine ⟨i,?_,?_⟩
  · rw [← heq]
    exact countingRatioOnes_singleton g h hinj i
  · intro j hj
    have hself : countingRatioOnes g (a • h)={i.val} := by
      rw [← heq]
      exact countingRatioOnes_singleton g h hinj i
    exact Subtype.ext (Finset.singleton_injective (hj.symm.trans hself))


/-- Distinct-ratio rows match a prescribed singleton for exactly its scalar. -/
theorem countingRatioOnes_singleton_iff (g h : countingHexacode)
    (hinj : Function.Injective (fun i : ↥(countingHexSupport g ∩ countingHexSupport h) =>
      h.val i.val/g.val i.val))
    (i : ↥(countingHexSupport g ∩ countingHexSupport h))
    (a : CountingFour) (ha : a ≠ 0) :
    countingRatioOnes g (a • h)={i.val} ↔ a=g.val i.val/h.val i.val := by
  have hg := (countingHexSupport_mem g i.val).mp (Finset.mem_inter.mp i.property).1
  have hh := (countingHexSupport_mem h i.val).mp (Finset.mem_inter.mp i.property).2
  constructor
  · intro he
    have hm : i.val ∈ countingRatioOnes g (a • h) := by rw [he]; simp
    have hr := (Finset.mem_filter.mp hm).2
    change (a*h.val i.val)/g.val i.val=1 at hr
    apply (eq_div_iff hh).mpr
    simpa only [one_mul] using (div_eq_iff hg).mp hr
  · intro he
    rw [he]
    exact countingRatioOnes_singleton g h hinj i

/-- The exact one-per-column multiplicity among actual words in the overlap-three row. -/
theorem countingRatioOnes_three_card (g h : countingHexacode)
    (hg : hammingNorm g.val=4) (hh : hammingNorm h.val=4)
    (hi : (countingHexSupport g ∩ countingHexSupport h).card=3)
    (i : ↥(countingHexSupport g ∩ countingHexSupport h)) :
    Nat.card {w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} //
      countingRatioOnes g w.val={i.val}}=1 := by
  have hb := countingNonzeroRatio_bijective g h hg hh hi
  have hinj : Function.Injective (fun j : ↥(countingHexSupport g ∩ countingHexSupport h) =>
      h.val j.val/g.val j.val) := by
    intro j k he
    exact hb.injective (Subtype.ext he)
  let r := g.val i.val/h.val i.val
  have hr : r ≠ 0 := div_ne_zero
    ((countingHexSupport_mem g _).mp (Finset.mem_inter.mp i.property).1)
    ((countingHexSupport_mem h _).mp (Finset.mem_inter.mp i.property).2)
  let f : {a : {a : CountingFour // a ≠ 0} // a.val=r} ≃
      {w : {w : countingHexacode // countingHexSupport w=countingHexSupport h} //
        countingRatioOnes g w.val={i.val}} :=
    Equiv.subtypeEquiv (countingSupportScalarEquiv h hh) (by
      intro a
      exact (countingRatioOnes_singleton_iff g h hinj i a.val a.property).symm)
  rw [← Nat.card_congr f,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he (a : {a : CountingFour // a ≠ 0}) : a.val=r ↔ a=⟨r,hr⟩ := by
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  simp only [he]
  rw [Finset.filter_eq',if_pos (Finset.mem_univ _),Finset.card_singleton]

end Atlas.Fischer




