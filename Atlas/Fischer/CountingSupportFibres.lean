import Atlas.Fischer.CountingHexacodeSupports
import Atlas.Fischer.CountingSourceMaskCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The actual nonzero-column support in the source F4 code. -/
def countingHexSupport (h : countingHexacode) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => h.val i ≠ 0)

theorem countingHexSupport_card (h : countingHexacode) :
    (countingHexSupport h).card=hammingNorm h.val := rfl

/-- Exactly three source hexacode words have any prescribed four-column support. -/
theorem countingHexSupport_fiber_card (S : Finset (Fin 6)) (hS : S.card=4) :
    Nat.card {h : countingHexacode // countingHexSupport h=S}=3 := by
  have hc : Sᶜ.card=2 := by rw [Finset.card_compl,hS]; decide
  obtain ⟨i,j,hij,hcomp⟩ := Finset.card_eq_two.mp hc
  have hs (k : Fin 6) : k ∈ S ↔ ¬(k=i ∨ k=j) := by
    have h : k ∉ S ↔ k=i ∨ k=j := by
      rw [← Finset.mem_compl,hcomp]
      simp
    simpa using not_congr h
  have hn (h : countingHexacode) (hh : countingHexSupport h=S) : h ≠ 0 := by
    intro hz
    subst h
    have hc := congrArg Finset.card hh
    simp [countingHexSupport,hS] at hc
  let f : {h : countingHexDoubleZero i j // h ≠ 0} ≃
      {h : countingHexacode // countingHexSupport h=S} :=
    { toFun := fun h => ⟨h.val.val,by
        ext k
        simp only [countingHexSupport,Finset.mem_filter,Finset.mem_univ,true_and]
        simp only [ne_eq,countingHexDoubleZero_nonzero_support i j hij h.val h.property,hs]⟩
      invFun := fun h => ⟨⟨h.val,by
        have hz (k : Fin 6) (hk : k=i ∨ k=j) : h.val.val k=0 := by
          by_contra he
          have hm : k ∈ countingHexSupport h.val := by simp [countingHexSupport,he]
          rw [h.property] at hm
          exact (hs k).mp hm hk
        exact ⟨hz i (Or.inl rfl),hz j (Or.inr rfl)⟩⟩,
        by intro he; exact hn h.val h.property (congrArg Subtype.val he)⟩
      left_inv := by intro h; rfl
      right_inv := by intro h; rfl }
  rw [← Nat.card_congr f,countingHexDoubleZero_nonzero_card i j hij]

/-- The twenty-four actual Type B parameters over each four-column support. -/
theorem countingSourceTypeB_support_card (S : Finset (Fin 6)) (hS : S.card=4) :
    Nat.card {t : CountingSourceTypeB // countingHexSupport t.1.val=S}=24 := by
  let p := fun h : {h : countingHexacode // hammingNorm h.val=4} =>
    {e : P6 // ∀ i : Fin 6, h.val.val i=0 → e.val i=0}
  rw [Nat.card_congr (Equiv.subtypeSigmaEquiv p (fun h => countingHexSupport h.val=S))]
  rw [Nat.card_sigma]
  have hm (h : {h : {h : countingHexacode // hammingNorm h.val=4} //
      countingHexSupport h.val=S}) : Nat.card (p h.val)=8 :=
    countingSourceMask_card h.val.val h.val.property
  simp only [hm,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have he : {h : {h : countingHexacode // hammingNorm h.val=4} // countingHexSupport h.val=S} ≃
      {h : countingHexacode // countingHexSupport h=S} :=
    Equiv.subtypeSubtypeEquivSubtype
      (p := fun h : countingHexacode => hammingNorm h.val=4)
      (q := fun h : countingHexacode => countingHexSupport h=S) (by
      intro h hh
      rw [← countingHexSupport_card,hh,hS])
  rw [← Nat.card_eq_fintype_card,Nat.card_congr he,countingHexSupport_fiber_card S hS]

end Atlas.Fischer
