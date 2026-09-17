import Atlas.Fischer.CubicCommonNeighborDistribution

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev CubicSourcePairNeighbors (i j k : Fin 6) (a b : ℕ) :=
  {t : CountingSourceParameters //
    (countingSourceColumn t i).card + (countingSourceColumn t j).card = a ∧
    (countingSourceColumn t i).card + (countingSourceColumn t k).card = b}

def cubicSourceMixedEquiv (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CubicSourcePairNeighbors i j k 0 4 ≃ CubicSourceCommonNeighbors k i j 4 :=
  Equiv.subtypeEquiv (Equiv.refl _) (by
    rintro (a | (b | c)) <;> simp only [Equiv.refl_apply]
    · rw [cubicSourceCommonCondition_A]
      simp only [Equiv.refl_apply, countingSourceColumn_card_A]
      split_ifs <;> simp_all
    · rw [cubicSourceCommonCondition_B]
      simp only [Equiv.refl_apply, countingSourceColumn_card_B]
      split_ifs <;> norm_num
    · rw [cubicSourceCommonCondition_C k i j 4 c (Ne.symm hik) (Ne.symm hjk) hij]
      simp only [Equiv.refl_apply, countingSourceColumn_card_C]
      split_ifs <;> norm_num)

theorem cubicSourceMixed_card (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (CubicSourcePairNeighbors i j k 0 4) = 3 := by
  rw [Nat.card_congr (cubicSourceMixedEquiv i j k hij hik hjk)]
  exact cubicSourceCommonFour_card k i j (Ne.symm hik) (Ne.symm hjk) hij

def cubicSourceBothZeroEquiv (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    {S : Finset (Fin 6) // S ∈ ({i,j,k}ᶜ : Finset (Fin 6)).powersetCard 2} ≃
      CubicSourcePairNeighbors i j k 0 0 :=
  Equiv.ofBijective (fun S => ⟨.inl ⟨S.val,(Finset.mem_powersetCard.mp S.property).2⟩,by
    have hs := (Finset.mem_powersetCard.mp S.property).1
    have hi : i ∉ S.val := by intro h; have := hs h; simpa using this
    have hj : j ∉ S.val := by intro h; have := hs h; simpa using this
    have hk : k ∉ S.val := by intro h; have := hs h; simpa using this
    simp [countingSourceColumn_card_A,hi,hj,hk]⟩) (by
    constructor
    · intro S T h
      apply Subtype.ext
      exact congrArg (fun t : CountingSourceParameters =>
        match t with | .inl a => a.val | _ => ∅) (congrArg Subtype.val h)
    · rintro ⟨a | (b | c),h⟩
      · have hi : i ∉ a.val := by
          intro hi
          have hh := h.1
          simp only [countingSourceColumn_card_A,if_pos hi] at hh
          omega
        have hj : j ∉ a.val := by
          intro hj
          have hh := h.1
          simp only [countingSourceColumn_card_A,if_pos hj] at hh
          omega
        have hk : k ∉ a.val := by
          intro hk
          have hh := h.2
          simp only [countingSourceColumn_card_A,if_pos hk] at hh
          omega
        refine ⟨⟨a.val,Finset.mem_powersetCard.mpr ⟨?_,a.property⟩⟩,rfl⟩
        intro x hx
        simp only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨fun he => hi (he ▸ hx),fun he => hj (he ▸ hx),fun he => hk (he ▸ hx)⟩
      · have hh := h.1
        simp only [countingSourceColumn_card_B] at hh
        have hh' := h.2
        simp only [countingSourceColumn_card_B] at hh'
        have hi : b.1.val.val i = 0 := by split_ifs at hh <;> simp_all
        have hj : b.1.val.val j = 0 := by split_ifs at hh <;> simp_all
        have hk : b.1.val.val k = 0 := by split_ifs at hh' <;> simp_all
        have hs : countingHexSupport b.1.val ⊆ ({i,j,k}ᶜ : Finset (Fin 6)) := by
          intro x hx
          have hn : b.1.val.val x ≠ 0 := by simpa [countingHexSupport] using hx
          simp only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or]
          exact ⟨fun he => hn (he.symm ▸ hi),fun he => hn (he.symm ▸ hj),fun he => hn (he.symm ▸ hk)⟩
        have hc := Finset.card_le_card hs
        rw [countingHexSupport_card,b.1.property,Finset.card_compl,Fintype.card_fin] at hc
        have ht : ({i,j,k} : Finset (Fin 6)).card = 3 := by simp [hij,hik,hjk]
        rw [ht] at hc
        omega
      · have hh := h.1
        simp only [countingSourceColumn_card_C] at hh
        split_ifs at hh <;> omega)

theorem cubicSourceBothZero_card (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (CubicSourcePairNeighbors i j k 0 0) = 3 := by
  rw [← Nat.card_congr (cubicSourceBothZeroEquiv i j k hij hik hjk),
    Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_powersetCard,
    Finset.card_compl,Fintype.card_fin]
  have ht : ({i,j,k} : Finset (Fin 6)).card = 3 := by simp [hij,hik,hjk]
  rw [ht]
  decide

end Atlas.Fischer

