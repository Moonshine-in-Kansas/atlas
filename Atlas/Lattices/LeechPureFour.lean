import Atlas.Lattices.LeechTwoFourRecovery

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def emptyTwoFourEquiv (U : Finset Omega) (hu : (U.card : Bit) = 0) :
    TwoFourSigns ∅ U ≃ (U → Bit) where
  toFun p := p.2
  invFun t := ⟨⟨fun i => False.elim (Finset.notMem_empty i.val i.prop),by simpa using hu.symm⟩,t⟩
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact False.elim (Finset.notMem_empty i.val i.prop)
    · rfl
  right_inv _ := rfl

theorem emptyTwoFourSigns_card (U : Finset Omega) (hu : (U.card : Bit) = 0) :
    Nat.card (TwoFourSigns ∅ U) = 2 ^ U.card := by
  rw [Nat.card_congr (emptyTwoFourEquiv U hu)]
  simp [Nat.card_eq_fintype_card,ZMod.card]

theorem pureFourParameters_card (u : ℕ) (hu : (u : Bit) = 0) :
    Nat.card (TwoFourParameters 0 u) = Nat.choose 24 u * 2 ^ u := by
  rw [Nat.card_sigma]
  have hh (T : CodeSupports 0) :
      Nat.card ((U : OutsideSupports T.val u) × TwoFourSigns T.val U.val) = Nat.choose 24 u * 2 ^ u := by
    have ht : T.val = ∅ := Finset.card_eq_zero.mp T.prop.2
    rw [Nat.card_sigma]
    have hs (U : OutsideSupports T.val u) : Nat.card (TwoFourSigns T.val U.val) = 2 ^ u := by
      simpa only [ht,U.prop.2] using emptyTwoFourSigns_card U.val (by simpa [U.prop.2] using hu)
    simp_rw [hs]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card,outsideSupports_card,ht]
    simp
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card,codeSupports_card,golay_weight_distribution]
  norm_num

theorem pureFourFamily_card (u : ℕ) (hu : (u : Bit) = 0) :
    (twoFourFamily 0 u).card = Nat.choose 24 u * 2 ^ u := by
  rw [twoFourFamily,Finset.card_image_of_injective _ (twoFourFamilyVector_injective 0 u),
    Finset.card_univ,← Nat.card_eq_fintype_card,pureFourParameters_card u hu]

theorem pureFour_shape_counts :
    (twoFourFamily 0 2).card = 1104 ∧ (twoFourFamily 0 4).card = 170016 := by
  rw [pureFourFamily_card 2 (by decide),pureFourFamily_card 4 (by decide)]
  norm_num [Nat.choose]

end Atlas.Lattices
