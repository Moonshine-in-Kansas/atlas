import Atlas.Rudvalis.OrthogonalCrossCount

namespace Atlas.Rudvalis

noncomputable def orthogonalPairSpace : SubMulAction gaussianLatticeGroup (MinimalCross×MinimalCross) where
  carrier := {z | CrossOrthogonal z.1 z.2}
  smul_mem' g z hz := (crossOrthogonal_gaussian g z.1 z.2).mpr hz

noncomputable abbrev OrthogonalPairs := orthogonalPairSpace

noncomputable def orthogonalPairsEquiv : OrthogonalPairs ≃ Σ x : MinimalCross,OrthogonalCrosses x where
  toFun z := ⟨z.val.1,z.val.2,z.prop⟩
  invFun z := ⟨(z.1,z.2.val),z.2.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem orthogonalPairs_card_of_uniform
    (h : ∀x : MinimalCross,Nat.card (OrthogonalCrosses x)=1755) :
    Nat.card OrthogonalPairs=7125300 := by
  classical
  let : Fintype MinimalCross := Fintype.ofFinite _
  rw [Nat.card_congr orthogonalPairsEquiv,Nat.card_sigma]
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,rudvalisLattice_minimal_cross_card]

end Atlas.Rudvalis
