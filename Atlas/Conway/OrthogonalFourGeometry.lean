import Atlas.Conway.DisjointFourCount

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimumPairPlus_dot (i j : Omega) (x : IntegerCoordinates) :
    integerDot (minimumPairPlus i j).val x = 4 * (x i + x j) := by
  simp [minimumPairPlus,integerDot,coordinateVector,Pi.single_apply,add_mul,ite_mul,
    Finset.sum_add_distrib,mul_add]

theorem four_orthogonal_nonzero_pair (i j : Omega) (hij : i ≠ j) (x : leech)
    (hx : x.val ∈ twoFourFamily 0 2)
    (ho : integerDot (minimumPairPlus i j).val x.val = 0) (hi : x.val i ≠ 0) :
    x = minimumPairMinus i j ∨ x = -minimumPairMinus i j := by
  have he : x.val i + x.val j = 0 := by rw [minimumPairPlus_dot] at ho; omega
  have hj : x.val j ≠ 0 := by omega
  obtain ⟨T,hT,s,hs⟩ := minimum_four_parameterization x hx
  have hiT : i ∈ T := by
    by_contra hn
    exact hi (by rw [hs]; simp [signedSupport,hn])
  have hjT : j ∈ T := by
    by_contra hn
    exact hj (by rw [hs]; simp [signedSupport,hn])
  have hTpair : T = {i,j} := (Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hiT (Finset.singleton_subset_iff.mpr hjT)) (by simp [hT,hij])).symm
  have hxi : x.val i = 4 ∨ x.val i = -4 := by
    rw [hs]
    simp only [signedSupport,dif_pos hiT]
    split_ifs <;> norm_num
  have hz (k : Omega) (hki : k ≠ i) (hkj : k ≠ j) : x.val k = 0 := by
    rw [hs]
    have hk : k ∉ T := by simp [hTpair,hki,hkj]
    simp [signedSupport,hk]
  rcases hxi with hxi | hxi
  · left
    apply Subtype.ext
    funext k
    by_cases hki : k = i
    · subst k; simp [minimumPairMinus,coordinateVector,Pi.single_apply,hij,hxi]
    · by_cases hkj : k = j
      · subst k
        have hxj : x.val j = -4 := by omega
        simp [minimumPairMinus,coordinateVector,Pi.single_apply,hki,hxj]
      · simp [minimumPairMinus,coordinateVector,Pi.single_apply,hki,hkj,hz k hki hkj]
  · right
    apply Subtype.ext
    funext k
    change x.val k = -((minimumPairMinus i j).val k)
    by_cases hki : k = i
    · subst k; simp [minimumPairMinus,coordinateVector,Pi.single_apply,hij,hxi]
    · by_cases hkj : k = j
      · subst k
        have hxj : x.val j = 4 := by omega
        simp [minimumPairMinus,coordinateVector,Pi.single_apply,hki,hxj]
      · simp [minimumPairMinus,coordinateVector,Pi.single_apply,hki,hkj,hz k hki hkj]

theorem four_orthogonal_partition (i j : Omega) (hij : i ≠ j) (x : leech)
    (hx : x.val ∈ twoFourFamily 0 2)
    (ho : integerDot (minimumPairPlus i j).val x.val = 0) :
    (x = minimumPairMinus i j ∨ x = -minimumPairMinus i j) ∨
      (x.val i = 0 ∧ x.val j = 0) := by
  by_cases hi : x.val i = 0
  · right
    rw [minimumPairPlus_dot,hi] at ho
    exact ⟨hi,by omega⟩
  · exact Or.inl (four_orthogonal_nonzero_pair i j hij x hx ho hi)

end Atlas.Conway
