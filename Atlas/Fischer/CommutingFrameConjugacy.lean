import Atlas.Fischer.StandardCommutingFrame

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Maximal commuting subsets of the actual distinguished involution class. -/
abbrev IsFischerFrame (F : Set rootGeneratedRayGroup) : Prop :=
  Atlas.GroupTheory.IsCommutingFrame (Set.range distinguishedRootElement) F

private theorem distinguished_conj_image (g : rootGeneratedRayGroup) :
    (MulAut.conj g) '' Set.range distinguishedRootElement = Set.range distinguishedRootElement := by
  have hf (g : rootGeneratedRayGroup) (x : rootGeneratedRayGroup)
      (hx : x ∈ Set.range distinguishedRootElement) :
      MulAut.conj g x ∈ Set.range distinguishedRootElement := by
    obtain ⟨i,rfl⟩ := hx
    obtain ⟨j,hj⟩ := displayedRayOfParameter_surjective (g.val (displayedRayOfParameter i))
    exact ⟨j,(distinguishedRootElement_conjugation g i j hj.symm).symm⟩
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩; exact hf g y hy
  · intro x hx
    refine ⟨MulAut.conj g⁻¹ x, hf g⁻¹ x hx, ?_⟩
    change g * (g⁻¹*x*(g⁻¹)⁻¹) * g⁻¹ = x
    simp [mul_assoc]

private theorem distinguished_square (x : rootGeneratedRayGroup)
    (hx : x ∈ Set.range distinguishedRootElement) : x^2=1 := by
  obtain ⟨i,rfl⟩ := hx
  exact orderOf_dvd_iff_pow_eq_one.mp (by rw [distinguishedRootElement_order])

private theorem distinguished_product_alternatives (x : rootGeneratedRayGroup)
    (hx : x ∈ Set.range distinguishedRootElement) (y : rootGeneratedRayGroup)
    (hy : y ∈ Set.range distinguishedRootElement) : (x*y)^2=1 ∨ orderOf (x*y)=3 := by
  obtain ⟨i,rfl⟩ := hx
  obtain ⟨j,rfl⟩ := hy
  by_cases hij : i=j
  · subst j
    left
    rw [← pow_two, distinguished_square _ ⟨i,rfl⟩, one_pow]
  · have hp := distinguishedRootElement_product_order i j hij
    split_ifs at hp with h
    · exact Or.inr hp
    · exact Or.inl (orderOf_dvd_iff_pow_eq_one.mp (by rw [hp]))

/-- Actual Fischer-frame conjugacy, proved without the Fischer group order. -/
theorem fischerFrames_conjugate (F K : Set rootGeneratedRayGroup)
    (hF : IsFischerFrame F) (hK : IsFischerFrame K) :
    ∃ g : rootGeneratedRayGroup, (MulAut.conj g) '' F = K :=
  Atlas.GroupTheory.commutingFrames_conjugate _ F K distinguished_square
    distinguished_product_alternatives distinguished_conj_image hF hK

/-- Every actual frame is a conjugate of the marked basic frame. -/
theorem fischerFrame_standard_conjugate (F : Set rootGeneratedRayGroup)
    (hF : IsFischerFrame F) :
    ∃ g : rootGeneratedRayGroup, (MulAut.conj g) '' standardCommutingFrame = F :=
  fischerFrames_conjugate _ F standardCommutingFrame_isFrame hF

theorem standardCommutingFrame_card : Nat.card standardCommutingFrame = 24 := by
  have hi : Function.Injective (fun i : Omega => distinguishedRootElement (.inl i)) := by
    intro i j h
    exact Sum.inl.inj (distinguishedRootElement_injective h)
  unfold standardCommutingFrame
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  rw [Nat.card_eq_fintype_card]; rfl

/-- The24-element frame size follows from conjugacy and the marked construction. -/
theorem fischerFrame_card (F : Set rootGeneratedRayGroup) (hF : IsFischerFrame F) :
    Nat.card F = 24 := by
  obtain ⟨g,hg⟩ := fischerFrame_standard_conjugate F hF
  rw [← hg]
  rw [← Nat.card_congr (Equiv.Set.image (MulAut.conj g) standardCommutingFrame (MulAut.conj g).injective)]
  exact standardCommutingFrame_card

end Atlas.Fischer
