import Atlas.GroupTheory.ThreeTranspositionFrames
import Atlas.Fischer.RootRayClassInterface
import Atlas.Fischer.BasicSupportSeparation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual twenty-four marked distinguished involutions. -/
def standardCommutingFrame : Set rootGeneratedRayGroup :=
  Set.range (fun i : Omega => distinguishedRootElement (.inl i))

theorem distinguishedRoot_commute_nonzero (i j : ReflectingRootParameter)
    (hc : Commute (distinguishedRootElement i) (distinguishedRootElement j)) :
    hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j) ≠ 0 := by
  intro hz
  have hij : i ≠ j := by
    intro h
    subst j
    have hh := (reflectingRootParameter_isReflectingRoot i).1.1
    rw [hz] at hh
    norm_num at hh
  have hp := distinguishedRootElement_product_order i j hij
  rw [if_pos hz] at hp
  have hs : (distinguishedRootElement i * distinguishedRootElement j)^2=1 := by
    rw [hc.mul_pow]
    have hi := orderOf_dvd_iff_pow_eq_one.mp (show orderOf (distinguishedRootElement i) ∣ 2 by
      rw [distinguishedRootElement_order])
    have hj := orderOf_dvd_iff_pow_eq_one.mp (show orderOf (distinguishedRootElement j) ∣ 2 by
      rw [distinguishedRootElement_order])
    rw [hi,hj,one_mul]
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [hp] at hd
  norm_num at hd

theorem standardCommutingFrame_isFrame :
    Atlas.GroupTheory.IsCommutingFrame (Set.range distinguishedRootElement) standardCommutingFrame := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨i,rfl⟩; exact ⟨.inl i,rfl⟩
  · rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    by_cases hij : i=j
    · subst j; exact Commute.refl _
    have hh : hermitian (basicAxis i) (basicAxis j)^3=1 := by
      rw [hermitian_basicAxis_basicAxis, if_neg hij]; norm_num
    have hc := displayedRootRay_unit_commute (.inl i) (.inl j) hh
    change distinguishedRootElement (.inl i) * distinguishedRootElement (.inl j) = _
    apply Subtype.ext
    exact hc
  · intro E hE hc hsub
    apply Set.Subset.antisymm _ hsub
    intro x hx
    obtain ⟨t,rfl⟩ := hE hx
    obtain ⟨j,rfl⟩ := displayedRoot_full_basic_support t (fun i =>
      distinguishedRoot_commute_nonzero (.inl i) t
        (hc _ (hsub ⟨i,rfl⟩) _ hx))
    exact ⟨j,rfl⟩

end Atlas.Fischer
