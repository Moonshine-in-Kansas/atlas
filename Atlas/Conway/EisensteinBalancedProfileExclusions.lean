import Atlas.Conway.EisensteinBalancedFrameProfile

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem eisensteinNormCount_capacity (x : EisensteinShell 6) (s : Finset ℤ) :
    ∑ n ∈ s,eisensteinNormCount x n ≤ 12 := by
  unfold eisensteinNormCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  exact (Finset.card_filter_le _ _).trans_eq (by decide)

/-- Balanced-heavy frames contain no vectors of the norm-nine-plus-hexad type. -/
theorem eisensteinBalancedFrame_no_nine (F : EisensteinFrame)
    (hF : F ∈ eisensteinBalancedFamily) (x : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors F) : eisensteinNormCount x 9=0 := by
  have h := eisensteinNormCount_capacity x {0,3,9,12}
  norm_num only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,
    Finset.sum_singleton,show (0 : ℤ)≠3 by decide,show (0 : ℤ)≠9 by decide,
    show (0 : ℤ)≠12 by decide,show (3 : ℤ)≠9 by decide,show (3 : ℤ)≠12 by decide,
    show (9 : ℤ)≠12 by decide,not_false_eq_true,or_false,or_self] at h
  have hp := eisensteinBalancedFrame_pattern F hF x hx
  rcases hp with ⟨h0,h3,h12⟩|⟨h0,h3⟩ <;> omega

end Atlas.Conway
