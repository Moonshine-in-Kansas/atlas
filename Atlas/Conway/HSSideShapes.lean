import Atlas.Conway.HSSideProfiles

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem hs_side_shape_coordinate (a : Omega) (t : Fin 5) (y : leech)
    (h : HSSideShape a t y) : y.val a = ![4,0,2,1,3] t := by
  fin_cases t
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,hy⟩ := h
    rw [hy]; simp [signedSupport,ha,hz]
  · obtain ⟨T,hT,ha,hy⟩ := h
    rw [hy]; simp [constantSupportVector,ha]
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,hy⟩ := h
    rw [hy]; simp [signedSupport,ha,hz]
  · obtain ⟨b,c,hb,hw,ha,hc,rfl⟩ := h
    simp [oddMinimumVector_apply,ha,Ne.symm hb]
  · obtain ⟨c,hw,ha,rfl⟩ := h
    simp [oddMinimumVector_apply,ha]

theorem hs_side_shape_unique (a : Omega) (s t : Fin 5) (y : leech)
    (hs : HSSideShape a s y) (ht : HSSideShape a t y) : s = t := by
  have h := (hs_side_shape_coordinate a s y hs).symm.trans (hs_side_shape_coordinate a t y ht)
  fin_cases s <;> fin_cases t <;> norm_num at *

theorem hs_side_shape_sound (a : Omega) (t : Fin 5) (y : leech)
    (h : HSSideShape a t y) :
    integerDot y.val y.val = 32 ∧ integerDot (normSixVector a).val y.val = 16 := by
  fin_cases t
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,hy⟩ := h
    constructor
    · rw [hy,scaled_signedSupport_norm,hT]; norm_num
    · rw [integerDot_normSix,hy,← Finset.mul_sum,signedSupport_sum]
      change 4*((T.card : ℤ)-2*supportNegativeCount T s)+4*(4*signedSupport T s a)=16
      rw [hn,hT]
      simp [signedSupport,ha,hz]
  · obtain ⟨T,hT,ha,hy⟩ := h
    constructor
    · rw [hy,constantSupport_norm,octad_size T hT]; norm_num
    · rw [integerDot_normSix,hy]
      simp [constantSupportVector,ha,octad_size T hT]
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,hy⟩ := h
    constructor
    · rw [hy,scaled_signedSupport_norm,octad_size T hT]; norm_num
    · rw [integerDot_normSix,hy,← Finset.mul_sum,signedSupport_sum]
      change 2*((T.card : ℤ)-2*supportNegativeCount T s)+4*(2*signedSupport T s a)=16
      rw [hn,octad_size T hT]
      simp [signedSupport,ha,hz]
  · obtain ⟨b,c,hb,hw,ha,hc,rfl⟩ := h
    refine ⟨((odd_minimal_shell_iff _).mpr (oddMinimumVector_mem _ _)).2.2,?_⟩
    rw [normSix_oddMinimum_dot]
    simp [hw,ha,hc,Ne.symm hb]
  · obtain ⟨c,hw,ha,rfl⟩ := h
    refine ⟨((odd_minimal_shell_iff _).mpr (oddMinimumVector_mem _ _)).2.2,?_⟩
    rw [normSix_oddMinimum_dot]
    simp [hw,ha]

end Atlas.Conway
