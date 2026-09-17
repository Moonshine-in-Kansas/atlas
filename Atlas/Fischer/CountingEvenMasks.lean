import Atlas.Fischer.CountingSourceTranslations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- An even mask supported on four columns is determined by its first three entries. -/
theorem countingEvenMasks_ext (e : Fin 4 ↪ Fin 6) (u v : P6)
    (hu : ∀ i, (∀ j, e j ≠ i) → u.val i=0)
    (hv : ∀ i, (∀ j, e j ≠ i) → v.val i=0)
    (hm : ∀ j : Fin 3, u.val (e ⟨j.val,by omega⟩)=v.val (e ⟨j.val,by omega⟩)) : u=v := by
  have ho (i : Fin 6) (hi : i ≠ e 3) : u.val i=v.val i := by
    by_cases hx : ∃ j, e j=i
    · obtain ⟨j,rfl⟩ := hx
      have hj : j ≠ 3 := fun h => hi (congrArg e h)
      have hj3 : j.val < 3 := by omega
      exact hm ⟨j.val,hj3⟩
    · have hn : ∀ j, e j ≠ i := by simpa only [not_exists] using hx
      rw [hu i hn,hv i hn]
  have heq : (∑ i : Fin 6, (u.val i-v.val i))=0 := by
    rw [Finset.sum_sub_distrib,(parityCode_mem 5 _).mp u.property,
      (parityCode_mem 5 _).mp v.property,sub_self]
  have hsingle : (∑ i : Fin 6, (u.val i-v.val i))=u.val (e 3)-v.val (e 3) := by
    apply Finset.sum_eq_single
    · intro i _ hi
      rw [ho i hi,sub_self]
    · simp
  rw [hsingle] at heq
  apply Subtype.ext
  funext i
  by_cases hi : i=e 3
  · subst i
    exact sub_eq_zero.mp heq
  · exact ho i hi

end Atlas.Fischer
