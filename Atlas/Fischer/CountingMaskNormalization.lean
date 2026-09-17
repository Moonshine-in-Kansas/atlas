import Atlas.Fischer.CountingSourceTranslations
import Atlas.Fischer.CountingHexacodeProjection

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
attribute [local instance] Classical.propDecidable

/-- Three coordinate trace values may be independently prescribed. -/
theorem countingHex_three_trace_prescribe (g : countingHexacode)
    (e : Fin 3 ↪ Fin 6) (hg : ∀ j, g.val (e j) ≠ 0) (v : Fin 3 → Bit) :
    ∃ b : countingHexacode, ∀ j, countingFieldTrace (b.val (e j)/g.val (e j))=v j := by
  let x : Fin 3 → CountingFour := fun j => if v j=0 then 0 else goldenFourTau*g.val (e j)
  obtain ⟨b,hb⟩ := (countingHexTripleProjection_bijective e).surjective x
  refine ⟨b,?_⟩
  intro j
  have hj := congrFun hb j
  change b.val (e j)=x j at hj
  rw [hj]
  have ht : ∀ (a : CountingFour) (z : Bit), a ≠ 0 →
      countingFieldTrace ((if z=0 then 0 else goldenFourTau*a)/a)=z := by
    simp only [countingFour_div]
    decide
  exact ht _ _ (hg j)

/-- Every even four-column complement pattern is realized by an actual hexacode
translation. The proof uses three-coordinate projection and the fourth parity equation. -/
theorem countingRatioMask_surjective (g : countingHexacode)
    (e : Fin 4 ↪ Fin 6) (hg : ∀ i, g.val i ≠ 0 ↔ ∃ j, e j=i)
    (v : P6) (hv : ∀ i, g.val i=0 → v.val i=0) :
    ∃ b : countingHexacode, countingRatioMask b g=v := by
  let e3 : Fin 3 ↪ Fin 6 :=
    ⟨fun j => e ⟨j.val,by omega⟩,by
      intro j k h
      exact Fin.ext (congrArg (fun x : Fin 4 => x.val) (e.injective h))⟩
  have hn : ∀ j, g.val (e3 j) ≠ 0 := by
    intro j
    exact (hg _).mpr ⟨⟨j.val,by omega⟩,rfl⟩
  obtain ⟨b,hb⟩ := countingHex_three_trace_prescribe g e3 hn (fun j => v.val (e3 j))
  have ho (i : Fin 6) (hi : i ≠ e 3) : (countingRatioMask b g).val i=v.val i := by
    by_cases hz : g.val i=0
    · rw [countingRatioMask_zero b g i hz,hv i hz]
    · obtain ⟨j,rfl⟩ := (hg i).mp hz
      have hj : j ≠ 3 := fun h => hi (congrArg e h)
      have hj3 : j.val < 3 := by omega
      have he : e3 ⟨j.val,hj3⟩=e j := congrArg e (Fin.ext rfl)
      have h := hb ⟨j.val,hj3⟩
      change countingFieldTrace (b.val (e j)/g.val (e j))=v.val (e j)
      simpa only [he] using h
  have hm := (parityCode_mem 5 _).mp (countingRatioMask b g).property
  have hvsum := (parityCode_mem 5 _).mp v.property
  have heq : (∑ i : Fin 6, ((countingRatioMask b g).val i-v.val i))=0 := by
    rw [Finset.sum_sub_distrib,hm,hvsum,sub_self]
  have hsingle : (∑ i : Fin 6, ((countingRatioMask b g).val i-v.val i))=
      (countingRatioMask b g).val (e 3)-v.val (e 3) := by
    apply Finset.sum_eq_single
    · intro i _ hi
      rw [ho i hi,sub_self]
    · simp
  rw [hsingle] at heq
  refine ⟨b,Subtype.ext (funext (fun i => ?_))⟩
  by_cases hi : i=e 3
  · subst i
    exact sub_eq_zero.mp heq
  · exact ho i hi


/-- Source Type B normalization for every actual weight-four word and even mask. -/
theorem countingSourceB_normalizes (t : CountingSourceTypeB) :
    ∃ b : countingHexacode, countingSourceBTranslation b t=
      ⟨t.1,⟨0,by intros; rfl⟩⟩ := by
  let S := Finset.univ.filter (fun i : Fin 6 => t.1.val.val i ≠ 0)
  have hS : Fintype.card S=4 := by
    rw [Fintype.card_coe]
    exact t.1.property
  let f : Fin 4 ≃ S := (Fintype.equivFinOfCardEq hS).symm
  let e : Fin 4 ↪ Fin 6 := f.toEmbedding.trans (Function.Embedding.subtype _)
  have hg : ∀ i, t.1.val.val i ≠ 0 ↔ ∃ j, e j=i := by
    intro i
    constructor
    · intro hi
      have his : i ∈ S := by simpa [S] using hi
      obtain ⟨j,hj⟩ := f.surjective ⟨i,his⟩
      exact ⟨j,congrArg Subtype.val hj⟩
    · rintro ⟨j,rfl⟩
      exact (Finset.mem_filter.mp (f j).property).2
  obtain ⟨b,hb⟩ := countingRatioMask_surjective t.1.val e hg t.2.val t.2.property
  refine ⟨b,?_⟩
  apply congrArg (fun s : {e : P6 // ∀ i : Fin 6, t.1.val.val i=0 → e.val i=0} => (⟨t.1,s⟩ : CountingSourceTypeB))
  apply Subtype.ext
  change t.2.val+countingRatioMask b t.1.val=0
  rw [hb]
  apply Subtype.ext
  funext i
  simp

end Atlas.Fischer

