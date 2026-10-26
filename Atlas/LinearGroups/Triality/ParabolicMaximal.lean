import Atlas.LinearGroups.Triality.SignedSurjectivity
import Atlas.LinearGroups.Triality.BruhatExhaustion

/-! Structural maximality of both actual parabolics from root conjugation. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem shortParabolic_weyl_overgroup (H : Subgroup (O_DPlus 4 K))
    (hP : shortParabolic F K hdeg ≤ H) (w : Fin 12) (hw : weylLift F K w ∈ H)
    (h0 : w ≠ 0) (hi : w ≠ 1) : generated F K ≤ H := by
  have hB : borel F K hdeg ≤ H := le_trans le_sup_left hP
  have hn : shortWeyl F K ∈ H := hP ((le_sup_right :
    Subgroup.closure {shortWeyl F K} ≤ shortParabolic F K hdeg)
      (Subgroup.subset_closure (Set.mem_singleton _)))
  obtain ⟨i,hpos,he⟩ := longSignedWord_outside_short w h0 hi
  have hneg (t : F) : longNegativeRoot F K t ∈ H := by
    have hh (u : F) := longSignedRoot_mem_of_weyl F K hdeg H hB w hw i hpos u
    rcases he with he|he
    · have ht := hh t
      rw [he] at ht
      exact ht
    · have hfour : longSignedRoot F K 4 (t) ∈ H := by simpa only [he] using hh (t)
      have hc := H.mul_mem (H.mul_mem hn hfour) (H.inv_mem hn)
      have hrel := longSignedRoot_intertwine F K true 4 (t)
      have hrel' : shortWeyl F K * longSignedRoot F K 4 (t) =
          longNegativeRoot F K t * shortWeyl F K := by
        simpa [longSignedReflection,longSignedNegate,longSignedRoot] using hrel
      rw [hrel',mul_inv_cancel_right] at hc
      exact hc
  have hQ : longParabolic F K hdeg ≤ H := by
    rw [longParabolic_eq_negative F K hdeg]
    apply sup_le hB
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact hneg t
  rw [← parabolic_sup_eq_generated F K hdeg]
  exact sup_le hP hQ

theorem shortParabolic_overgroup (H : Subgroup (O_DPlus 4 K))
    (hP : shortParabolic F K hdeg ≤ H) (hG : H ≤ generated F K) :
    H = shortParabolic F K hdeg ∨ H = generated F K := by
  by_cases heq : H ≤ shortParabolic F K hdeg
  · exact Or.inl (le_antisymm heq hP)
  right
  obtain ⟨g,hg,hnot⟩ := SetLike.not_le_iff_exists.mp heq
  obtain ⟨w,b,hb,c,hc,he⟩ := bruhat_exhaustion F K hdeg g (hG hg)
  have hB : borel F K hdeg ≤ H := le_trans le_sup_left hP
  have hw : weylLift F K w ∈ H := by
    have hm := H.mul_mem (H.mul_mem (H.inv_mem (hB hb)) hg) (H.inv_mem (hB hc))
    rw [he] at hm
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one] using hm
  have h0 : w ≠ 0 := by
    intro h
    subst w
    have he' : g=b*c := by simpa [weylLift,weylWord] using he
    apply hnot
    rw [he']
    exact (le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) (Subgroup.mul_mem _ hb hc)
  have hi : w ≠ 1 := by
    intro h
    subst w
    have he' : g=b*shortWeyl F K*c := by simpa [weylLift,weylWord] using he
    apply hnot
    rw [he']
    have hn : shortWeyl F K ∈ shortParabolic F K hdeg :=
      (le_sup_right : Subgroup.closure {shortWeyl F K} ≤ _)
        (Subgroup.subset_closure (Set.mem_singleton _))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      ((le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) hb) hn)
      ((le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) hc)
  exact le_antisymm hG (shortParabolic_weyl_overgroup F K hdeg H hP w hw h0 hi)

theorem longParabolic_weyl_overgroup (H : Subgroup (O_DPlus 4 K))
    (hP : longParabolic F K hdeg ≤ H) (w : Fin 12) (hw : weylLift F K w ∈ H)
    (h0 : w ≠ 0) (hi : w ≠ 2) : generated F K ≤ H := by
  have hB : borel F K hdeg ≤ H := le_trans le_sup_left hP
  have hn : longWeyl F K ∈ H := hP ((le_sup_right :
    Subgroup.closure {longWeyl F K} ≤ longParabolic F K hdeg)
      (Subgroup.subset_closure (Set.mem_singleton _)))
  obtain ⟨i,hpos,he⟩ := shortSignedWord_outside_long w h0 hi
  have hneg (t : K) : shortNegativeRoot F K t ∈ H := by
    have hh (u : K) := shortSignedRoot_mem_of_weyl F K hdeg H hB w hw i hpos u
    rcases he with he|he
    · have ht := hh t
      rw [he] at ht
      exact ht
    · have hfour : shortSignedRoot F K 4 (-t) ∈ H := by simpa only [he] using hh (-t)
      have hc := H.mul_mem (H.mul_mem hn hfour) (H.inv_mem hn)
      have hrel := shortSignedRoot_intertwine F K false 4 (-t)
      have hrel' : longWeyl F K * shortSignedRoot F K 4 (-t) =
          shortNegativeRoot F K t * longWeyl F K := by
        simpa [shortSignedReflection,shortSignedNegate,shortSignedRoot] using hrel
      rw [hrel',mul_inv_cancel_right] at hc
      exact hc
  have hQ : shortParabolic F K hdeg ≤ H := by
    rw [shortParabolic_eq_negative F K hdeg]
    apply sup_le hB
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact hneg t
  rw [← parabolic_sup_eq_generated F K hdeg]
  exact sup_le hQ hP

theorem longParabolic_overgroup (H : Subgroup (O_DPlus 4 K))
    (hP : longParabolic F K hdeg ≤ H) (hG : H ≤ generated F K) :
    H = longParabolic F K hdeg ∨ H = generated F K := by
  by_cases heq : H ≤ longParabolic F K hdeg
  · exact Or.inl (le_antisymm heq hP)
  right
  obtain ⟨g,hg,hnot⟩ := SetLike.not_le_iff_exists.mp heq
  obtain ⟨w,b,hb,c,hc,he⟩ := bruhat_exhaustion F K hdeg g (hG hg)
  have hB : borel F K hdeg ≤ H := le_trans le_sup_left hP
  have hw : weylLift F K w ∈ H := by
    have hm := H.mul_mem (H.mul_mem (H.inv_mem (hB hb)) hg) (H.inv_mem (hB hc))
    rw [he] at hm
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one] using hm
  have h0 : w ≠ 0 := by
    intro h
    subst w
    have he' : g=b*c := by simpa [weylLift,weylWord] using he
    apply hnot
    rw [he']
    exact (le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg) (Subgroup.mul_mem _ hb hc)
  have hi : w ≠ 2 := by
    intro h
    subst w
    have he' : g=b*longWeyl F K*c := by simpa [weylLift,weylWord] using he
    apply hnot
    rw [he']
    have hn : longWeyl F K ∈ longParabolic F K hdeg :=
      (le_sup_right : Subgroup.closure {longWeyl F K} ≤ _)
        (Subgroup.subset_closure (Set.mem_singleton _))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      ((le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg) hb) hn)
      ((le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg) hc)
  exact le_antisymm hG (longParabolic_weyl_overgroup F K hdeg H hP w hw h0 hi)

end Atlas.Triality
