import Atlas.LinearGroups.ReeF4.SpecialPivotElementary

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem elementary_reduction_leading2 {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    {u : TraceZero F} (hl : SpecialLeadingAt 2 u) : ElementaryReducesToLowest hcard u := by
  have hc : u.val.2 0 0≠0 := hl.1
  have hs : u=(u.val.2 0 0) • rootVector (0,0) := by
    have hb : ∀ j, specialAbsoluteGrade 18<specialAbsoluteGrade j → isotropyCoordinates u j=0 := by
      intro j hj
      exact hl.2 j (lt_trans (by decide : specialAbsoluteGrade 2<specialAbsoluteGrade 18) hj)
    have h18 : u.val.2 2 0=0 := hl.2 18 (by decide)
    simpa only [h18,zero_smul,add_zero] using terminal_support hb
  refine ⟨terminalScalarNormalizer hcard _ hc,terminalScalarNormalizer_mem_elementary hcard _ hc,?_⟩
  calc
    _ = (terminalScalarNormalizer hcard _ hc).val ((u.val.2 0 0) • rootVector (0,0)) := congrArg _ hs
    _ = _ := terminalScalarNormalizer_action hcard _ hc

theorem elementary_reduction_leading18 {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    {u : TraceZero F} (hl : SpecialLeadingAt 18 u) : ElementaryReducesToLowest hcard u := by
  have hc : u.val.2 2 0≠0 := hl.1
  let g := terminalPivot hcard (u.val.2 0 0) (u.val.2 2 0)
  have hg : g.val u=(u.val.2 2 0) • rootVector (0,0) := by
    calc
      _ = g.val ((u.val.2 0 0) • rootVector (0,0)+(u.val.2 2 0) • rootVector (2,0)) :=
        congrArg _ (terminal_support hl.2)
      _ = _ := terminalPivot_action hcard _ _ hc
  refine elementaryReducesToLowest_of_map hcard g (terminalPivot_mem_elementary hcard _ _) ?_
  refine ⟨terminalScalarNormalizer hcard _ hc,terminalScalarNormalizer_mem_elementary hcard _ hc,?_⟩
  rw [hg,terminalScalarNormalizer_action]


end Atlas.ReeF4
