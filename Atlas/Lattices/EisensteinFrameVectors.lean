import Atlas.Lattices.EisensteinFrames

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- All norm-six vectors represented by an intrinsic frame. -/
def eisensteinFrameVectors (F : EisensteinFrame) : Finset (EisensteinShell 6) :=
  Finset.univ.filter (fun x => eisensteinClass x.val ∈ F.val)

theorem eisensteinFrame_pair (F : EisensteinFrame) :
    ∃ c ∈ eisensteinShellClasses 6, F.val = eisensteinFramePair c := by
  obtain ⟨c, hc, he⟩ := Finset.mem_image.mp F.property
  exact ⟨c, hc, he.symm⟩

theorem eisensteinFrameVectors_card (F : EisensteinFrame) : (eisensteinFrameVectors F).card = 72 := by
  obtain ⟨c, hc, he⟩ := eisensteinFrame_pair F
  have hn : c ≠ -c := Ne.symm (eisensteinClasses_neg_ne
    (fun h => eisensteinShellClasses_zero_not_mem 6 (by decide) (h ▸ hc)))
  have hdis : Disjoint
      (Finset.univ.filter (fun x : EisensteinShell 6 => eisensteinClass x.val=c))
      (Finset.univ.filter (fun x : EisensteinShell 6 => eisensteinClass x.val= -c)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hn ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)
  have hv : eisensteinFrameVectors F =
      (Finset.univ.filter (fun x : EisensteinShell 6 => eisensteinClass x.val=c)) ∪
      (Finset.univ.filter (fun x : EisensteinShell 6 => eisensteinClass x.val= -c)) := by
    ext x
    simp [eisensteinFrameVectors, he, eisensteinFramePair]
  have hf (d : EisensteinClasses) :
      (Finset.univ.filter (fun x : EisensteinShell 6 => eisensteinClass x.val=d)).card =
        Nat.card (EisensteinClassFiber 6 d) :=
    (Atlas.Combinatorics.fiber_card_filter (fun x : EisensteinShell 6 => eisensteinClass x.val) d).symm
  rw [hv, Finset.card_union_of_disjoint hdis, hf c, hf (-c)]
  change Nat.card (EisensteinClassFiber 6 c) + Nat.card (EisensteinClassFiber 6 (-c)) = 72
  rw [eisenstein_six_class_card c hc, eisenstein_six_class_card (-c) (eisensteinShellClasses_neg hc)]

/-- The short-vector set remembers its intrinsic pair of classes. -/
theorem eisensteinFrameVectors_injective : Function.Injective eisensteinFrameVectors := by
  intro F G h
  apply Subtype.ext
  have he (H : EisensteinFrame) :
      (eisensteinFrameVectors H).image (fun x => eisensteinClass x.val) = H.val := by
    obtain ⟨c, hc, hH⟩ := eisensteinFrame_pair H
    ext d
    constructor
    · rintro hd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      exact (Finset.mem_filter.mp hx).2
    · intro hd
      have hds : d ∈ eisensteinShellClasses 6 := by
        rcases (show d=c ∨ d= -c by simpa [hH, eisensteinFramePair] using hd) with rfl | rfl
        · exact hc
        · exact eisensteinShellClasses_neg hc
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hds
      refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hx⟩
      simpa only [hx] using hd
  rw [← he F, ← he G, h]

end Atlas.Lattices
