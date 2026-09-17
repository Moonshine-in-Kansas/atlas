import Atlas.Fischer.MarkedPentadOctad
import Atlas.Fischer.OctadicParityFrameMaximality

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual frames through the five marked coordinate involutions. -/
abbrev MarkedPentadFrame (S : Finset Omega) :=
  {F : Set rootGeneratedRayGroup // IsFischerFrame F ∧
    ∀ i ∈ S, distinguishedRootElement (.inl i) ∈ F}

private theorem pentad_frame_member_extension (S : Finset Omega)
    (F : MarkedPentadFrame S) (t : ReflectingRootParameter)
    (ht : distinguishedRootElement t ∈ F.val)
    (hne : ∀ i ∈ S,t ≠ .inl i) : IsMarkedBasicExtension S t := by
  intro i hi
  refine ⟨?_,distinguishedRoot_commute_nonzero (.inl i) t
    (F.prop.1.2.1 _ (F.prop.2 i hi) _ ht)⟩
  intro he
  exact hne i hi (reflectingRootParameterRay_injective he)

/-- Any frame through the marked pentad is standard or one of the two actual
parity frames over its unique containing octad. -/
theorem markedPentadFrame_classification (S : Finset Omega) (hS : S.card=5)
    (F : MarkedPentadFrame S) :
    F.val=standardCommutingFrame ∨
      ∃ e : Bit,F.val=octadicParityFrame (markedPentadOctad S hS) e := by
  classical
  by_cases hall : ∀ x ∈ F.val,x ∈ standardCommutingFrame
  · left
    exact Set.eq_of_subset_of_ncard_le hall (by
      change Nat.card standardCommutingFrame ≤ Nat.card F.val
      rw [standardCommutingFrame_card,fischerFrame_card _ F.prop.1]) (Set.toFinite _)
  push_neg at hall
  obtain ⟨x,hx,hnot⟩ := hall
  obtain ⟨t,rfl⟩ := F.prop.1.1 hx
  have hne : ∀ i ∈ S,t≠.inl i := by
    intro i hi h
    subst t
    exact hnot ⟨i,rfl⟩
  have ht := pentad_frame_member_extension S F t hx hne
  rcases (markedPentadExtension_classification S hS t).mp ht with
    ⟨i,hi,rfl⟩ | ⟨χ,rfl⟩
  · exact (hnot ⟨i,rfl⟩).elim
  right
  let O := markedPentadOctad S hS
  refine ⟨χ (octadShortenedOne O),?_⟩
  apply Set.eq_of_subset_of_ncard_le ?_ (by
    change Nat.card (octadicParityFrame O (χ (octadShortenedOne O))) ≤ Nat.card F.val
    rw [octadicParityFrame_card,fischerFrame_card _ F.prop.1]) (Set.toFinite _)
  intro y hy
  obtain ⟨s,rfl⟩ := F.prop.1.1 hy
  by_cases hs : ∃ i∈S,s=.inl i
  · obtain ⟨i,hi,rfl⟩ := hs
    exact (mem_octadicParityFrame_basic O _ i).mpr (markedPentadOctad_contains S hS hi)
  have hsn : ∀ i∈S,s≠.inl i := by simpa using hs
  have hs' := pentad_frame_member_extension S F s hy hsn
  rcases (markedPentadExtension_classification S hS s).mp hs' with
    ⟨i,hi,rfl⟩ | ⟨ψ,rfl⟩
  · apply (mem_octadicParityFrame_basic O _ i).mpr
    have hh := distinguishedRoot_commute_nonzero (.inl i) (.inr (.inl ⟨O,χ⟩))
      (F.prop.1.2.1 _ hy _ hx)
    change hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration O) χ)≠0 at hh
    by_contra hn
    rw [hermitian_basicAxis_octadic,if_neg hn] at hh
    exact hh rfl
  · apply (mem_octadicParityFrame_octadic O _ ψ).mpr
    have hh := distinguishedRoot_commute_nonzero (.inr (.inl ⟨O,ψ⟩))
      (.inr (.inl ⟨O,χ⟩)) (F.prop.1.2.1 _ hy _ hx)
    exact (octadicRoot_pairing_ne_zero_iff (chosenOctadCalibration O) ψ χ).mp hh

end Atlas.Fischer
