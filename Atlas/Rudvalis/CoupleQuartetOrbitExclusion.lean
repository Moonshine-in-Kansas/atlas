import Atlas.Rudvalis.CoupleQuartetTransport
import Atlas.Rudvalis.CoupleFourTransitivity
import Atlas.Rudvalis.HeavyCoupleTransitivity

namespace Atlas.Rudvalis

theorem codeCouple_intrinsicDozen_iff (g : codeCoupleStabilizer) (c : MinimalCross) :
    g.val • c∈intrinsicDozen referenceCouple ↔ c∈intrinsicDozen referenceCouple := by
  let a : coupleFusionGroup := ⟨coupleGaussianHom g,coupleGaussianHom_mem g⟩
  have h := coupleFusion_intrinsicDozen_iff a c
  change codeGaussianHom g.val • c∈intrinsicDozen referenceCouple ↔ _ at h
  simpa only [codeGaussianHom_cross] using h

theorem fourCouple_intrinsicDozen_iff (v w : FourBlockCrosses)
    (hv : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece v))
    (hw : ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece w))
    (he : crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece v)=
      crossRowEnergy referenceDozenRows (shellPieceCrossMap fourShellPiece w)) :
    shellPieceCrossMap fourShellPiece v∈intrinsicDozen referenceCouple ↔
      shellPieceCrossMap fourShellPiece w∈intrinsicDozen referenceCouple := by
  obtain ⟨g,hgx,hgy,hg⟩ := fourCouple_crosses_transitive v w hv hw he
  have h := codeCouple_intrinsicDozen_iff ⟨g,hgx,hgy⟩ (shellPieceCrossMap fourShellPiece v)
  change g • shellPieceCrossMap fourShellPiece v∈intrinsicDozen referenceCouple ↔ _ at h
  rw [hg] at h
  exact h.symm

theorem heavyCouple_intrinsicDozen_iff (v w : HeavyCrosses)
    (hv : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece v))
    (hw : ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece w)) :
    shellPieceCrossMap heavyShellPiece v∈intrinsicDozen referenceCouple ↔
      shellPieceCrossMap heavyShellPiece w∈intrinsicDozen referenceCouple := by
  obtain ⟨g,hg⟩ := heavyCross_couple_stabilizer_transitive v w hv hw
  have h := codeCouple_intrinsicDozen_iff g (shellPieceCrossMap heavyShellPiece v)
  rw [hg] at h
  exact h.symm

theorem intrinsicDozen_noncoordinate_common (z : MinimalCross)
    (hz : z∈intrinsicDozen referenceCouple) (hzF : z∉coordinateFrame) :
    ReferenceCoupleOrthogonal z := by
  obtain ⟨Q,hQ,hc,hz⟩ := hz
  exact ⟨hQ.2.1 (hc (Or.inl rfl)) hz (fun h=>hzF (h ▸ coordinateCross_mem _)),
    hQ.2.1 (hc (Or.inr rfl)) hz (fun h=>hzF (h ▸ coordinateCross_mem _))⟩

/-- Exhaustion reduces to exclusion in the actual noncoordinate shell pieces. -/
theorem reference_intrinsicDozen_eq_of_piece_exclusion
    (hf : ∀v : FourBlockCrosses,ReferenceCoupleOrthogonal (shellPieceCrossMap fourShellPiece v) →
      shellPieceCrossMap fourShellPiece v∉intrinsicDozen referenceCouple)
    (hh : ∀v : HeavyCrosses,ReferenceCoupleOrthogonal (shellPieceCrossMap heavyShellPiece v) →
      shellPieceCrossMap heavyShellPiece v∉intrinsicDozen referenceCouple) :
    intrinsicDozen referenceCouple=referenceCoordinateDozen := by
  apply Set.Subset.antisymm _ referenceCoordinateDozen_subset_intrinsicDozen
  intro z hz
  by_cases hzF : z∈coordinateFrame
  · rw [←reference_intrinsicDozen_coordinate_intersection]
    exact ⟨hz,hzF⟩
  have ho := intrinsicDozen_noncoordinate_common z hz hzF
  rcases minimalCross_piece_cases z with ⟨v,hv⟩|⟨v,hv⟩|⟨v,hv⟩
  · exact (hzF (hv ▸ ⟨v,rfl⟩)).elim
  · rw [←hv] at ho hz
    exact (hf v ho hz).elim
  · rw [←hv] at ho hz
    exact (hh v ho hz).elim

end Atlas.Rudvalis
