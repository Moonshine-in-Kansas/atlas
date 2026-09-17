import Atlas.Conway.EisensteinHexadPhaseOrbit
import Atlas.Codes.TernaryConstantHexadTransitivity

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem eisensteinHexad_phase_line_support (s r : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (hr : r ∈ ternaryConstantHexads)
    (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ r) (t : ternaryGolay)
    (he : eisensteinScalarLine
      (eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6
        (eisensteinHexadShellVector s hs i hi)) =
      eisensteinScalarLine (eisensteinHexadShellVector r hr j hj)) : s=r := by
  have hij := eisensteinHexad_phase_line_heavy s r hs hr i j hi hj t he
  subst j
  obtain ⟨u,hu⟩ := eisenstein_six_sameLine_unit _ _
    (eisensteinHexadVector_norm r hr i hj)
    (eisensteinIntegralAction_norm _ _ |>.trans (eisensteinHexadVector_norm s hs i hi))
    ((eisensteinScalarLine_eq_iff _ _).mp he)
  ext k
  by_cases hki : k=i
  · subst k; simp [hi,hj]
  · have hh := congrArg (fun x : EisensteinLattice => (x.val k).norm) hu
    change ((eisensteinIntegralAction _ _).val k).norm =
      ((u : Eisenstein)*eisensteinHexadVector r i k).norm at hh
    rw [eisensteinIntegralAction_phase,eisensteinDiagonal_coordinate_norm,map_mul,
      (eisenstein_isUnit_iff (u : Eisenstein)).mp u.isUnit,one_mul] at hh
    change (eisensteinHexadVector s i k).norm = (eisensteinHexadVector r i k).norm at hh
    rw [eisensteinHexadVector_coordinate_norm s i hi k,
      eisensteinHexadVector_coordinate_norm r i hj k] at hh
    by_cases hks : k ∈ s <;> by_cases hkr : k ∈ r <;> simp_all

/-- Coordinate phases cannot change the underlying complementary hexad partition. -/
theorem eisensteinHexadFrame_phase_pair (s r : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (hr : r ∈ ternaryConstantHexads)
    (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ r) (t : ternaryGolay)
    (he : eisensteinPhaseIsometries (Multiplicative.ofAdd t) • eisensteinHexadFrame s hs i hi =
      eisensteinHexadFrame r hr j hj) : ternaryConstantHexadPair s=ternaryConstantHexadPair r := by
  let x := eisensteinHexadShellVector s hs i hi
  let y := eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6 x
  have hy : y ∈ eisensteinFrameVectors (eisensteinHexadFrame r hr j hj) := by
    rw [← he,eisensteinFrameAction_vectors]
    exact Finset.mem_image.mpr ⟨x,eisensteinHexadFrame_contains s hs i i hi hi,rfl⟩
  have hl := (eisensteinFrameLines_recovers_vectors _ y).mpr hy
  rw [eisensteinHexadFrame_lines] at hl
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hl
  unfold eisensteinHexadSideVector at hk
  split_ifs at hk with hkr
  · have hs := eisensteinHexad_phase_line_support s r hs hr i k hi hkr t hk.symm
    rw [hs]
  · have hs := eisensteinHexad_phase_line_support s rᶜ hs (ternaryConstantHexads_compl r hr)
      i k hi (Finset.mem_compl.mpr hkr) t hk.symm
    rw [hs,ternaryConstantHexadPair_compl]

end Atlas.Conway
