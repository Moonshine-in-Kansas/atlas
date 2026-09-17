import Atlas.Lattices.EisensteinHexadPhases
import Atlas.Conway.EisensteinFrameAction
import Atlas.Conway.EisensteinPhaseIsometries

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped QuadraticAlgebra
attribute [local instance] Classical.propDecidable

/-- The full Hermitian phase action agrees with the integral coordinate phases. -/
theorem eisensteinIntegralAction_phase (t : ternaryGolay) (x : EisensteinLattice) :
    (eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) x).val =
      eisensteinDiagonal t.val x.val := by
  apply eisensteinCoordinateEmbedding_injective
  rw [eisensteinIntegralAction_agrees]
  exact eisensteinRationalDiagonal_embedding t.val x.val

theorem eisensteinDiagonal_coordinate_norm (t : TernaryWord) (z : EisensteinCoordinates)
    (j : Fin 12) : (eisensteinDiagonal t z j).norm = (z j).norm := by
  change (eisensteinPhase (t j)*z j).norm = _
  have hp : ∀ a : ZMod 3, (eisensteinPhase a).norm = 1 := by decide +kernel
  rw [map_mul,hp,one_mul]

/-- Equality with any unphased heavy line forces the same distinguished coordinate. -/
theorem eisensteinHexad_phase_line_heavy (s r : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (hr : r ∈ ternaryConstantHexads)
    (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ r) (t : ternaryGolay)
    (he : eisensteinScalarLine
      (eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6
        (eisensteinHexadShellVector s hs i hi)) =
      eisensteinScalarLine (eisensteinHexadShellVector r hr j hj)) : i=j := by
  obtain ⟨u,hu⟩ := eisenstein_six_sameLine_unit _ _
    (eisensteinHexadVector_norm r hr j hj)
    (eisensteinIntegralAction_norm _ _ |>.trans (eisensteinHexadVector_norm s hs i hi))
    ((eisensteinScalarLine_eq_iff _ _).mp he)
  have hh := congrArg (fun x : EisensteinLattice => (x.val i).norm) hu
  change ((eisensteinIntegralAction _ _).val i).norm =
    ((u : Eisenstein)*eisensteinHexadVector r j i).norm at hh
  rw [eisensteinIntegralAction_phase,eisensteinDiagonal_coordinate_norm,map_mul,
    (eisenstein_isUnit_iff (u : Eisenstein)).mp u.isUnit,one_mul] at hh
  change (eisensteinHexadVector s i i).norm = (eisensteinHexadVector r j i).norm at hh
  rw [eisensteinHexadVector_coordinate_norm s i hi i,
    eisensteinHexadVector_coordinate_norm r j hj i] at hh
  by_contra hij
  simp only [ite_true,hij,ite_false] at hh
  split_ifs at hh <;> norm_num at hh

/-- The phase stabilizer of a constant-hexad frame is exactly the codewords
whose phase is constant on that hexad. -/
theorem eisensteinHexadFrame_phase_stabilizer (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) (t : ternaryGolay) :
    eisensteinPhaseIsometries (Multiplicative.ofAdd t) • eisensteinHexadFrame s hs i hi =
      eisensteinHexadFrame s hs i hi ↔ ∀ j ∈ s, t.val j = t.val i := by
  let g := eisensteinPhaseIsometries (Multiplicative.ofAdd t)
  let x := eisensteinHexadShellVector s hs i hi
  let y := eisensteinShellAction g 6 x
  have hline : eisensteinScalarLine y = eisensteinScalarLine x ↔
      ∀ j ∈ s, t.val j = t.val i := by
    rw [eisensteinScalarLine_eq_iff]
    change (∃ c : EisensteinRational,
      eisensteinCoordinateEmbedding ((eisensteinIntegralAction g x.val).val) =
        c • eisensteinCoordinateEmbedding x.val.val) ↔ _
    rw [eisensteinIntegralAction_phase]
    exact eisensteinHexadVector_phase_line s i hi t.val
  constructor
  · intro hfix
    have hy : y ∈ eisensteinFrameVectors (eisensteinHexadFrame s hs i hi) := by
      rw [← hfix,eisensteinFrameAction_vectors]
      exact Finset.mem_image.mpr ⟨x,eisensteinHexadFrame_contains s hs i i hi hi,rfl⟩
    have hl := (eisensteinFrameLines_recovers_vectors _ y).mpr hy
    rw [eisensteinHexadFrame_lines] at hl
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hl
    have hij : i=j := by
      unfold eisensteinHexadSideVector at hj
      split_ifs at hj <;>
        exact eisensteinHexad_phase_line_heavy _ _ _ _ _ _ _ _ t hj.symm
    subst j
    have hsame : eisensteinScalarLine y = eisensteinScalarLine x := by
      simpa only [eisensteinHexadSideVector,dif_pos hi] using hj.symm
    exact hline.mp hsame
  · intro ht
    have hy : y ∈ eisensteinFrameVectors (eisensteinHexadFrame s hs i hi) :=
      eisensteinFrameVectors_sameLine _ x y
        (eisensteinHexadFrame_contains s hs i i hi hi) (hline.mpr ht)
    have hm := (Finset.mem_filter.mp hy).2
    change eisensteinClass y.val ∈ eisensteinFramePair (eisensteinClass x.val) at hm
    change g • eisensteinFrameOfVector x = eisensteinFrameOfVector x
    rw [eisensteinFrameAction_vector]
    apply Subtype.ext
    change eisensteinFramePair (eisensteinClass y.val) = eisensteinFramePair (eisensteinClass x.val)
    apply (eisensteinFramePair_eq_iff _ _).mpr
    simpa [eisensteinFramePair] using hm

end Atlas.Conway
