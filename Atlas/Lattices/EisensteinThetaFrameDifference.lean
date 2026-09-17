import Atlas.Lattices.EisensteinThetaClassResidue
import Atlas.Lattices.EisensteinFrames

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- Equality of intrinsic theta-class pairs gives lattice membership after cancelling
theta, with exactly the two possible orientations. -/
theorem eisensteinTheta_frame_difference (u v : EisensteinCoordinates)
    (hu : eisensteinTheta • u ∈ eisensteinLeechModule)
    (hv : eisensteinTheta • v ∈ eisensteinLeechModule)
    (h : eisensteinFramePair (eisensteinClass ⟨eisensteinTheta • u,hu⟩)=
      eisensteinFramePair (eisensteinClass ⟨eisensteinTheta • v,hv⟩)) :
    u-v ∈ eisensteinLeechModule ∨ u+v ∈ eisensteinLeechModule := by
  rw [eisensteinFramePair_eq_iff] at h
  rcases h with h|h
  · exact Or.inl ((eisensteinTheta_class_eq_iff u v hu hv).mp h)
  · have hn : eisensteinTheta • (-v) ∈ eisensteinLeechModule := by
      rw [smul_neg]; exact eisensteinLeechModule.neg_mem hv
    have he : (⟨eisensteinTheta • (-v),hn⟩ : EisensteinLattice)= -⟨eisensteinTheta • v,hv⟩ := by
      apply Subtype.ext; simp only [smul_neg,Submodule.coe_neg]
    have hc : eisensteinClass ⟨eisensteinTheta • u,hu⟩=
        eisensteinClass ⟨eisensteinTheta • (-v),hn⟩ := by rw [he,map_neg]; exact h
    have hm := (eisensteinTheta_class_eq_iff u (-v) hu hn).mp hc
    exact Or.inr (by simpa using hm)

/-- The common scalar residue of any actual lattice vector is independent of its coordinate. -/
theorem eisensteinLeech_residue_coordinates (w : EisensteinCoordinates)
    (hw : w ∈ eisensteinLeechModule) (i j : Fin 12) :
    eisensteinResidue (w i)=eisensteinResidue (w j) := by
  obtain ⟨m,hm⟩ := hw
  exact (eisensteinCongruence_residue w m hm i).trans
    (eisensteinCongruence_residue w m hm j).symm

end Atlas.Lattices
