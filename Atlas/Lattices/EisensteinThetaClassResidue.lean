import Atlas.Lattices.EisensteinClassCoordinates

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- In the theta-divisible part, equality of theta-classes is exactly lattice
membership of the difference after cancelling one theta. -/
theorem eisensteinTheta_class_eq_iff (u v : EisensteinCoordinates)
    (hu : eisensteinTheta • u ∈ eisensteinLeechModule)
    (hv : eisensteinTheta • v ∈ eisensteinLeechModule) :
    eisensteinClass ⟨eisensteinTheta • u,hu⟩ = eisensteinClass ⟨eisensteinTheta • v,hv⟩ ↔
      u-v ∈ eisensteinLeechModule := by
  constructor
  · intro h
    obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
    have he : w.val=u-v := by
      funext i
      apply eisenstein_theta_cancel
      have hi := congrArg (fun z : EisensteinLattice => z.val i) hw
      change eisensteinTheta*w.val i=eisensteinTheta*u i-eisensteinTheta*v i at hi
      simpa only [Pi.sub_apply,mul_sub] using hi
    exact he ▸ w.property
  · intro h
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨⟨u-v,h⟩,?_⟩
    apply Subtype.ext
    funext i
    change eisensteinTheta*(u i-v i)=eisensteinTheta*u i-eisensteinTheta*v i
    ring

/-- The normalized ternary codewords of two equal short theta-classes differ
only by a constant word. This is an actual lattice congruence consequence. -/
theorem eisensteinTheta_class_residue (u v : EisensteinCoordinates)
    (hu : eisensteinTheta • u ∈ eisensteinLeechModule)
    (hv : eisensteinTheta • v ∈ eisensteinLeechModule)
    (h : eisensteinClass ⟨eisensteinTheta • u,hu⟩ = eisensteinClass ⟨eisensteinTheta • v,hv⟩) :
    ∃ a : ZMod 3, ∀ i, eisensteinResidue (u i)-eisensteinResidue (v i)=a := by
  obtain ⟨m,hm⟩ := (eisensteinTheta_class_eq_iff u v hu hv).mp h
  refine ⟨eisensteinResidue m,?_⟩
  intro i
  have hi := eisensteinCongruence_residue (u-v) m hm i
  simpa only [Pi.sub_apply,map_sub] using hi

end Atlas.Lattices
