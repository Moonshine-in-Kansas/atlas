import Atlas.Lattices.EisensteinClassCoordinates

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra

theorem eisensteinClass_theta_difference_iff (x y : EisensteinLattice)
    (u v : EisensteinCoordinates) (hx : x.val=eisensteinTheta • u)
    (hy : y.val=eisensteinTheta • v) :
    eisensteinClass x=eisensteinClass y ↔ u-v ∈ eisensteinLeechModule := by
  constructor
  · intro h
    obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
    have he : w.val=u-v := by
      funext i
      apply eisenstein_theta_cancel
      have hi := congrArg (fun z : EisensteinLattice => z.val i) hw
      change eisensteinTheta*w.val i=x.val i-y.val i at hi
      rw [hx,hy] at hi
      simpa [Pi.smul_apply,smul_eq_mul,mul_sub] using hi
    exact he ▸ w.prop
  · intro h
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨⟨u-v,h⟩,?_⟩
    apply Subtype.ext
    change eisensteinTheta • (u-v)=x.val-y.val
    rw [hx,hy,smul_sub]

end Atlas.Lattices
