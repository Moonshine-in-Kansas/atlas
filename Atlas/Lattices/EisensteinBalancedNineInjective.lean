import Atlas.Lattices.EisensteinBalancedNineShell
import Atlas.Algebra.EisensteinCancellation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

theorem eisensteinBalancedNineParameterVector_injective :
    Function.Injective eisensteinBalancedNineParameterVector := by
  intro p q h
  have htheta : eisensteinTheta≠0 := by decide +kernel
  have hlift : eisensteinBalancedNineParameterLift p=eisensteinBalancedNineParameterLift q := by
    funext i
    apply eisenstein_mul_left_cancel htheta
    exact congrFun h i
  have hcd : p.1=q.1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [← eisensteinBalancedNineParameterLift_residue p,
      ← eisensteinBalancedNineParameterLift_residue q,hlift]
  rcases p with ⟨c,j,b,a,t⟩
  rcases q with ⟨d,k,e,a',s⟩
  dsimp only at hcd
  subst d
  have hjk : j=k := by
    apply Subtype.ext
    have hn := congrArg (fun v : EisensteinCoordinates => (v j.val).norm) h
    rw [eisensteinBalancedNineParameter_coordinate_norm,
      eisensteinBalancedNineParameter_coordinate_norm] at hn
    simp only [j.prop,ite_false,ite_true,zero_add] at hn
    by_contra hne
    simp [hne] at hn
  subst k
  have hbt : b=e ∧ t=s := by
    have hz : c.val.val j.val=0 := by simpa [ternarySupport] using j.prop
    have hh := congrFun h j.val
    have hu : eisensteinBalancedNineSign b*eisensteinPhase t =
        eisensteinBalancedNineSign e*eisensteinPhase s := by
      apply eisenstein_mul_left_cancel htheta
      apply eisenstein_mul_left_cancel htheta
      simpa [eisensteinBalancedNineParameterVector,eisensteinBalancedNineParameterLift,Pi.smul_apply,
        smul_eq_mul,hz,ternarySignedLift,show (0 : ZMod 3)≠2 by decide,mul_assoc] using hh
    have huinj : ∀ b e : Bool,∀ t s : ZMod 3,
        eisensteinBalancedNineSign b*eisensteinPhase t=eisensteinBalancedNineSign e*eisensteinPhase s →
          b=e ∧ t=s := by decide +kernel
    exact huinj b e t s hu
  rcases hbt with ⟨rfl,rfl⟩
  have haa : a=a' := by
    apply Subtype.ext
    funext i
    have hi : i.val≠j.val := by intro he; exact j.prop (he ▸ i.prop)
    have hc : c.val.val i.val≠0 := (Finset.mem_filter.mp i.prop).2
    have hl : (ternarySignedLift (c.val.val i.val) : Eisenstein)≠0 :=
      (show ∀ a : ZMod 3,a≠0 → (ternarySignedLift a : Eisenstein)≠0 by decide +kernel) _ hc
    apply eisensteinPhase_injective
    apply eisenstein_mul_left_cancel hl
    apply eisenstein_mul_left_cancel htheta
    simpa [eisensteinBalancedNineParameterVector,eisensteinBalancedNineParameterLift,
      eisensteinBalancedNinePhaseWord,Pi.smul_apply,smul_eq_mul,hi,i.prop]
      using congrFun h i.val
  subst a'
  rfl

end Atlas.Lattices
