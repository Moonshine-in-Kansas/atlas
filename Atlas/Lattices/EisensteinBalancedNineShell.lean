import Atlas.Lattices.EisensteinBalancedNineMembership

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

theorem eisensteinBalancedNineParameter_coordinate_norm (p : EisensteinBalancedNineParameters)
    (i : Fin 12) : (eisensteinBalancedNineParameterVector p i).norm =
      (if i ∈ ternarySupport p.1.val.val then 3 else 0)+(if i=p.2.1.val then 9 else 0) := by
  have hs : ∀ a t : ZMod 3,
      (eisensteinTheta*((ternarySignedLift a : Eisenstein)*eisensteinPhase t)).norm =
        if a≠0 then 3 else 0 := by decide +kernel
  have hj : ∀ b : Bool,∀ t : ZMod 3,
      (eisensteinTheta*(eisensteinTheta*eisensteinBalancedNineSign b*eisensteinPhase t)).norm=9 := by
    decide +kernel
  by_cases hi : i=p.2.1.val
  · subst i
    have hz : p.1.val.val p.2.1.val=0 := by simpa [ternarySupport] using p.2.1.prop
    simpa [eisensteinBalancedNineParameterVector,eisensteinBalancedNineParameterLift,Pi.smul_apply,
      smul_eq_mul,hz,ternarySignedLift,p.2.1.prop,show (0 : ZMod 3)≠2 by decide]
      using hj p.2.2.1 p.2.2.2.2
  · simpa [eisensteinBalancedNineParameterVector,eisensteinBalancedNineParameterLift,Pi.smul_apply,
      smul_eq_mul,hi,ternarySupport] using
        hs (p.1.val.val i) (eisensteinBalancedNinePhaseWord p.1 p.2.2.1 p.2.2.2.1 i)

theorem eisensteinBalancedNineParameter_norm (p : EisensteinBalancedNineParameters) :
    eisensteinNorm (eisensteinBalancedNineParameterLatticeVector p)=6 := by
  rw [eisensteinNorm,eisensteinBilinear_self_sum_norm]
  have he (i : Fin 12) :
      (eisensteinToRational (eisensteinBalancedNineParameterVector p i)).norm =
        ((eisensteinBalancedNineParameterVector p i).norm : ℚ) := by
    simp [eisensteinToRational,QuadraticAlgebra.norm_def]
  change (2/9 : ℚ)*∑ i,(eisensteinToRational (eisensteinBalancedNineParameterVector p i)).norm=6
  simp_rw [he,eisensteinBalancedNineParameter_coordinate_norm]
  norm_num [Int.cast_add,Int.cast_ite,Finset.sum_add_distrib,ternarySupport_card,
    ternaryBalanced_weight _ p.1.prop]

def eisensteinBalancedNineParameterShell (p : EisensteinBalancedNineParameters) : EisensteinShell 6 :=
  ⟨eisensteinBalancedNineParameterLatticeVector p,eisensteinBalancedNineParameter_norm p⟩

end Atlas.Lattices
