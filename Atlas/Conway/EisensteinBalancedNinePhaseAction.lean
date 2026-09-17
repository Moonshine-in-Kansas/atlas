import Atlas.Lattices.EisensteinBalancedNineInjective
import Atlas.Codes.TernaryHexadPointProjection
import Atlas.Conway.EisensteinBalancedPhaseAction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinBalancedNineVector_phase (c : TernaryBalancedWords)
    (j : {j : Fin 12 // j ∉ ternarySupport c.val.val}) (b : Bool)
    (a d : EisensteinBalancedNinePhase c b) (r s : ZMod 3) (t : ternaryGolay)
    (hS : ∀ i : ternarySupport c.val.val,t.val i.val=d.val i-a.val i)
    (hj : t.val j.val=s-r) :
    eisensteinDiagonal t.val (eisensteinBalancedNineParameterVector ⟨c,j,b,a,r⟩)=
      eisensteinBalancedNineParameterVector ⟨c,j,b,d,s⟩ := by
  funext i
  by_cases hij : i=j.val
  · subst i
    have hc : c.val.val j.val=0 := by simpa [ternarySupport] using j.prop
    have hs : s=t.val j.val+r := by rw [hj]; ring
    simp only [eisensteinDiagonal,eisensteinBalancedNineParameterVector,
      eisensteinBalancedNineParameterLift,Pi.smul_apply,smul_eq_mul,hc,ternarySignedLift,
      if_true,Int.cast_zero,zero_mul,zero_add,show (0 : ZMod 3)≠1 by decide,show (0 : ZMod 3)≠2 by decide,ite_false]
    rw [hs,eisensteinPhase_add]
    ring
  · by_cases hi : i ∈ ternarySupport c.val.val
    · have ha : d.val ⟨i,hi⟩=t.val i+a.val ⟨i,hi⟩ := by rw [hS ⟨i,hi⟩]; ring
      simp only [eisensteinDiagonal,eisensteinBalancedNineParameterVector,
        eisensteinBalancedNineParameterLift,eisensteinBalancedNinePhaseWord,
        Pi.smul_apply,smul_eq_mul,dif_pos hi,if_neg hij,add_zero]
      rw [ha,eisensteinPhase_add]
      ring
    · have hc : c.val.val i=0 := by simpa [ternarySupport] using hi
      simp [eisensteinDiagonal,eisensteinBalancedNineParameterVector,
        eisensteinBalancedNineParameterLift,Pi.smul_apply,smul_eq_mul,hc,ternarySignedLift,hij,
        show (0 : ZMod 3)≠2 by decide]

/-- All729 phase choices at a fixed signed hexad, outside point and heavy residue
are conjugate by actual code phases. -/
theorem eisensteinBalancedNinePhase_transitive (c : TernaryBalancedWords)
    (j : {j : Fin 12 // j ∉ ternarySupport c.val.val}) (b : Bool)
    (a d : EisensteinBalancedNinePhase c b) (r s : ZMod 3) :
    ∃ t : ternaryGolay,
      eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t))
        (eisensteinBalancedNineParameterLatticeVector ⟨c,j,b,a,r⟩)=
          eisensteinBalancedNineParameterLatticeVector ⟨c,j,b,d,s⟩ := by
  let z : (ternaryHexadFunctional (ternaryBalancedSixWord c)).ker :=
    ⟨d.val-a.val,by rw [LinearMap.mem_ker,map_sub,d.prop,a.prop,sub_self]⟩
  obtain ⟨t,hS,hj⟩ := ternaryHexadPointPhase_lift (ternaryBalancedSixWord c) j.val j.prop z (s-r)
  refine ⟨t,?_⟩
  apply Subtype.ext
  rw [eisensteinIntegralAction_phase]
  exact eisensteinBalancedNineVector_phase c j b a d r s t hS hj

end Atlas.Conway
