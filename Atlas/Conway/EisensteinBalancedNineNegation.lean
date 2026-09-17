import Atlas.Conway.EisensteinBalancedNineCoordinateAction
import Atlas.Conway.EisensteinSignShell

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem ternaryBalancedNineSign_not (b : Bool) :
    ternaryBalancedNineSign (!b)= -ternaryBalancedNineSign b := by revert b; decide +kernel

theorem eisensteinBalancedNineSign_not (b : Bool) :
    eisensteinBalancedNineSign (!b)= -eisensteinBalancedNineSign b := by revert b; decide +kernel

def eisensteinBalancedNineNegPhase (c : TernaryBalancedWords) (b : Bool)
    (a : EisensteinBalancedNinePhase c b) : EisensteinBalancedNinePhase (ternaryBalancedNeg c) (!b) := by
  let A := eisensteinBalancedNinePhaseWord c b a
  refine ⟨fun i => A i.val,?_⟩
  change (∑ i : ternarySupport (ternaryBalancedNeg c).val.val,
    (ternaryBalancedNeg c).val.val i.val*A i.val)=_
  rw [Finset.sum_coe_sort _ (fun i => (ternaryBalancedNeg c).val.val i*A i)]
  have he : (∑ i ∈ ternarySupport (ternaryBalancedNeg c).val.val,
      (ternaryBalancedNeg c).val.val i*A i)=∑ i,(ternaryBalancedNeg c).val.val i*A i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hn
    have hz : (ternaryBalancedNeg c).val.val i=0 := by simpa [ternarySupport] using hn
    rw [hz,zero_mul]
  rw [he,ternaryBalancedNineSign_not]
  simp only [ternaryBalancedNeg,Submodule.coe_neg,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
  exact congrArg Neg.neg (eisensteinBalancedNinePhaseWord_weighted c b a)

def eisensteinBalancedNineNegParameter (p : EisensteinBalancedNineParameters) :
    EisensteinBalancedNineParameters :=
  ⟨ternaryBalancedNeg p.1,⟨p.2.1.val,by
    simpa [ternarySupport,ternaryBalancedNeg] using p.2.1.prop⟩,
      !p.2.2.1,eisensteinBalancedNineNegPhase p.1 p.2.2.1 p.2.2.2.1,p.2.2.2.2⟩

theorem eisensteinBalancedNineNegParameter_vector (p : EisensteinBalancedNineParameters) :
    eisensteinBalancedNineParameterLatticeVector (eisensteinBalancedNineNegParameter p) =
      -eisensteinBalancedNineParameterLatticeVector p := by
  apply Subtype.ext
  funext i
  have hs : i ∈ ternarySupport (ternaryBalancedNeg p.1).val.val ↔
      i ∈ ternarySupport p.1.val.val := by simp [ternarySupport,ternaryBalancedNeg]
  by_cases hi : i ∈ ternarySupport p.1.val.val
  · have hi' := hs.mpr hi
    simp only [eisensteinBalancedNineParameterLatticeVector,eisensteinBalancedNineParameterVector,
      eisensteinBalancedNineParameterLift,eisensteinBalancedNineNegParameter,
      eisensteinBalancedNinePhaseWord,eisensteinBalancedNineNegPhase,Pi.smul_apply,
      smul_eq_mul,Submodule.coe_neg,Pi.neg_apply,ternaryBalancedNeg,ternarySignedLift_neg,
      Int.cast_neg,eisensteinBalancedNineSign_not]
    have hin : i ∈ ternarySupport (-p.1.val.val) := by simpa [ternarySupport] using hi
    simp only [dif_pos hin,dif_pos hi]
    split_ifs <;> ring
  · have hz : p.1.val.val i=0 := by simpa [ternarySupport] using hi
    simp [eisensteinBalancedNineParameterLatticeVector,eisensteinBalancedNineParameterVector,
      eisensteinBalancedNineParameterLift,eisensteinBalancedNineNegParameter,
      Pi.smul_apply,smul_eq_mul,ternaryBalancedNeg,hz,ternarySignedLift,
      eisensteinBalancedNineSign_not,show (0 : ZMod 3)≠2 by decide]
    split_ifs <;> simp_all

theorem eisensteinBalancedNineVectors_transitive (p q : EisensteinBalancedNineParameters) :
    ∃ g : eisensteinCoordinateFrameStabilizer,
      eisensteinIntegralAction g.val (eisensteinBalancedNineParameterLatticeVector p)=
        eisensteinBalancedNineParameterLatticeVector q := by
  by_cases hb : p.2.2.1=q.2.2.1
  · rcases p with ⟨c,j,b,a,r⟩
    rcases q with ⟨d,k,e,a',s⟩
    dsimp only at hb
    subst e
    exact eisensteinBalancedNine_same_sign_transitive c d j k b a a' r s
  · let p' := eisensteinBalancedNineNegParameter p
    have hb' : p'.2.2.1=q.2.2.1 := by
      change (!p.2.2.1)=q.2.2.1
      cases hp : p.2.2.1 <;> cases hq : q.2.2.1 <;> simp_all
    have ht : ∃ g : eisensteinCoordinateFrameStabilizer,
        eisensteinIntegralAction g.val (eisensteinBalancedNineParameterLatticeVector p')=
          eisensteinBalancedNineParameterLatticeVector q := by
      rcases p' with ⟨c,j,b,a,r⟩
      rcases q with ⟨d,k,e,a',s⟩
      dsimp only at hb'
      subst e
      exact eisensteinBalancedNine_same_sign_transitive c d j k b a a' r s
    obtain ⟨g,hg⟩ := ht
    let z := eisensteinFrameFromParameters (true,0,1)
    have hz : z.val=eisensteinSignIsometry := by
      change eisensteinMonomialParameterIsometry (true,0,1)=_
      simp [eisensteinMonomialParameterIsometry]
    refine ⟨g*z,?_⟩
    rw [Subgroup.coe_mul,eisensteinIntegralAction_mul,hz,eisensteinSignIntegral,
      ← eisensteinBalancedNineNegParameter_vector]
    exact hg

end Atlas.Conway
