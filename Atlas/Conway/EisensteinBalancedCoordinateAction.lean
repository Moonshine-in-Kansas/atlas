import Atlas.Conway.EisensteinBalancedPhaseAction
import Atlas.Conway.EisensteinTriadOrbit

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinBalancedBaseFrame_coordinate (c d : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (k : ternarySupport d.val.val)
    (g : TernaryPureAutomorphism) (hc : ∀ i,c.val.val (g.val.symm i)=d.val.val i)
    (hj : g.val j.val=k.val) :
    eisensteinCoordinateIsometries g • eisensteinBalancedBaseFrame c j =
      eisensteinBalancedBaseFrame d k := by
  rw [eisensteinBalancedBaseFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  change eisensteinCoordinateEmbedding
    (eisensteinIntegralAction (eisensteinCoordinateIsometries g)
      (eisensteinBalancedHexadLatticeVector c j.val)).val = _
  rw [eisensteinIntegralAction_agrees]
  funext i
  change eisensteinToRational (eisensteinBalancedHexadVector c j.val (g.val.symm i)) =
    eisensteinToRational (eisensteinBalancedHexadVector d k.val i)
  have hi : g.val.symm i=j.val ↔ i=k.val := by
    rw [← hj,Equiv.symm_apply_eq]
  have hck : c.val.val j.val=d.val.val k.val := by simpa [← hj] using hc k.val
  simp [eisensteinBalancedHexadVector,eisensteinBalancedHexadLift,hc,hi,hck]

def eisensteinBalancedNegPosition (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) : ternarySupport (ternaryBalancedNeg c).val.val :=
  ⟨j.val,by simpa [ternarySupport,ternaryBalancedNeg] using j.prop⟩

theorem eisensteinBalancedBaseFrame_neg (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) :
    eisensteinBalancedBaseFrame (ternaryBalancedNeg c) (eisensteinBalancedNegPosition c j) =
      eisensteinBalancedBaseFrame c j := by
  have hv : eisensteinBalancedHexadLatticeVector (ternaryBalancedNeg c) j.val =
      -eisensteinBalancedHexadLatticeVector c j.val := by
    apply Subtype.ext
    funext i
    change eisensteinBalancedHexadVector (ternaryBalancedNeg c) j.val i =
      -eisensteinBalancedHexadVector c j.val i
    simp only [eisensteinBalancedHexadVector,Pi.smul_apply,smul_eq_mul,eisensteinBalancedHexadLift,ternaryBalancedNeg,
      Submodule.coe_neg,Pi.neg_apply,ternarySignedLift_neg,Int.cast_neg]
    split_ifs <;> ring
  apply Subtype.ext
  change eisensteinFramePair (eisensteinClass
    (eisensteinBalancedHexadLatticeVector (ternaryBalancedNeg c) j.val)) =
      eisensteinFramePair (eisensteinClass (eisensteinBalancedHexadLatticeVector c j.val))
  rw [hv,map_neg,eisensteinFramePair_neg]

end Atlas.Conway
