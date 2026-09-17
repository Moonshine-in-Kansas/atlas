import Atlas.Conway.EisensteinBalancedNinePhaseAction
import Atlas.Codes.TernaryBalancedOutsideAction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

def eisensteinBalancedNinePermutedPhase (c d : TernaryBalancedWords)
    (g : TernaryPureAutomorphism) (hc : ∀ i,c.val.val (g.val.symm i)=d.val.val i)
    (b : Bool) (a : EisensteinBalancedNinePhase c b) : EisensteinBalancedNinePhase d b := by
  let A := eisensteinBalancedNinePhaseWord c b a
  refine ⟨fun i => A (g.val.symm i.val),?_⟩
  change (∑ i : ternarySupport d.val.val,d.val.val i.val*A (g.val.symm i.val))=_
  rw [Finset.sum_coe_sort _ (fun i => d.val.val i*A (g.val.symm i))]
  have he : (∑ i ∈ ternarySupport d.val.val,d.val.val i*A (g.val.symm i))=
      ∑ i,d.val.val i*A (g.val.symm i) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hn
    have hz : d.val.val i=0 := by simpa [ternarySupport] using hn
    rw [hz,zero_mul]
  rw [he]
  simp_rw [← hc]
  rw [g.val.symm.sum_comp (fun i => c.val.val i*A i)]
  exact eisensteinBalancedNinePhaseWord_weighted c b a

theorem eisensteinIntegralAction_coordinate (g : TernaryPureAutomorphism)
    (x : EisensteinLattice) :
    (eisensteinIntegralAction (eisensteinCoordinateIsometries g) x).val =
      eisensteinPermutation g.val x.val := by
  apply eisensteinCoordinateEmbedding_injective
  rw [eisensteinIntegralAction_agrees]
  exact eisensteinCoordinateEquiv_embedding g.val x.val

theorem eisensteinBalancedNine_coordinate (c d : TernaryBalancedWords)
    (g : TernaryPureAutomorphism) (hc : ∀ i,c.val.val (g.val.symm i)=d.val.val i)
    (j : {j : Fin 12 // j ∉ ternarySupport c.val.val})
    (k : {k : Fin 12 // k ∉ ternarySupport d.val.val}) (hj : g.val j.val=k.val)
    (b : Bool) (a : EisensteinBalancedNinePhase c b) (r : ZMod 3) :
    eisensteinIntegralAction (eisensteinCoordinateIsometries g)
      (eisensteinBalancedNineParameterLatticeVector ⟨c,j,b,a,r⟩)=
        eisensteinBalancedNineParameterLatticeVector
          ⟨d,k,b,eisensteinBalancedNinePermutedPhase c d g hc b a,r⟩ := by
  apply Subtype.ext
  rw [eisensteinIntegralAction_coordinate]
  funext i
  change eisensteinBalancedNineParameterVector ⟨c,j,b,a,r⟩ (g.val.symm i)=
    eisensteinBalancedNineParameterVector ⟨d,k,b,eisensteinBalancedNinePermutedPhase c d g hc b a,r⟩ i
  have hi : g.val.symm i=j.val ↔ i=k.val := by rw [← hj,Equiv.symm_apply_eq]
  have hs : g.val.symm i ∈ ternarySupport c.val.val ↔ i ∈ ternarySupport d.val.val := by
    simp [ternarySupport,hc]
  by_cases his : i ∈ ternarySupport d.val.val
  · have his' := hs.mpr his
    simp [eisensteinPermutation,eisensteinBalancedNineParameterVector,
      eisensteinBalancedNineParameterLift,Pi.smul_apply,smul_eq_mul,
      eisensteinBalancedNinePhaseWord,eisensteinBalancedNinePermutedPhase,his,his',hi,hc]
  · have hz : d.val.val i=0 := by simpa [ternarySupport] using his
    have hz' : c.val.val (g.val.symm i)=0 := (hc i).trans hz
    simp [eisensteinPermutation,eisensteinBalancedNineParameterVector,
      eisensteinBalancedNineParameterLift,Pi.smul_apply,smul_eq_mul,hz,hz',hi,
      ternarySignedLift,show (0 : ZMod 3)≠2 by decide]

/-- The local group is transitive on raw norm-nine vectors with a fixed heavy residue. -/
theorem eisensteinBalancedNine_same_sign_transitive
    (c d : TernaryBalancedWords)
    (j : {j : Fin 12 // j ∉ ternarySupport c.val.val})
    (k : {k : Fin 12 // k ∉ ternarySupport d.val.val})
    (b : Bool) (a : EisensteinBalancedNinePhase c b) (a' : EisensteinBalancedNinePhase d b)
    (r s : ZMod 3) :
    ∃ g : eisensteinCoordinateFrameStabilizer,
      eisensteinIntegralAction g.val (eisensteinBalancedNineParameterLatticeVector ⟨c,j,b,a,r⟩)=
        eisensteinBalancedNineParameterLatticeVector ⟨d,k,b,a',s⟩ := by
  obtain ⟨g,hg,hjk⟩ := ternaryBalanced_outside_flags_transitive c d j.val k.val j.prop k.prop
  let a0 := eisensteinBalancedNinePermutedPhase c d g hg b a
  obtain ⟨t,ht⟩ := eisensteinBalancedNinePhase_transitive d k b a0 a' r s
  refine ⟨eisensteinFrameFromParameters (false,t,g),?_⟩
  change eisensteinIntegralAction (eisensteinMonomialParameterIsometry (false,t,g)) _ = _
  have he : eisensteinMonomialParameterIsometry (false,t,g)=
      eisensteinPhaseIsometries (Multiplicative.ofAdd t)*eisensteinCoordinateIsometries g := by
    simp [eisensteinMonomialParameterIsometry]
  rw [he,eisensteinIntegralAction_mul,eisensteinBalancedNine_coordinate c d g hg j k hjk b a r]
  exact ht

end Atlas.Conway
