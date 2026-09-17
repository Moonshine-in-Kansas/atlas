import Atlas.Conway.EisensteinBalancedClasses

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinBalancedParameterClass_neg (p : EisensteinBalancedParameters) :
    ∃ q : EisensteinBalancedParameters,eisensteinBalancedParameterClass q =
      -eisensteinBalancedParameterClass p := by
  rcases p with ⟨c,j,a⟩
  obtain ⟨t,ht⟩ := ternaryHexadPhase_lift (ternaryBalancedSixWord c) a.val a.prop
  let d := ternaryBalancedNeg c
  have hs : ternarySupport d.val.val=ternarySupport c.val.val := ternarySupport_neg _
  let k : ternarySupport d.val.val := ⟨j.val,by rw [hs]; exact j.prop⟩
  let b : EisensteinBalancedPhase d :=
    ⟨ternaryRestriction (ternarySupport d.val.val) t,
      ternaryHexadRestriction_le (ternaryBalancedSixWord d) ⟨t,rfl⟩⟩
  have hb : eisensteinBalancedPhaseWord d b=eisensteinBalancedPhaseWord c a := by
    funext i
    by_cases hi : i ∈ ternarySupport c.val.val
    · have hd : i ∈ ternarySupport d.val.val := hs ▸ hi
      simp only [eisensteinBalancedPhaseWord,dif_pos hi,dif_pos hd]
      exact ht ⟨i,hi⟩
    · have hd : i ∉ ternarySupport d.val.val := hs ▸ hi
      simp only [eisensteinBalancedPhaseWord,dif_neg hi,dif_neg hd]
  have hv : eisensteinBalancedHexadVector d k.val= -eisensteinBalancedHexadVector c j.val := by
    funext i
    change eisensteinTheta*((ternarySignedLift (-c.val.val i) : Eisenstein)-
      (if i=j.val then 3*(ternarySignedLift (-c.val.val j.val) : Eisenstein) else 0)) =
      -(eisensteinTheta*((ternarySignedLift (c.val.val i) : Eisenstein)-
        (if i=j.val then 3*(ternarySignedLift (c.val.val j.val) : Eisenstein) else 0)))
    simp only [ternarySignedLift_neg,Int.cast_neg]
    split_ifs <;> ring
  have he : eisensteinBalancedPhasedLatticeVector d k b= -eisensteinBalancedPhasedLatticeVector c j a := by
    apply Subtype.ext
    funext i
    change eisensteinPhase (eisensteinBalancedPhaseWord d b i)*eisensteinBalancedHexadVector d k.val i =
      -(eisensteinPhase (eisensteinBalancedPhaseWord c a i)*eisensteinBalancedHexadVector c j.val i)
    rw [hb,hv]
    exact mul_neg _ _
  refine ⟨⟨d,k,b⟩,?_⟩
  change eisensteinClass (eisensteinBalancedPhasedLatticeVector d k b)=
    -eisensteinClass (eisensteinBalancedPhasedLatticeVector c j a)
  rw [he,map_neg]

theorem eisensteinBalancedClasses_neg (c : EisensteinClasses) (hc : c ∈ eisensteinBalancedClasses) :
    -c ∈ eisensteinBalancedClasses := by
  classical
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨q,hq⟩ := eisensteinBalancedParameterClass_neg p
  exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,hq⟩

end Atlas.Conway
