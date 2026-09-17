import Atlas.Conway.EisensteinConstantNineShell
import Atlas.Algebra.EisensteinCancellation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

 theorem eisensteinNinePartitionSide_injective (p : TernaryConstantHexadPair) :
    Function.Injective (eisensteinNinePartitionSide p) := by
  intro r s h
  have hn : (eisensteinHexadPairSupport p)ᶜ≠eisensteinHexadPairSupport p := by
    intro he
    have hi := eisensteinHexadPairPoint_mem p
    have hc : eisensteinHexadPairPoint p ∈ (eisensteinHexadPairSupport p)ᶜ := he.symm ▸ hi
    exact (Finset.mem_compl.mp hc) hi
  cases r <;> cases s <;> simp_all [eisensteinNinePartitionSide]

 theorem eisensteinConstantNineParameterVector_injective (p : TernaryConstantHexadPair)
    (b : ZMod 3) (hb : b≠0) : Function.Injective (eisensteinConstantNineParameterVector p b) := by
  intro a q h
  have hside : eisensteinNinePartitionSide p a.1=eisensteinNinePartitionSide p q.1 := by
    ext i
    have hn := congrArg (fun v : EisensteinCoordinates => (v i).norm) h
    rw [eisensteinConstantNineParameter_coordinate_norm p b hb,
      eisensteinConstantNineParameter_coordinate_norm p b hb] at hn
    by_cases hi : i ∈ eisensteinNinePartitionSide p a.1 <;>
      by_cases hj : i ∈ eisensteinNinePartitionSide p q.1 <;> simp_all only [ite_true,ite_false]
    all_goals split_ifs at hn <;> omega
  have hrs := eisensteinNinePartitionSide_injective p hside
  rcases a with ⟨r,d,j,A,z⟩
  rcases q with ⟨s,e,k,B,w⟩
  dsimp only at hrs
  subst s
  have hjk : j=k := by
    apply Subtype.ext
    have hn := congrArg (fun v : EisensteinCoordinates => (v j.val).norm) h
    rw [eisensteinConstantNineParameter_coordinate_norm p b hb,
      eisensteinConstantNineParameter_coordinate_norm p b hb] at hn
    have hj : j.val ∉ eisensteinNinePartitionSide p r := by
      simpa only [eisensteinNinePartitionCode,ternaryConstantHexadCodeword_support] using j.property
    simp only [hj,ite_false,ite_true,zero_add] at hn
    by_contra hne
    simp [hne] at hn
  subst k
  have htheta : eisensteinTheta≠0 := by decide +kernel
  have hdz : d=e ∧ z=w := by
    have hj : j.val ∉ eisensteinNinePartitionSide p r := by
      simpa only [eisensteinNinePartitionCode,ternaryConstantHexadCodeword_support] using j.property
    have hh := congrFun h j.val
    have hf : ∀ b : ZMod 3,b≠0 → ∀ d e : Bool,∀ z w : ZMod 3,
        eisensteinTheta*((if d then (-1 : Eisenstein) else 1)*
          (-(eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase z)))=
        eisensteinTheta*((if e then (-1 : Eisenstein) else 1)*
          (-(eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase w))) → d=e ∧ z=w := by
      decide +kernel
    apply hf b hb d e z w
    simpa [eisensteinConstantNineParameterVector,eisensteinConstantNineParameterLift,
      Pi.smul_apply,smul_eq_mul,hj] using hh
  rcases hdz with ⟨rfl,rfl⟩
  have hAB : A=B := by
    apply Subtype.ext
    funext i
    have his : i.val ∈ eisensteinNinePartitionSide p r := by
      simpa only [eisensteinNinePartitionCode,ternaryConstantHexadCodeword_support] using i.property
    have hij : i.val≠j.val := by intro he; exact j.property (he ▸ i.property)
    have hd : (if d then (-1 : Eisenstein) else 1)≠0 := by cases d <;> simp
    apply eisensteinPhase_injective
    apply eisenstein_mul_left_cancel hd
    apply eisenstein_mul_left_cancel htheta
    simpa [eisensteinConstantNineParameterVector,eisensteinConstantNineParameterLift,
      eisensteinConstantNinePhaseWord,Pi.smul_apply,smul_eq_mul,his,hij,i.property]
      using congrFun h i.val
  subst B
  rfl

end Atlas.Conway
