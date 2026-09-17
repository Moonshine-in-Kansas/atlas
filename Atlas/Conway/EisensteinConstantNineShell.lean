import Atlas.Conway.EisensteinConstantNineMembership

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem eisensteinConstantNineParameter_coordinate_norm (p : TernaryConstantHexadPair)
    (b : ZMod 3) (hb : b≠0) (a : EisensteinConstantNineParameters p b) (i : Fin 12) :
    (eisensteinConstantNineParameterVector p b a i).norm=
      (if i ∈ eisensteinNinePartitionSide p a.1 then 3 else 0)+
      (if i=a.2.2.1.val then 9 else 0) := by
  have hj : a.2.2.1.val ∉ eisensteinNinePartitionSide p a.1 := by
    simpa only [eisensteinNinePartitionCode,ternaryConstantHexadCodeword_support] using a.2.2.1.property
  have h3 : ∀ d : Bool,∀ t : ZMod 3,
      (eisensteinTheta*((if d then (-1 : Eisenstein) else 1)*eisensteinPhase t)).norm=3 := by decide +kernel
  have h9 : ∀ d : Bool,∀ e t : ZMod 3,e≠0 →
      (eisensteinTheta*((if d then (-1 : Eisenstein) else 1)*
        (-(eisensteinTheta*eisensteinPhaseCorrection e*eisensteinPhase t)))).norm=9 := by decide +kernel
  by_cases hij : i=a.2.2.1.val
  · subst i
    simpa [eisensteinConstantNineParameterVector,eisensteinConstantNineParameterLift,
      Pi.smul_apply,smul_eq_mul,hj] using h9 a.2.1 b a.2.2.2.2 hb
  · by_cases hi : i ∈ eisensteinNinePartitionSide p a.1
    · simpa [eisensteinConstantNineParameterVector,eisensteinConstantNineParameterLift,
        Pi.smul_apply,smul_eq_mul,hi,hij] using
          h3 a.2.1 (eisensteinConstantNinePhaseWord p a.1 b a.2.2.2.1 i)
    · simp [eisensteinConstantNineParameterVector,eisensteinConstantNineParameterLift,
        Pi.smul_apply,smul_eq_mul,hi,hij]

theorem eisensteinConstantNineParameter_norm (p : TernaryConstantHexadPair)
    (b : ZMod 3) (hb : b≠0) (a : EisensteinConstantNineParameters p b) :
    eisensteinNorm (eisensteinConstantNineParameterLattice p b a)=6 := by
  rw [eisensteinNorm,eisensteinBilinear_self_sum_norm]
  have he (i : Fin 12) :
      (eisensteinToRational (eisensteinConstantNineParameterVector p b a i)).norm =
        ((eisensteinConstantNineParameterVector p b a i).norm : ℚ) := by
    simp [eisensteinToRational,QuadraticAlgebra.norm_def]
  change (2/9 : ℚ)*∑ i,(eisensteinToRational (eisensteinConstantNineParameterVector p b a i)).norm=6
  simp_rw [he,eisensteinConstantNineParameter_coordinate_norm p b hb a]
  norm_num [Int.cast_add,Int.cast_ite,Finset.sum_add_distrib,
    ((mem_ternaryConstantHexads _).mp (eisensteinNinePartitionSide_mem p a.1)).1]

def eisensteinConstantNineParameterShell (p : TernaryConstantHexadPair)
    (b : ZMod 3) (hb : b≠0) (a : EisensteinConstantNineParameters p b) : EisensteinShell 6 :=
  ⟨eisensteinConstantNineParameterLattice p b a,eisensteinConstantNineParameter_norm p b hb a⟩

end Atlas.Conway
