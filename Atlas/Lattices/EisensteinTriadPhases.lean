import Atlas.Lattices.EisensteinTriadVectors
import Atlas.Lattices.EisensteinCongruenceCriteria

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

/-- Within one triad support, the theta class depends only on the sum of its
three phase exponents. -/
theorem eisensteinTriadClass_eq_of_sum (s : Finset (Fin 12)) (hs : s.card=3)
    (a b : TernaryWord) (hab : ∑ i ∈ s,a i = ∑ i ∈ s,b i) :
    eisensteinClass (eisensteinTriadLatticeVector s hs a) =
      eisensteinClass (eisensteinTriadLatticeVector s hs b) := by
  let u : EisensteinCoordinates := fun i => if i ∈ s then
    eisensteinPhaseCorrection (a i)-eisensteinPhaseCorrection (b i) else 0
  have hu : eisensteinTheta ∣ ∑ i,u i := by
    apply (eisensteinResidue_eq_zero _).mp
    simp only [map_sum,u,apply_ite,map_sub,eisensteinPhaseCorrection_residue,map_zero]
    rw [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_sub_distrib,
      Finset.sum_neg_distrib,Finset.sum_neg_distrib,hab,sub_self]
  let w : EisensteinLattice := ⟨(3 : Eisenstein) • u,eisensteinLeechModule_three_mem u hu⟩
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨w,?_⟩
  apply Subtype.ext
  funext i
  change eisensteinTheta*(3*u i) = eisensteinTriadVector s a i-eisensteinTriadVector s b i
  by_cases hi : i ∈ s
  · simp only [u,eisensteinTriadVector,if_pos hi]
    rw [eisensteinPhase_correction,eisensteinPhase_correction]
    ring
  · simp [u,eisensteinTriadVector,hi]

theorem eisensteinTriadFrame_eq_of_sum (s : Finset (Fin 12)) (hs : s.card=3)
    (a b : TernaryWord) (hab : ∑ i ∈ s,a i = ∑ i ∈ s,b i) :
    eisensteinTriadFrame s hs a = eisensteinTriadFrame s hs b := by
  apply Subtype.ext
  change eisensteinFramePair (eisensteinClass (eisensteinTriadLatticeVector s hs a)) =
    eisensteinFramePair (eisensteinClass (eisensteinTriadLatticeVector s hs b))
  rw [eisensteinTriadClass_eq_of_sum s hs a b hab]

end Atlas.Lattices
