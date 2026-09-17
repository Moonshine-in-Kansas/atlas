import Atlas.Lattices.EisensteinCongruenceCriteria
import Atlas.Codes.TernaryConstantHexads

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

/-- Every actual Eisenstein Leech vector has coordinate sum divisible by three
on each constant ternary hexad, by code self-orthogonality. -/
theorem eisensteinLeech_constant_hexad_sum (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (w : EisensteinCoordinates)
    (hw : w ∈ eisensteinLeechModule) : (3 : Eisenstein) ∣ ∑ i ∈ s,w i := by
  classical
  obtain ⟨m,r,hr,hcode,hd⟩ := hw
  have hz : eisensteinResidue (∑ i ∈ s,r i)=0 := by
    have ho := ternaryGolay_selfOrthogonal hcode (ternaryTriadWord s)
      ((mem_ternaryConstantHexads s).mp hs).2
    change (∑ i,ternaryTriadWord s i*eisensteinWordResidue r i)=0 at ho
    simpa [ternaryTriadWord,eisensteinWordResidue,Finset.sum_filter] using ho
  have htheta : eisensteinTheta ∣ ∑ i ∈ s,r i := (eisensteinResidue_eq_zero _).mp hz
  have hthree : (3 : Eisenstein) ∣ eisensteinTheta*(∑ i ∈ s,r i) :=
    (eisenstein_three_dvd_theta_iff _).mpr htheta
  have he : (∑ i ∈ s,w i)=6*m+eisensteinTheta*(∑ i ∈ s,r i) := by
    simp_rw [hr]
    simp only [Finset.sum_add_distrib,Finset.sum_const,← Finset.mul_sum,nsmul_eq_mul]
    rw [((mem_ternaryConstantHexads s).mp hs).1]
    norm_num
  rw [he]
  exact dvd_add ((show (3 : Eisenstein) ∣ 6 from ⟨2,by norm_num⟩).mul_right m) hthree

end Atlas.Lattices
