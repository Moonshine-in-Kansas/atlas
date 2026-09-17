import Atlas.Lattices.EisensteinMonomial

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

/-- On the coordinatewise theta-divisible part, the full lattice condition is
exactly the ternary code condition and the integral sum condition. -/
theorem eisensteinLeechModule_theta_iff (u : EisensteinCoordinates) :
    eisensteinTheta • u ∈ eisensteinLeechModule ↔
      eisensteinWordResidue u ∈ ternaryGolay ∧ (3 : Eisenstein) ∣ ∑ i,u i := by
  constructor
  · intro hu
    have hc := eisensteinLeechModule_theta_code u hu
    obtain ⟨m,hm⟩ := hu
    have hres := eisensteinCongruence_residue _ m hm 0
    have hz : eisensteinResidue m = 0 := by
      simpa [Pi.smul_apply,smul_eq_mul,
        show eisensteinResidue eisensteinTheta = 0 by decide +kernel] using hres.symm
    obtain ⟨a,ha⟩ := (eisensteinResidue_eq_zero m).mp hz
    have hm0 : EisensteinCongruence (eisensteinTheta • u) 0 := by
      apply (eisensteinCongruence_lift_independent _ 0 a).mp
      simpa [ha] using hm
    obtain ⟨_,_,_,b,hb⟩ := hm0
    refine ⟨hc,b,eisenstein_theta_cancel ?_⟩
    simpa [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm] using hb
  · rintro ⟨hc,b,hb⟩
    refine ⟨0,u,?_,hc,b,?_⟩
    · intro i; simp
    · simp [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hb,mul_assoc,mul_comm,mul_left_comm]

theorem eisensteinLeechModule_three_mem (u : EisensteinCoordinates)
    (hu : eisensteinTheta ∣ ∑ i,u i) : (3 : Eisenstein) • u ∈ eisensteinLeechModule := by
  have he : (3 : Eisenstein) • u = eisensteinTheta • (-eisensteinTheta • u) := by
    funext i
    simp [Pi.smul_apply,smul_eq_mul,← mul_assoc,← pow_two,eisensteinTheta_sq]
  rw [he,eisensteinLeechModule_theta_iff]
  constructor
  · have hz : eisensteinWordResidue (-eisensteinTheta • u) = 0 := by
      ext i
      simp [eisensteinWordResidue,
        show eisensteinResidue eisensteinTheta = 0 by decide +kernel]
    rw [hz]; exact Submodule.zero_mem _
  · obtain ⟨b,hb⟩ := hu
    refine ⟨b,?_⟩
    simp [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hb,← mul_assoc,
      ← pow_two,eisensteinTheta_sq]

theorem eisenstein_three_dvd_theta_iff (a : Eisenstein) :
    (3 : Eisenstein) ∣ eisensteinTheta*a ↔ eisensteinTheta ∣ a := by
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨-b,eisenstein_theta_cancel ?_⟩
    rw [hb]
    simp [← mul_assoc,← pow_two,eisensteinTheta_sq]
  · rintro ⟨b,rfl⟩
    refine ⟨-b,?_⟩
    simp [← mul_assoc,← pow_two,eisensteinTheta_sq]

end Atlas.Lattices
