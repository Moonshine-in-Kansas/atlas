import Atlas.Conway.EisensteinHexadFamily
import Atlas.Codes.TernaryHexadProjection
import Atlas.Lattices.EisensteinCongruenceCriteria

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

/-- The actual sum congruence forces the phase assignment on a constant-heavy hexad
into the five-dimensional restriction hyperplane. -/
theorem eisensteinHexad_phase_sum_zero (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k : Fin 12) (hk : k ∈ s) (t : TernaryWord)
    (hz : eisensteinDiagonal t (eisensteinHexadVector s k) ∈ eisensteinLeechModule) :
    ∑ i ∈ s,t i=0 := by
  let u : EisensteinCoordinates := fun i => eisensteinPhase (t i)*eisensteinHexadLift s k i
  have he : eisensteinDiagonal t (eisensteinHexadVector s k)=eisensteinTheta • u := by
    funext i
    change eisensteinPhase (t i)*(eisensteinTheta*eisensteinHexadLift s k i)=
      eisensteinTheta*(eisensteinPhase (t i)*eisensteinHexadLift s k i)
    ring
  rw [he,eisensteinLeechModule_theta_iff] at hz
  let Z : Eisenstein := ∑ i,eisensteinPhaseCorrection (t i)*eisensteinHexadLift s k i
  have hu : ∑ i,u i=3+eisensteinTheta*Z := by
    have hi (i : Fin 12) : u i=eisensteinHexadLift s k i+
        eisensteinTheta*(eisensteinPhaseCorrection (t i)*eisensteinHexadLift s k i) := by
      dsimp [u]; rw [eisensteinPhase_correction]; ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,eisensteinHexadLift_sum,
      ((mem_ternaryConstantHexads _).mp hs).1]
    norm_num [Z]
  have hd : (3 : Eisenstein) ∣ eisensteinTheta*Z := by
    have h := dvd_sub hz.2 (dvd_refl (3 : Eisenstein))
    simpa [hu] using h
  have hr := (eisensteinResidue_eq_zero Z).mpr ((eisenstein_three_dvd_theta_iff Z).mp hd)
  have hi (i : Fin 12) : eisensteinResidue (eisensteinHexadLift s k i)=
      if i ∈ s then 1 else 0 := by
    by_cases his : i ∈ s <;> by_cases hik : i=k <;>
      simp [eisensteinHexadLift,his,hik,show eisensteinResidue 3=0 by decide +kernel]
  simp only [Z,map_sum,map_mul,eisensteinPhaseCorrection_residue,hi,mul_ite,mul_one,mul_zero] at hr
  have hsum : (∑ i,if i ∈ s then -t i else 0)= -(∑ i ∈ s,t i) := by simp
  rw [hsum] at hr
  exact neg_eq_zero.mp hr

/-- Any lattice-preserving heavy-hexad phase assignment extends to an actual Golay code phase. -/
theorem eisensteinHexad_phase_code_lift (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k : Fin 12) (hk : k ∈ s) (t : TernaryWord)
    (hz : eisensteinDiagonal t (eisensteinHexadVector s k) ∈ eisensteinLeechModule) :
    ∃ a : ternaryGolay,eisensteinDiagonal t (eisensteinHexadVector s k)=
      eisensteinDiagonal a.val (eisensteinHexadVector s k) := by
  let c := ternaryConstantHexadCodeword s hs
  let f : ternarySupport c.val.val → ZMod 3 := fun i => t i.val
  have hf : ∑ i,c.val.val i.val*f i=0 := by
    have hi (i : ternarySupport c.val.val) : c.val.val i.val=1 := by
      have his : i.val ∈ s := (ternaryConstantHexadCodeword_support s hs) ▸ i.property
      simp [c,ternaryConstantHexadCodeword,ternaryTriadWord,his]
    simp_rw [hi,one_mul]
    rw [Finset.sum_coe_sort]
    simpa [f,c,ternaryConstantHexadCodeword_support] using eisensteinHexad_phase_sum_zero s hs k hk t hz
  obtain ⟨a,ha⟩ := ternaryHexadPhase_lift c f hf
  refine ⟨a,?_⟩
  funext i
  by_cases hi : i ∈ s
  · have his : i ∈ ternarySupport c.val.val := (ternaryConstantHexadCodeword_support s hs).symm ▸ hi
    have ht := ha ⟨i,his⟩
    change a.val i=t i at ht
    simp only [eisensteinDiagonal,ht]
  · have hik : i≠k := by intro h; exact hi (h ▸ hk)
    simp [eisensteinDiagonal,eisensteinHexadVector,eisensteinHexadLift,Pi.smul_apply,smul_eq_mul,hi,hik]

end Atlas.Conway
