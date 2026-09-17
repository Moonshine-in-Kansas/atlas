import Atlas.Lattices.EisensteinMonomial
import Atlas.Lattices.EisensteinPhases

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

theorem eisensteinUnit_residue_one_phase (z : Eisenstein) (hz : IsUnit z)
    (hr : eisensteinResidue z = 1) : ∃ a : ZMod 3, z = eisensteinPhase a := by
  rcases (eisenstein_norm_one_iff z).mp ((eisenstein_isUnit_iff z).mp hz) with h|h|h|h|h|h
  · rw [h]; exact ⟨0,by decide +kernel⟩
  · rw [h] at hr
    exact False.elim ((by decide +kernel : eisensteinResidue (-1) ≠ 1) hr)
  · rw [h]; exact ⟨1,by decide +kernel⟩
  · rw [h] at hr
    exact False.elim ((by decide +kernel : eisensteinResidue (-eisensteinOmega) ≠ 1) hr)
  · rw [h] at hr
    exact False.elim ((by decide +kernel : eisensteinResidue (1+eisensteinOmega) ≠ 1) hr)
  · rw [h]; exact ⟨2,by decide +kernel⟩

/-- A phase word is forced to be a codeword by the image of the single glue vector,
even if an arbitrary coordinate permutation precedes it. -/
theorem eisensteinPhase_permuted_glue_necessary (t : TernaryWord)
    (σ : Equiv.Perm (Fin 12))
    (ht : eisensteinDiagonal t (eisensteinPermutation σ eisensteinGlue) ∈ eisensteinLeechModule) :
    t ∈ ternaryGolay := by
  let r : EisensteinCoordinates := fun i => if σ.symm i=0 then 2*eisensteinTheta else 0
  have hr (i : Fin 12) : eisensteinGlue (σ.symm i) = 1+eisensteinTheta*r i := by
    by_cases h : σ.symm i=0
    · simp only [eisensteinGlue,h,r,ite_true]
      linear_combination -2*eisensteinTheta_sq
    · simp [eisensteinGlue,r,h]
  let u : EisensteinCoordinates := fun i =>
    eisensteinPhase (t i)*r i + eisensteinPhaseCorrection (t i)
  have hu : ∀ i, eisensteinDiagonal t (eisensteinPermutation σ eisensteinGlue) i =
      1+eisensteinTheta*u i := by
    intro i
    change eisensteinPhase (t i)*eisensteinGlue (σ.symm i) = _
    rw [hr,eisensteinPhase_correction]
    dsimp [u]
    rw [eisensteinPhase_correction]
    ring
  have hc := eisensteinLeechModule_code_of_witness _ ht 1 u hu
  have hres (i : Fin 12) : eisensteinResidue (r i) = 0 := by
    dsimp [r]
    split_ifs <;> simp [show eisensteinResidue eisensteinTheta = 0 by decide +kernel]
  have he : eisensteinWordResidue u = -t := by
    funext i
    simp [eisensteinWordResidue,u,hres]
  rw [he] at hc
  simpa using ternaryGolay.neg_mem hc

/-- Exact monomial membership criterion. The final permutation factor is the full
pure-coordinate group, already identified with the existing M11. -/
theorem eisensteinUnitMonomial_lattice_iff (u : Fin 12 → Eisensteinˣ)
    (σ : Equiv.Perm (Fin 12)) :
    (∀ z ∈ eisensteinLeechModule, eisensteinUnitMonomial u σ z ∈ eisensteinLeechModule) ↔
      ∃ ε : Eisenstein, (ε=1 ∨ ε = -1) ∧ ∃ t : ternaryGolay,
        (∀ i, (u i : Eisenstein) = ε*eisensteinPhase (t.val i)) ∧
        σ ∈ ternaryPureAutomorphism := by
  constructor
  · intro hp
    have hs := eisensteinUnitMonomial_common_residue u σ hp
    have hd : ∃ ε : Eisenstein, (ε=1 ∨ ε = -1) ∧ ∃ t : TernaryWord,
        ∀ i, (u i : Eisenstein) = ε*eisensteinPhase (t i) := by
      rcases hs with hs | hs
      · choose t ht using fun i => eisensteinUnit_residue_one_phase _ (u i).isUnit (hs i)
        exact ⟨1,Or.inl rfl,t,fun i => by simpa using ht i⟩
      · have hn (i : Fin 12) : eisensteinResidue (-(u i : Eisenstein)) = 1 := by
          rw [map_neg,hs i,neg_neg]
        choose t ht using fun i => eisensteinUnit_residue_one_phase _ (u i).isUnit.neg (hn i)
        refine ⟨-1,Or.inr rfl,t,?_⟩
        intro i
        have he := congrArg Neg.neg (ht i)
        simpa using he
    obtain ⟨ε,hε,t,ht⟩ := hd
    have hε2 : ε*ε=1 := by rcases hε with rfl|rfl <;> ring
    have heq (z : EisensteinCoordinates) :
        ε • eisensteinUnitMonomial u σ z = eisensteinDiagonal t (eisensteinPermutation σ z) := by
      funext i
      change ε*((u i : Eisenstein)*z (σ.symm i)) = eisensteinPhase (t i)*z (σ.symm i)
      rw [ht i]
      calc
        _ = (ε*ε)*(eisensteinPhase (t i)*z (σ.symm i)) := by ring
        _ = _ := by rw [hε2,one_mul]
    have hn (z : EisensteinCoordinates) (hz : z ∈ eisensteinLeechModule) :
        eisensteinDiagonal t (eisensteinPermutation σ z) ∈ eisensteinLeechModule := by
      rw [← heq]
      exact eisensteinLeechModule.smul_mem ε (hp z hz)
    have htc : t ∈ ternaryGolay :=
      eisensteinPhase_permuted_glue_necessary t σ (hn _ eisensteinGlue_mem)
    have hperm : TernaryCoordinatePreserves σ := by
      apply eisensteinPermutation_code_necessary
      intro z hz
      exact (eisensteinDiagonal_lattice_iff ⟨t,htc⟩ _).mpr (hn z hz)
    exact ⟨ε,hε,⟨t,htc⟩,ht,hperm⟩
  · rintro ⟨ε,_,t,hu,hσ⟩ z hz
    have hp := eisensteinPermutation_mem ⟨σ,hσ⟩ z hz
    have ht := eisensteinDiagonal_mem t hp
    have h := eisensteinLeechModule.smul_mem ε ht
    have he : ε • eisensteinDiagonal t.val (eisensteinPermutation σ z) =
        eisensteinUnitMonomial u σ z := by
      funext i
      change ε*(eisensteinPhase (t.val i)*z (σ.symm i)) = (u i : Eisenstein)*z (σ.symm i)
      rw [hu i,mul_assoc]
    rw [he] at h; exact h

end Atlas.Lattices
