import Atlas.Conway.EisensteinHexadPhaseRecognition
import Atlas.Algebra.EisensteinSmallNorms
import Atlas.Lattices.EisensteinMonomialCriterion

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

private theorem hexad_norm_zero (z : Eisenstein) (h : z.norm=0) : z=0 := by
  rw [eisenstein_norm] at h
  have hr : z.re=0 := by nlinarith [sq_nonneg z.im,sq_nonneg (z.re-z.im)]
  have hi : z.im=0 := by nlinarith [sq_nonneg z.re,sq_nonneg (z.re-z.im)]
  exact QuadraticAlgebra.ext hr hi

/-- Normalized constant-heavy coordinates are precisely phases of the explicit heavy hexad. -/
theorem eisensteinHexad_normalized_phases (s : Finset (Fin 12)) (k : Fin 12) (hk : k ∈ s)
    (u : EisensteinCoordinates) (hr : eisensteinWordResidue u=ternaryTriadWord s)
    (hn : ∀ i,(u i).norm=if i=k then 4 else if i ∈ s then 1 else 0) :
    ∃ t : TernaryWord, ∀ i,u i=eisensteinPhase (t i)*eisensteinHexadLift s k i := by
  have he (i : Fin 12) : ∃ a : ZMod 3,u i=eisensteinPhase a*eisensteinHexadLift s k i := by
    have hri := congrFun hr i
    change eisensteinResidue (u i)=ternaryTriadWord s i at hri
    by_cases hik : i=k
    · subst i
      have h4 : (u k).norm=4 := by simpa using hn k
      obtain ⟨v,hv⟩ := eisenstein_norm_four_unit (u k) h4
      have hres : eisensteinResidue (-(v : Eisenstein))=1 := by
        have hh := congrArg eisensteinResidue hv
        have hkres : eisensteinResidue (u k)=1 := by simpa [ternaryTriadWord,hk] using hri
        rw [hkres] at hh
        simpa [show eisensteinResidue 2= -1 by decide +kernel] using hh.symm
      obtain ⟨a,ha⟩ := eisensteinUnit_residue_one_phase (-(v : Eisenstein)) v.isUnit.neg hres
      refine ⟨a,?_⟩
      rw [hv,← ha]
      simp [eisensteinHexadLift,hk]
      ring
    · by_cases his : i ∈ s
      · have h1 : (u i).norm=1 := by simpa [hik,his] using hn i
        obtain ⟨a,ha⟩ := eisensteinUnit_residue_one_phase (u i) ((eisenstein_isUnit_iff _).mpr h1)
          (by simpa [ternaryTriadWord,his] using hri)
        exact ⟨a,by simpa [eisensteinHexadLift,his,hik] using ha⟩
      · have h0 : (u i).norm=0 := by simpa [hik,his] using hn i
        exact ⟨0,by simp [hexad_norm_zero _ h0,eisensteinHexadLift,his,hik]⟩
  choose t ht using he
  exact ⟨t,ht⟩

/-- Any actual normalized constant-heavy vector is obtained by an actual Golay code phase. -/
theorem eisensteinHexad_normalized_code_phase (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k : Fin 12) (hk : k ∈ s)
    (u : EisensteinCoordinates) (hr : eisensteinWordResidue u=ternaryTriadWord s)
    (hn : ∀ i,(u i).norm=if i=k then 4 else if i ∈ s then 1 else 0)
    (hu : eisensteinTheta • u ∈ eisensteinLeechModule) :
    ∃ a : ternaryGolay,eisensteinTheta • u=eisensteinDiagonal a.val (eisensteinHexadVector s k) := by
  obtain ⟨t,ht⟩ := eisensteinHexad_normalized_phases s k hk u hr hn
  have he : eisensteinTheta • u=eisensteinDiagonal t (eisensteinHexadVector s k) := by
    funext i
    change eisensteinTheta*u i=eisensteinPhase (t i)*(eisensteinTheta*eisensteinHexadLift s k i)
    rw [ht]
    ring
  obtain ⟨a,ha⟩ := eisensteinHexad_phase_code_lift s hs k hk t (he ▸ hu)
  exact ⟨a,he.trans ha⟩

end Atlas.Conway
