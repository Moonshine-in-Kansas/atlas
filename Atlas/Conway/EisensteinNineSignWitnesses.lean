import Atlas.Conway.EisensteinNineSignAction
import Atlas.Conway.EisensteinNineHexadFamily

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

/-- Every explicit constant norm-nine frame carries its prescribed intrinsic sign. -/
theorem eisensteinNineHexadFrame_sign (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b : ZMod 3) (hb : b≠0) :
    EisensteinNineSignFrame b (eisensteinNineHexadFrame s hs k j hk hj b hb) := by
  classical
  refine ⟨s,hs,j,hj,0,Pi.single k b,?_,
    eisensteinNineHexadShellVector s hs k j hk hj b hb,?_,rfl⟩
  · simp [Pi.single_apply,hk]
  · funext i
    change eisensteinTheta*eisensteinNineHexadLift s k j b i=
      eisensteinTheta*eisensteinConstantNineForm s j b 0 (Pi.single k b) i
    congr 1
    have hkj : k≠j := by intro h; exact hj (h ▸ hk)
    by_cases hik : i=k
    · subst i
      simp [eisensteinNineHexadLift,eisensteinConstantNineForm,hk,hkj,Pi.single_apply,
        eisensteinPhase_correction]
    · by_cases hij : i=j
      · subst i
        simp [eisensteinNineHexadLift,eisensteinConstantNineForm,hj,hik,Pi.single_apply]
      · by_cases hi : i ∈ s <;>
          simp [eisensteinNineHexadLift,eisensteinConstantNineForm,hi,hik,hij,Pi.single_apply]

 theorem eisensteinNineHexadFamily_sign (b : ZMod 3) (hb : b≠0)
    (F : EisensteinFrame) (hF : F ∈ eisensteinNineHexadFamily b hb) : EisensteinNineSignFrame b F := by
  classical
  obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
  obtain ⟨t,ht⟩ := (eisensteinNineHexadPairOrbit_mem b hb p F).mp hp
  rw [← ht]
  apply eisensteinNineSignFrame_phase
  exact eisensteinNineHexadFrame_sign _ (eisensteinHexadPairSupport_mem p) _ _
    (eisensteinHexadPairPoint_mem p) (eisensteinNineHexadPairOutside_mem p) b hb

local instance eisensteinNineSignPhaseAction : MulAction (Multiplicative ternaryGolay) EisensteinFrame :=
  MulAction.compHom EisensteinFrame eisensteinPhaseIsometries

/-- Every frame with the intrinsic nonzero sign has an actual code-phase orbit of243. -/
theorem eisensteinNineSignFrame_phase_orbit_card (b : ZMod 3) (hb : b≠0)
    (F : EisensteinFrame) (hF : EisensteinNineSignFrame b F) :
    Nat.card (MulAction.orbit (Multiplicative ternaryGolay) F)=243 := by
  obtain ⟨s,hs,k,hk,z,t,ht,x,hx,rfl⟩ := hF
  have hu : IsUnit (-eisensteinPhaseCorrection b*eisensteinPhase z) := by
    apply (eisenstein_isUnit_iff _).mpr
    have h : ∀ b z : ZMod 3,b≠0 → (-eisensteinPhaseCorrection b*eisensteinPhase z).norm=1 := by
      decide +kernel
    exact h b z hb
  obtain ⟨a,ha⟩ := hu
  apply eisensteinNine_phase_orbit_card x (ternaryConstantHexadCodeword s hs)
    (eisensteinConstantNineForm s k b z t) hx
    (eisensteinConstantNineForm_wordResidue s k b z t) k
    (by simpa only [ternaryConstantHexadCodeword_support] using hk) a
  · rw [ha]
    simp [eisensteinConstantNineForm,hk]
    ring
  · intro i hi hik
    rw [ternaryConstantHexadCodeword_support] at hi
    simp [eisensteinConstantNineForm,hi,hik]

end Atlas.Conway
