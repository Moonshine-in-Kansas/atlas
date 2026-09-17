import Atlas.Conway.EisensteinNormalizedFrameRange
import Atlas.Conway.EisensteinNineHexadFamily

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
local instance normalizedClassDecidableEq : DecidableEq EisensteinClasses :=
  fun _ _ => Classical.propDecidable _
local instance normalizedClassFinsetDecidableEq : DecidableEq (Finset EisensteinClasses) :=
  Finset.decidableEq
local instance normalizedFrameDecidableEq : DecidableEq EisensteinFrame :=
  Subtype.instDecidableEq
attribute [local irreducible] eisensteinHexadFamily eisensteinNineHexadFamily
  eisensteinBalancedNineFamily eisensteinBalancedFamily

theorem eisensteinWordResidue_diagonal (t : TernaryWord) (u : EisensteinCoordinates) :
    eisensteinWordResidue (eisensteinDiagonal t u)=eisensteinWordResidue u := by
  funext i
  change eisensteinResidue (eisensteinPhase (t i)*u i)=eisensteinResidue (u i)
  rw [map_mul,eisensteinPhase_residue,one_mul]

theorem eisensteinDiagonal_theta (t : TernaryWord) (u : EisensteinCoordinates) :
    eisensteinDiagonal t (eisensteinTheta • u)=eisensteinTheta • eisensteinDiagonal t u := by
  funext i
  change eisensteinPhase (t i)*(eisensteinTheta*u i)=eisensteinTheta*(eisensteinPhase (t i)*u i)
  ring

theorem eisensteinBalancedParameter_full (p : EisensteinBalancedParameters) :
    EisensteinNormalizedFull (eisensteinBalancedPhasedLatticeVector p.1 p.2.1 p.2.2) := by
  refine ⟨eisensteinDiagonal (eisensteinBalancedPhaseWord p.1 p.2.2)
    (eisensteinBalancedHexadLift p.1 p.2.1.val),eisensteinDiagonal_theta _ _,?_⟩
  rw [eisensteinWordResidue_diagonal,eisensteinBalancedHexadLift_residue]
  exact ternaryBalanced_surjective p.1

theorem eisensteinBalancedNineParameter_full (p : EisensteinBalancedNineParameters) :
    EisensteinNormalizedFull (eisensteinBalancedNineParameterLatticeVector p) := by
  refine ⟨eisensteinBalancedNineParameterLift p,rfl,?_⟩
  rw [eisensteinBalancedNineParameterLift_residue]
  exact ternaryBalanced_surjective p.1

/-- Every frame in either balanced family has a normalized representative taking
all three ternary values. -/
theorem eisensteinBalancedFamilies_full (F : EisensteinFrame)
    (h : F ∈ eisensteinBalancedFamily ∨ F ∈ eisensteinBalancedNineFamily) :
    ∃ x : EisensteinShell 6,eisensteinFrameOfVector x=F ∧ EisensteinNormalizedFull x.val := by
  rcases h with h|h
  · obtain ⟨p,rfl⟩ := (eisensteinBalancedFamily_mem_iff F).mp h
    exact ⟨eisensteinBalancedPhasedShellVector p.1 p.2.1 p.2.2,rfl,eisensteinBalancedParameter_full p⟩
  · unfold eisensteinBalancedNineFamily at h
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
    exact ⟨eisensteinBalancedNineParameterShell p,rfl,eisensteinBalancedNineParameter_full p⟩

theorem ternaryTriadWord_not_surjective (s : Finset (Fin 12)) :
    ¬Function.Surjective (ternaryTriadWord s) := by
  intro h
  obtain ⟨i,hi⟩ := h 2
  by_cases hs : i ∈ s <;> simp [ternaryTriadWord,hs,show (1 : ZMod 3)≠2 by decide,show (0 : ZMod 3)≠2 by decide] at hi

def EisensteinNormalizedConstant (x : EisensteinLattice) : Prop :=
  ∃ u : EisensteinCoordinates,∃ s : Finset (Fin 12),
    x.val=eisensteinTheta • u ∧ eisensteinWordResidue u=ternaryTriadWord s

theorem eisensteinNormalizedConstant_phase (x : EisensteinLattice)
    (hx : EisensteinNormalizedConstant x) (t : Multiplicative ternaryGolay) :
    EisensteinNormalizedConstant (eisensteinIntegralAction (eisensteinPhaseIsometries t) x) := by
  obtain ⟨u,s,hu,hs⟩ := hx
  refine ⟨eisensteinDiagonal t.toAdd.val u,s,?_,?_⟩
  · change (eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t.toAdd)) x).val=_
    rw [eisensteinIntegralAction_phase,hu,eisensteinDiagonal_theta]
  · rw [eisensteinWordResidue_diagonal,hs]

theorem eisensteinHexad_normalized_constant (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) :
    EisensteinNormalizedConstant (eisensteinHexadLatticeVector s hs i) := by
  refine ⟨eisensteinHexadLift s i,s,rfl,?_⟩
  funext k
  by_cases hk : k=i <;> by_cases hks : k ∈ s <;>
    simp [eisensteinWordResidue,eisensteinHexadLift,ternaryTriadWord,hk,hks,
      show eisensteinResidue 3=0 by decide +kernel]

theorem eisensteinNineHexad_normalized_constant (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (b : ZMod 3) :
    EisensteinNormalizedConstant (eisensteinNineHexadLatticeVector s hs k j b) := by
  refine ⟨eisensteinNineHexadLift s k j b,s,rfl,?_⟩
  funext i
  by_cases hi : i ∈ s <;> simp [eisensteinWordResidue,eisensteinNineHexadLift,
    ternaryTriadWord,hi,map_add,map_mul,show eisensteinResidue eisensteinTheta=0 by decide +kernel]

theorem eisensteinConstantBalanced_frame_ne (x y : EisensteinShell 6)
    (hx : EisensteinNormalizedFull x.val) (hy : EisensteinNormalizedConstant y.val) :
    eisensteinFrameOfVector x≠eisensteinFrameOfVector y := by
  intro h
  obtain ⟨u,s,hu,hs⟩ := hy
  have hh := eisensteinNormalizedFull_frame x y h hx u hu
  rw [hs] at hh
  exact ternaryTriadWord_not_surjective s hh

theorem eisensteinConstantFamilies_constant (F : EisensteinFrame)
    (h : F ∈ eisensteinHexadFamily ∨
      ∃ b : ZMod 3,∃ hb : b≠0,F ∈ eisensteinNineHexadFamily b hb) :
    ∃ x : EisensteinShell 6,eisensteinFrameOfVector x=F ∧ EisensteinNormalizedConstant x.val := by
  rcases h with h|⟨b,hb,h⟩
  · unfold eisensteinHexadFamily at h
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp h
    obtain ⟨t,rfl⟩ := (eisensteinHexadPairOrbit_mem p F).mp hp
    refine ⟨eisensteinShellAction (eisensteinPhaseIsometries t) 6
      (eisensteinHexadShellVector _ (eisensteinHexadPairSupport_mem p)
        _ (eisensteinHexadPairPoint_mem p)),?_,?_⟩
    · rw [eisensteinHexadPairFrame,eisensteinHexadFrame,eisensteinFrameAction_vector]
    · change EisensteinNormalizedConstant (eisensteinIntegralAction (eisensteinPhaseIsometries t)
        (eisensteinHexadLatticeVector (eisensteinHexadPairSupport p)
          (eisensteinHexadPairSupport_mem p) (eisensteinHexadPairPoint p)))
      exact eisensteinNormalizedConstant_phase _
        (eisensteinHexad_normalized_constant (eisensteinHexadPairSupport p)
          (eisensteinHexadPairSupport_mem p) (eisensteinHexadPairPoint p)) t
  · unfold eisensteinNineHexadFamily at h
    rw [Finset.mem_biUnion] at h
    obtain ⟨p,_,hp⟩ := h
    obtain ⟨t,rfl⟩ := (eisensteinNineHexadPairOrbit_mem b hb p F).mp hp
    refine ⟨eisensteinShellAction (eisensteinPhaseIsometries t) 6
      (eisensteinNineHexadShellVector _ (eisensteinHexadPairSupport_mem p)
        _ _ (eisensteinHexadPairPoint_mem p) (eisensteinNineHexadPairOutside_mem p) b hb),?_,?_⟩
    · rw [eisensteinNineHexadPairFrame,eisensteinNineHexadFrame,eisensteinFrameAction_vector]
    · change EisensteinNormalizedConstant (eisensteinIntegralAction (eisensteinPhaseIsometries t)
        (eisensteinNineHexadLatticeVector (eisensteinHexadPairSupport p)
          (eisensteinHexadPairSupport_mem p) (eisensteinHexadPairPoint p)
          (eisensteinNineHexadPairOutside p) b))
      exact eisensteinNormalizedConstant_phase _
        (eisensteinNineHexad_normalized_constant (eisensteinHexadPairSupport p)
          (eisensteinHexadPairSupport_mem p) (eisensteinHexadPairPoint p)
          (eisensteinNineHexadPairOutside p) b) t

theorem eisensteinConstantBalanced_disjoint (F : EisensteinFrame)
    (hc : F ∈ eisensteinHexadFamily ∨
      ∃ b : ZMod 3,∃ hb : b≠0,F ∈ eisensteinNineHexadFamily b hb)
    (hb : F ∈ eisensteinBalancedFamily ∨ F ∈ eisensteinBalancedNineFamily) : False := by
  obtain ⟨x,hx,hxf⟩ := eisensteinBalancedFamilies_full F hb
  obtain ⟨y,hy,hyc⟩ := eisensteinConstantFamilies_constant F hc
  exact eisensteinConstantBalanced_frame_ne x y hxf hyc (hx.trans hy.symm)

theorem eisensteinNineHexad_balancedNine_disjoint (b : ZMod 3) (hb : b≠0) :
    Disjoint (eisensteinNineHexadFamily b hb) eisensteinBalancedNineFamily := by
  apply Finset.disjoint_left.mpr
  intro F hc hd
  exact eisensteinConstantBalanced_disjoint F (Or.inr ⟨b,hb,hc⟩) (Or.inr hd)

theorem eisensteinHexad_balancedNine_disjoint :
    Disjoint eisensteinHexadFamily eisensteinBalancedNineFamily := by
  apply Finset.disjoint_left.mpr
  intro F hc hd
  exact eisensteinConstantBalanced_disjoint F (Or.inl hc) (Or.inr hd)

theorem eisensteinNineHexad_balanced_disjoint (b : ZMod 3) (hb : b≠0) :
    Disjoint (eisensteinNineHexadFamily b hb) eisensteinBalancedFamily := by
  apply Finset.disjoint_left.mpr
  intro F hc hd
  exact eisensteinConstantBalanced_disjoint F (Or.inr ⟨b,hb,hc⟩) (Or.inl hd)

end Atlas.Conway
