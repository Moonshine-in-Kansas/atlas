import Atlas.Conway.EisensteinBalancedNineLocalFiber

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def eisensteinBalancedNineParameterAct (g : eisensteinCoordinateFrameStabilizer)
    (p : EisensteinBalancedNineParameters) : EisensteinBalancedNineParameters :=
  Classical.choose (eisensteinBalancedNineParameter_action g p)

theorem eisensteinBalancedNineParameterAct_spec (g : eisensteinCoordinateFrameStabilizer)
    (p : EisensteinBalancedNineParameters) :
    eisensteinIntegralAction g.val (eisensteinBalancedNineParameterLatticeVector p)=
      eisensteinBalancedNineParameterLatticeVector (eisensteinBalancedNineParameterAct g p) :=
  Classical.choose_spec (eisensteinBalancedNineParameter_action g p)

theorem eisensteinBalancedNineParameterAct_injective (g : eisensteinCoordinateFrameStabilizer) :
    Function.Injective (eisensteinBalancedNineParameterAct g) := by
  intro p q h
  have he := congrArg eisensteinBalancedNineParameterLatticeVector h
  rw [← eisensteinBalancedNineParameterAct_spec,← eisensteinBalancedNineParameterAct_spec] at he
  have hv := (eisensteinIntegralAction g.val).injective he
  exact eisensteinBalancedNineParameterVector_injective (congrArg Subtype.val hv)

def eisensteinBalancedNineParameterEquiv (g : eisensteinCoordinateFrameStabilizer) :
    EisensteinBalancedNineParameters ≃ EisensteinBalancedNineParameters :=
  Equiv.ofBijective (eisensteinBalancedNineParameterAct g)
    ⟨eisensteinBalancedNineParameterAct_injective g,
      Finite.surjective_of_injective (eisensteinBalancedNineParameterAct_injective g)⟩

theorem eisensteinBalancedNineParameterEquiv_frame (g : eisensteinCoordinateFrameStabilizer)
    (p : EisensteinBalancedNineParameters) :
    eisensteinBalancedNineParameterFrame (eisensteinBalancedNineParameterEquiv g p)=
      g.val • eisensteinBalancedNineParameterFrame p := by
  rw [eisensteinBalancedNineParameterFrame,eisensteinBalancedNineParameterFrame,
    eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  exact (eisensteinBalancedNineParameterAct_spec g p).symm

def eisensteinBalancedNineFrameFiberEquiv (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame) : EisensteinBalancedNineFrameFiber F ≃
      EisensteinBalancedNineFrameFiber (g.val • F) :=
  (eisensteinBalancedNineParameterEquiv g).subtypeEquiv (fun p => by
    rw [eisensteinBalancedNineParameterEquiv_frame]
    exact (MulAction.injective g.val).eq_iff.symm)

theorem eisensteinBalancedNineFrameFiber_card (F : EisensteinFrame)
    (hF : F ∈ eisensteinBalancedNineFamily) : Nat.card (EisensteinBalancedNineFrameFiber F)=36 := by
  obtain ⟨g,hg⟩ := eisensteinBalancedNineFamily_transitive eisensteinNineBridgeFrame F
    eisensteinNineBridgeFrame_mem_family hF
  have he := Nat.card_congr (eisensteinBalancedNineFrameFiberEquiv g eisensteinNineBridgeFrame)
  rw [hg] at he
  exact he.symm.trans eisensteinNineBridgeFrameFiber_card

/-- The53460 family consists of actual opposite norm-six classes in the lattice. -/
theorem eisensteinBalancedNineFamily_card : eisensteinBalancedNineFamily.card=53460 := by
  have h := Finset.card_eq_sum_card_image (f := eisensteinBalancedNineParameterFrame) Finset.univ
  have hf (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedNineFamily) :
      (Finset.univ.filter (fun p => eisensteinBalancedNineParameterFrame p=F)).card=36 := by
    rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card]
    exact eisensteinBalancedNineFrameFiber_card F hF
  change Fintype.card EisensteinBalancedNineParameters =
    ∑ F ∈ eisensteinBalancedNineFamily,
      (Finset.univ.filter (fun p => eisensteinBalancedNineParameterFrame p=F)).card at h
  rw [← Nat.card_eq_fintype_card,eisensteinBalancedNineParameters_card] at h
  have hh : (∑ F ∈ eisensteinBalancedNineFamily,
      (Finset.univ.filter (fun p => eisensteinBalancedNineParameterFrame p=F)).card)=
        eisensteinBalancedNineFamily.card*36 := by
    simp_rw [Finset.sum_congr rfl hf]
    simp
  rw [hh] at h
  omega

theorem eisensteinBalancedNineFamily_Fourier_edge :
    ∃ F ∈ eisensteinBalancedFamily,eisensteinFourierIsometry • F ∈ eisensteinBalancedNineFamily := by
  obtain ⟨F,hF,he⟩ := eisensteinNineBridge_edge
  refine ⟨F,hF,?_⟩
  rw [he]
  exact eisensteinNineBridgeFrame_mem_family

end Atlas.Conway
