import Atlas.Conway.EisensteinPairUnitFrames
import Atlas.Codes.TernarySmallSyndromes

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem eisensteinPairSupport_mem (p : EisensteinOrderedPair) : eisensteinPairSupport p ∈ ternaryPairs := by
  apply Finset.mem_powersetCard.mpr
  exact ⟨Finset.subset_univ _,Finset.card_pair p.property⟩

theorem eisensteinPairRepresentative_exists (S : TernaryPair) :
    ∃ p : EisensteinOrderedPair, eisensteinPairSupport p=S.val := by
  have hcard := (Finset.mem_powersetCard.mp S.property).2
  obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp hcard
  exact ⟨⟨(i,j),hij⟩,he.symm⟩

def eisensteinPairRepresentative (S : TernaryPair) : EisensteinOrderedPair :=
  (eisensteinPairRepresentative_exists S).choose

theorem eisensteinPairRepresentative_support (S : TernaryPair) :
    eisensteinPairSupport (eisensteinPairRepresentative S)=S.val :=
  (eisensteinPairRepresentative_exists S).choose_spec

/-- One of the two chirality families, defined on actual intrinsic frames. -/
def eisensteinPairUnitFrames (b : Bool) : Set EisensteinFrame :=
  Set.range (fun p : EisensteinOrderedPair × ternaryGolay => eisensteinPairUnitFrame b p.1 p.2)

def eisensteinPairUnitFrameParameter (b : Bool) (p : TernaryPair × TernaryPhaseModule) : eisensteinPairUnitFrames b :=
  ⟨eisensteinPairUnitFrame b (eisensteinPairRepresentative p.1) (eisensteinHeavyPhaseRepresentative p.2),
    ⟨(eisensteinPairRepresentative p.1,eisensteinHeavyPhaseRepresentative p.2),rfl⟩⟩

theorem eisensteinPairUnitFrameParameter_injective (b : Bool) :
    Function.Injective (eisensteinPairUnitFrameParameter b) := by
  intro p q h
  have hh := (eisensteinPairUnitFrame_eq_iff _ _ _ _ _ _).mp (congrArg Subtype.val h)
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    simpa only [eisensteinPairRepresentative_support] using hh.2.1
  · have he := (Submodule.Quotient.eq ternaryConstants).mpr hh.2.2
    change ternaryConstants.mkQ (eisensteinHeavyPhaseRepresentative p.2) =
      ternaryConstants.mkQ (eisensteinHeavyPhaseRepresentative q.2) at he
    simpa only [eisensteinHeavyPhaseRepresentative_mk] using he

theorem eisensteinPairUnitFrameParameter_surjective (b : Bool) :
    Function.Surjective (eisensteinPairUnitFrameParameter b) := by
  rintro ⟨F,⟨⟨p,t⟩,rfl⟩⟩
  let S : TernaryPair := ⟨eisensteinPairSupport p,eisensteinPairSupport_mem p⟩
  refine ⟨(S,ternaryConstants.mkQ t),?_⟩
  apply Subtype.ext
  apply (eisensteinPairUnitFrame_eq_iff _ _ _ _ _ _).mpr
  refine ⟨rfl,eisensteinPairRepresentative_support S,?_⟩
  exact (Submodule.Quotient.eq ternaryConstants).mp
    (eisensteinHeavyPhaseRepresentative_mk (ternaryConstants.mkQ t))

def eisensteinPairUnitFramesEquiv (b : Bool) :
    (TernaryPair × TernaryPhaseModule) ≃ eisensteinPairUnitFrames b :=
  Equiv.ofBijective (eisensteinPairUnitFrameParameter b)
    ⟨eisensteinPairUnitFrameParameter_injective b,eisensteinPairUnitFrameParameter_surjective b⟩

theorem eisensteinPairUnitFrames_card (b : Bool) : Nat.card (eisensteinPairUnitFrames b)=16038 := by
  rw [← Nat.card_congr (eisensteinPairUnitFramesEquiv b),Nat.card_prod,ternaryPhaseModule_card]
  have hp : Nat.card TernaryPair=66 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,ternaryPairs_card]
  rw [hp]

theorem eisensteinPairUnitFrames_disjoint :
    Disjoint (eisensteinPairUnitFrames false) (eisensteinPairUnitFrames true) := by
  apply Set.disjoint_left.mpr
  rintro F ⟨⟨p,t⟩,hF⟩ ⟨⟨q,s⟩,hG⟩
  have hh := (eisensteinPairUnitFrame_eq_iff _ _ _ _ _ _).mp (hF.trans hG.symm)
  exact Bool.false_ne_true hh.1

end Atlas.Conway
