import Atlas.Conway.EisensteinTriadUnitFrames
import Atlas.Codes.TernarySyndromePartition

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev EisensteinTriadSyndrome := ↥ternaryOrientedSyndromes

theorem eisensteinTriadRepresentative_exists (S : EisensteinTriadSyndrome) :
    ∃ e : Fin 3 ↪ Fin 12, ternaryOrientedSyndrome (eisensteinEmbeddingOriented e)=S.val := by
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp S.property
  obtain ⟨e,he,hi⟩ := ternaryOriented_embedding p
  refine ⟨e,?_⟩
  have hep : eisensteinEmbeddingOriented e=p := Subtype.ext (Prod.ext he hi)
  rw [hep,hp]

def eisensteinTriadRepresentative (S : EisensteinTriadSyndrome) : Fin 3 ↪ Fin 12 :=
  (eisensteinTriadRepresentative_exists S).choose

theorem eisensteinTriadRepresentative_syndrome (S : EisensteinTriadSyndrome) :
    ternaryOrientedSyndrome (eisensteinEmbeddingOriented (eisensteinTriadRepresentative S))=S.val :=
  (eisensteinTriadRepresentative_exists S).choose_spec

def eisensteinTriadUnitFrames (r : Fin 3) : Set EisensteinFrame :=
  Set.range (fun p : (Fin 3 ↪ Fin 12) × ternaryGolay => eisensteinTriadUnitFrame r p.1 p.2)

def eisensteinTriadUnitFrameParameter (r : Fin 3) (p : EisensteinTriadSyndrome × TernaryPhaseModule) :
    eisensteinTriadUnitFrames r :=
  ⟨eisensteinTriadUnitFrame r (eisensteinTriadRepresentative p.1) (eisensteinHeavyPhaseRepresentative p.2),
    ⟨(eisensteinTriadRepresentative p.1,eisensteinHeavyPhaseRepresentative p.2),rfl⟩⟩

theorem eisensteinTriadUnitFrameParameter_injective (r : Fin 3) :
    Function.Injective (eisensteinTriadUnitFrameParameter r) := by
  intro p q h
  have hh := (eisensteinTriadUnitFrame_eq_iff _ _ _ _ _ _).mp (congrArg Subtype.val h)
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    have he : ternaryOrientedSyndrome (eisensteinEmbeddingOriented (eisensteinTriadRepresentative p.1))=
        ternaryOrientedSyndrome (eisensteinEmbeddingOriented (eisensteinTriadRepresentative q.1)) :=
      Subtype.ext hh.2.1
    simpa only [eisensteinTriadRepresentative_syndrome] using he
  · have he := (Submodule.Quotient.eq ternaryConstants).mpr hh.2.2
    change ternaryConstants.mkQ (eisensteinHeavyPhaseRepresentative p.2) =
      ternaryConstants.mkQ (eisensteinHeavyPhaseRepresentative q.2) at he
    simpa only [eisensteinHeavyPhaseRepresentative_mk] using he

theorem eisensteinTriadUnitFrameParameter_surjective (r : Fin 3) :
    Function.Surjective (eisensteinTriadUnitFrameParameter r) := by
  rintro ⟨F,⟨⟨e,t⟩,rfl⟩⟩
  let S : EisensteinTriadSyndrome := ⟨ternaryOrientedSyndrome (eisensteinEmbeddingOriented e),
    Finset.mem_image.mpr ⟨eisensteinEmbeddingOriented e,Finset.mem_univ _,rfl⟩⟩
  refine ⟨(S,ternaryConstants.mkQ t),?_⟩
  apply Subtype.ext
  apply (eisensteinTriadUnitFrame_eq_iff _ _ _ _ _ _).mpr
  refine ⟨rfl,congrArg Subtype.val (eisensteinTriadRepresentative_syndrome S),?_⟩
  exact (Submodule.Quotient.eq ternaryConstants).mp
    (eisensteinHeavyPhaseRepresentative_mk (ternaryConstants.mkQ t))

def eisensteinTriadUnitFramesEquiv (r : Fin 3) :
    (EisensteinTriadSyndrome × TernaryPhaseModule) ≃ eisensteinTriadUnitFrames r :=
  Equiv.ofBijective (eisensteinTriadUnitFrameParameter r)
    ⟨eisensteinTriadUnitFrameParameter_injective r,eisensteinTriadUnitFrameParameter_surjective r⟩

theorem eisensteinTriadUnitFrames_card (r : Fin 3) : Nat.card (eisensteinTriadUnitFrames r)=40095 := by
  rw [← Nat.card_congr (eisensteinTriadUnitFramesEquiv r),Nat.card_prod,ternaryPhaseModule_card]
  have hp : Nat.card EisensteinTriadSyndrome=165 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,ternaryOrientedSyndromes_card]
  rw [hp]

theorem eisensteinTriadUnitFrames_disjoint (r s : Fin 3) (hrs : r≠s) :
    Disjoint (eisensteinTriadUnitFrames r) (eisensteinTriadUnitFrames s) := by
  apply Set.disjoint_left.mpr
  rintro F ⟨⟨e,t⟩,hF⟩ ⟨⟨f,u⟩,hG⟩
  exact hrs ((eisensteinTriadUnitFrame_eq_iff _ _ _ _ _ _).mp (hF.trans hG.symm)).1

end Atlas.Conway
