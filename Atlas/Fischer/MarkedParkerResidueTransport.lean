import Atlas.Fischer.MarkedParkerRootOrbits
import Atlas.Fischer.ParkerRayRepresentation
import Atlas.Fischer.ResidueModels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual marked Parker group maps into the actual basic centralizer. -/
def markedParkerResidueHom (T : Finset Omega) :
    parkerMarkedSubset T →* residueCentralizer T where
  toFun e := ⟨parkerRayHom e.val,by
    apply (mem_markedPentadPointwise_iff T _).mpr
    intro i hi
    rw [parkerRayHom_conjugate_basic]
    rw [(mem_parkerMarkedSubset_iff T e.val).mp e.prop i hi]⟩
  map_one' := by apply Subtype.ext;exact map_one _
  map_mul' e f := by apply Subtype.ext;exact map_mul _ _ _

theorem parkerRoot_conjugation_of_vector (e : ParkerStandardGroup)
    (s t : ReflectingRootParameter)
    (h : parkerCoordinateAction e (reflectingRootParameterVector s)=reflectingRootParameterVector t) :
    (MulAut.conj (parkerRayHom e)) (distinguishedRootElement s)=distinguishedRootElement t := by
  apply distinguishedRootElement_conjugation
  apply Subtype.ext
  change (semilinearDisplayedRayAction (parkerAlgebraRepresentation e) (displayedRayOfParameter s)).val=_
  rw [semilinearDisplayedRayAction_parameter_value]
  change rootRay (parkerCoordinateAction e (reflectingRootParameterVector s))=_
  rw [h]
  rfl

/-- The local duadic phase orbit lies in the actual centralizer of S and x,
acting on the original distinguished elements before any quotient identification. -/
theorem residue_marked_duadic_transitive (S : Finset Omega) (hS : S.card≤2)
    (x : Omega) (p q : RootDuad) (hSp : S ⊆ p.val) (hSq : S ⊆ q.val)
    (hxp : x∉p.val) (hxq : x∉q.val)
    (ξ : Module.Dual Bit (duadShortenedCode p.val))
    (η : Module.Dual Bit (duadShortenedCode q.val)) :
    ∃ g : residueCentralizer (insert x S),
      (MulAut.conj g.val) (distinguishedRootElement (.inr (.inr ⟨p,ξ⟩)))=
        distinguishedRootElement (.inr (.inr ⟨q,η⟩)) := by
  obtain ⟨e,he⟩ := markedParker_duadicRoot_transitive S hS x p q hSp hSq hxp hxq ξ η
  exact ⟨markedParkerResidueHom _ e,parkerRoot_conjugation_of_vector e.val _ _ he⟩

end Atlas.Fischer
